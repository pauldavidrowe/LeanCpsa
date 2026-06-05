/-
LeanCPSA.Displayer

Port of CPSA.Displayer (MITRE cpsa).

Copyright (c) 2026 Paul D. Rowe

Displays protocols and preskeletons as S-expressions.

Copyright (c) 2009 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.
-/

import LeanCPSA.Algebra
import LeanCPSA.Channel
import LeanCPSA.Protocol
import LeanCPSA.Operation
import LeanCPSA.Strand

namespace LeanCPSA.Displayer

open LeanCPSA.Algebra
open LeanCPSA.Channel
open LeanCPSA.Protocol
open LeanCPSA.Operation (Operation Direction Cause Method getStrandMap Node Pair Sid)
open LeanCPSA.Strand
open LeanCPSA.Lib (SExpr assertError)

-- ── Sort helpers ──────────────────────────────────────────────────────────────

-- `List.mergeSort` needs a `Bool` comparison, not `Ordering`.
-- This helper converts any `Ord α` instance.
private def sortWith {α : Type} [Ord α] (xs : List α) : List α :=
  xs.mergeSort fun a b => compare a b != .gt

-- Lean 4.15 has no built-in `Ord (α × β)`.  We define a private generic
-- instance here for sorting pairs of terms / option-lengths.
private instance instOrdProd {α β : Type} [Ord α] [Ord β] : Ord (α × β) where
  compare p q :=
    match (Ord.compare p.1 q.1 : Ordering) with
    | .eq => Ord.compare p.2 q.2
    | o   => o

-- `Option Int` has no built-in `Ord` in Lean 4; we need one for
-- sorting `sansNestedPts` results.
private instance : Ord (Option Int) where
  compare
    | none,   none   => .eq
    | none,   some _ => .lt
    | some _, none   => .gt
    | some x, some y => Ord.compare x y

-- ── varsContext ───────────────────────────────────────────────────────────────

/-- Build a `Context` from a list of variables.
    Mirrors `varsContext :: [Term] -> Context`. -/
def varsContext (vars : List Term) : Context :=
  addToContext emptyContext vars

-- ── displayOptional ───────────────────────────────────────────────────────────

/-- Prepend an optional S-expression field only when `value` is non-empty.
    Mirrors `displayOptional :: String -> [SExpr ()] -> [SExpr ()] -> [SExpr ()]`. -/
def displayOptional (key : String) (value : List (SExpr Unit))
    (rest : List (SExpr Unit)) : List (SExpr Unit) :=
  match value with
  | []  => rest
  | _   => .lst () (.sym () key :: value) :: rest

-- ── displayNode / displayNodes ────────────────────────────────────────────────

/-- Display a `Node` as `(strand index)`.
    Mirrors `displayNode :: Node -> SExpr ()`. -/
def displayNode (n : Node) : SExpr Unit :=
  .lst () [.num () n.1, .num () n.2]

/-- Display a sorted list of nodes.
    Mirrors `displayNodes :: [Node] -> [SExpr ()]`. -/
def displayNodes (ns : List Node) : List (SExpr Unit) :=
  (sortWith ns).map displayNode

-- ── displayPair / displayOrdering ────────────────────────────────────────────

/-- Display an ordering pair.
    Mirrors `displayPair :: Pair -> SExpr ()`. -/
def displayPair (p : Pair) : SExpr Unit :=
  .lst () [displayNode p.1, displayNode p.2]

/-- Display a sorted list of ordering pairs.
    Mirrors `displayOrdering :: [Pair] -> [SExpr ()]`. -/
def displayOrdering (orderings : List Pair) : List (SExpr Unit) :=
  (sortWith orderings).map displayPair

-- ── displayTerms / displayLenTerms / displayTermPairs ─────────────────────────

/-- Display a sorted list of terms.
    Mirrors `displayTerms :: Context -> [Term] -> [SExpr ()]`. -/
def displayTerms (ctx : Context) (ts : List Term) : List (SExpr Unit) :=
  (sortWith ts).map (displayTerm ctx)

/-- Display a single optional-length/term pair.
    Mirrors `displayLenTerm :: Context -> (Maybe Int, Term) -> SExpr ()`. -/
def displayLenTerm (ctx : Context) (lt : Option Int × Term) : SExpr Unit :=
  match lt with
  | (none,     t) => displayTerm ctx t
  | (some len, t) => .lst () [.num () len, displayTerm ctx t]

/-- Display a sorted list of optional-length/term pairs.
    Mirrors `displayLenTerms :: Context -> [(Maybe Int, Term)] -> [SExpr ()]`. -/
def displayLenTerms (ctx : Context) (ts : List (Option Int × Term))
    : List (SExpr Unit) :=
  (sortWith ts).map (displayLenTerm ctx)

/-- Display a single term pair.
    Mirrors `displayTermPair :: Context -> (Term, Term) -> SExpr ()`. -/
def displayTermPair (ctx : Context) (xy : Term × Term) : SExpr Unit :=
  .lst () [displayTerm ctx xy.1, displayTerm ctx xy.2]

/-- Display a sorted list of term pairs.
    Mirrors `displayTermPairs :: Context -> [(Term, Term)] -> [SExpr ()]`. -/
def displayTermPairs (ctx : Context) (ts : List (Term × Term))
    : List (SExpr Unit) :=
  (sortWith ts).map (displayTermPair ctx)

-- ── sansPts helpers ───────────────────────────────────────────────────────────

/-- Filter out `pt`-sort terms.
    Mirrors `sansPts :: [Term] -> [Term]`. -/
def sansPts (ts : List Term) : List Term := ts.filter notPt

/-- Filter out entries where the term is a `pt`.
    Mirrors `sansNestedPts :: [(Maybe Int, Term)] -> [(Maybe Int, Term)]`. -/
def sansNestedPts (ts : List (Option Int × Term)) : List (Option Int × Term) :=
  ts.filter (fun (_, t) => notPt t)

/-- Filter out maplets whose domain variable is a `pt`.
    Mirrors `sansPtMaplets :: [(Term, Term)] -> [(Term, Term)]`. -/
def sansPtMaplets (ts : List (Term × Term)) : List (Term × Term) :=
  ts.filter (fun (v, _) => notPt v)

-- ── displayParam ─────────────────────────────────────────────────────────────

/-- Display a role parameter as a quoted name.
    Mirrors `displayParam :: Role -> Term -> SExpr ()`. -/
def displayParam (r : Role) (t : Term) : SExpr Unit :=
  match displayTerm (varsContext r.rvars) t with
  | .sym _ v => .str () v
  | _        => assertError "Displayer.displayParam: bad parameter"

-- ── displayForm ───────────────────────────────────────────────────────────────

/-- Display an atomic formula.
    Mirrors `displayForm :: Context -> AForm -> SExpr ()`. -/
def displayForm (ctx : Context) : AForm → SExpr Unit
  | .Length r s l =>
      .lst () [.sym () "p", .str () r.rname, displayTerm ctx s, displayTerm ctx l]
  | .Param r p _ s t =>
      .lst () [.sym () "p", .str () r.rname, displayParam r p,
               displayTerm ctx s, displayTerm ctx t]
  | .Prec (x, i) (y, j) =>
      .lst () [.sym () "prec",
               displayTerm ctx x, displayTerm ctx i,
               displayTerm ctx y, displayTerm ctx j]
  | .Non t =>
      .lst () [.sym () "non", displayTerm ctx t]
  | .Pnon t =>
      .lst () [.sym () "pnon", displayTerm ctx t]
  | .Uniq t =>
      .lst () [.sym () "uniq", displayTerm ctx t]
  | .UniqAt t (s, i) =>
      .lst () [.sym () "uniq-at", displayTerm ctx t,
               displayTerm ctx s, displayTerm ctx i]
  | .Ugen t =>
      .lst () [.sym () "ugen", displayTerm ctx t]
  | .UgenAt t (s, i) =>
      .lst () [.sym () "ugen-at", displayTerm ctx t,
               displayTerm ctx s, displayTerm ctx i]
  | .GenStV t =>
      .lst () [.sym () "gen-st", displayTerm ctx t]
  | .Conf t =>
      .lst () [.sym () "conf", displayTerm ctx t]
  | .Auth t =>
      .lst () [.sym () "auth", displayTerm ctx t]
  | .AFact name fs =>
      .lst () (.sym () "fact" :: .sym () name :: fs.map (displayTerm ctx))
  | .Equals t1 t2 =>
      .lst () [.sym () "=", displayTerm ctx t1, displayTerm ctx t2]
  | .Component t1 t2 =>
      .lst () [.sym () "component", displayTerm ctx t1, displayTerm ctx t2]
  | .Commpair (i, j) (i', j') =>
      .lst () [.sym () "comm-pr",
               displayTerm ctx i, displayTerm ctx j,
               displayTerm ctx i', displayTerm ctx j']
  | .SameLocn (i, j) (i', j') =>
      .lst () [.sym () "same-locn",
               displayTerm ctx i, displayTerm ctx j,
               displayTerm ctx i', displayTerm ctx j']
  | .StateNode (i, j) =>
      .lst () [.sym () "state-node", displayTerm ctx i, displayTerm ctx j]
  | .Trans (i, j) =>
      .lst () [.sym () "trans", displayTerm ctx i, displayTerm ctx j]
  | .LeadsTo (i, j) (i', j') =>
      .lst () [.sym () "leads-to",
               displayTerm ctx i, displayTerm ctx j,
               displayTerm ctx i', displayTerm ctx j']

-- ── displayConj / displayDisj / displayExistential ────────────────────────────

/-- Display a conjunction of atomic formulas.
    Mirrors `displayConj :: Context -> [AForm] -> SExpr ()`. -/
def displayConj (ctx : Context) : List AForm → SExpr Unit
  | []     => .lst () []
  | [form] => displayForm ctx form
  | forms  => .lst () (.sym () "and" :: forms.map (displayForm ctx))

/-- Display a single existentially-quantified conjunct.
    Mirrors `displayExistential :: Context -> ([Term], [AForm]) -> SExpr ()`. -/
def displayExistential (ctx : Context) (evarsConj : List Term × List AForm)
    : SExpr Unit :=
  match evarsConj with
  | ([], conj) => displayConj ctx conj
  | (evars, conj) =>
      let ctx' := addToContext ctx evars
      .lst () [.sym () "exists",
               .lst () (displayVars ctx' evars),
               displayConj ctx' conj]

/-- Display a disjunction of existentials (or `false` for empty).
    Mirrors `displayDisj :: Context -> [([Term],[AForm])] -> SExpr ()`. -/
def displayDisj (ctx : Context) : List (List Term × List AForm) → SExpr Unit
  | []     => .lst () [.sym () "false"]
  | [conj] => displayExistential ctx conj
  | disj   => .lst () (.sym () "or" :: disj.map (displayExistential ctx))

-- ── displayGoal / displayImpl ─────────────────────────────────────────────────

/-- Display the implication body of a goal.
    Mirrors `displayImpl :: Context -> Goal -> SExpr ()`. -/
def displayImpl (ctx : Context) (g : Goal) : SExpr Unit :=
  .lst () [.sym () "implies",
           displayConj ctx g.antec,
           displayDisj ctx g.consq]

/-- Display a universally-quantified goal.
    Mirrors `displayGoal :: Goal -> SExpr ()`. -/
def displayGoal (g : Goal) : SExpr Unit :=
  let ctx := varsContext g.uvars
  .lst () [.sym () "forall",
           .lst () (displayVars ctx g.uvars),
           displayImpl ctx g]

-- ── displayRule ───────────────────────────────────────────────────────────────

/-- Display a rule with a given keyword (e.g. "defrule" or "defgenrule").
    Mirrors `displayRule :: String -> Rule -> SExpr ()`. -/
def displayRule (kw : String) (r : Rule) : SExpr Unit :=
  .lst () (.sym () kw :: .sym () r.rlname :: displayGoal r.rlgoal :: r.rlcomment)

/-- Display a user-written rule with `defrule`.
    Mirrors `displayUserRule :: Rule -> SExpr ()`. -/
def displayUserRule : Rule → SExpr Unit := displayRule "defrule"

/-- Display a generated rule with `defgenrule`.
    Mirrors `displayGenRule :: Rule -> SExpr ()`. -/
def displayGenRule : Rule → SExpr Unit := displayRule "defgenrule"

-- ── displayTrace / displayTraceNoPt ───────────────────────────────────────────

/-- Display a single trace event.
    Mirrors the inner `displayDt` in `displayTrace`. -/
private def displayEvent (ctx : Context) : Event → SExpr Unit
  | .In  (.Plain t)     => .lst () [.sym () "recv", displayTerm ctx t]
  | .In  (.ChMsg ct ch t)  =>
      if ct == .Locn then .lst () [.sym () "load", displayTerm ctx ch, displayTerm ctx t]
      else                .lst () [.sym () "recv", displayTerm ctx ch, displayTerm ctx t]
  | .Out (.Plain t)     => .lst () [.sym () "send", displayTerm ctx t]
  | .Out (.ChMsg ct ch t)  =>
      if ct == .Locn then .lst () [.sym () "stor", displayTerm ctx ch, displayTerm ctx t]
      else                .lst () [.sym () "send", displayTerm ctx ch, displayTerm ctx t]

/-- Display a trace as S-expressions.
    Mirrors `displayTrace :: Context -> Trace -> [SExpr ()]`. -/
def displayTrace (ctx : Context) (trace : Trace) : List (SExpr Unit) :=
  trace.map (displayEvent ctx)

/-- Display a trace, suppressing point-sort payload terms in state events.
    Mirrors `displayTraceNoPt :: Context -> Trace -> [SExpr ()]`. -/
def displayTraceNoPt (ctx : Context) (trace : Trace) : List (SExpr Unit) :=
  trace.map fun e =>
    match e with
    | .In  (.ChMsg ct ch t) =>
        if ct == .Locn then .lst () [.sym () "load", displayTerm ctx ch, displayTermNoPt ctx t]
        else               .lst () [.sym () "recv", displayTerm ctx ch, displayTerm ctx t]
    | .Out (.ChMsg ct ch t) =>
        if ct == .Locn then .lst () [.sym () "stor", displayTerm ctx ch, displayTermNoPt ctx t]
        else               .lst () [.sym () "send", displayTerm ctx ch, displayTerm ctx t]
    | ev                 => displayEvent ctx ev

-- ── displayRole ───────────────────────────────────────────────────────────────

/-- Display a role definition.
    Mirrors `displayRole :: Role -> SExpr ()`. -/
def displayRole (r : Role) : SExpr Unit :=
  let vars := sansPts r.rvars
  let ctx  := varsContext r.rvars
  .lst () (.sym () "defrole" ::
           .sym () r.rname ::
           .lst () (.sym () "vars" :: displayVars ctx vars) ::
           .lst () (.sym () "trace" :: displayTraceNoPt ctx r.rtrace) ::
           displayOptional "non-orig"     (displayLenTerms ctx (sansNestedPts r.rnon))
          (displayOptional "pen-non-orig" (displayLenTerms ctx (sansNestedPts r.rpnon))
          (displayOptional "uniq-orig"    (displayTerms ctx (sansPts r.runique))
          (displayOptional "uniq-gen"     (displayTerms ctx r.runiqgen)
          (displayOptional "absent"       (displayTermPairs ctx r.rabsent)
          (displayOptional "conf"         (displayTerms ctx r.rconf)
          (displayOptional "auth"         (displayTerms ctx r.rauth)
           r.rcomment)))))))

-- ── displayProt ───────────────────────────────────────────────────────────────

/-- Display a full protocol definition.
    Mirrors `displayProt :: Prot -> SExpr ()`. -/
def displayProt (p : Prot) : SExpr Unit :=
  -- roles in original order; user rules, gen rules, comments follow
  let ruleExprs := p.userrules.map displayUserRule ++
                   p.generatedrules.map displayGenRule
  .lst () (.sym () "defprotocol" ::
           .sym () p.pname ::
           .sym () p.alg ::
           p.roles.map displayRole ++ ruleExprs ++ p.pcomment)

-- ── displayFterm / displayFact / displayFacts ─────────────────────────────────

/-- Display a fact term (either a strand index or an algebra term).
    Mirrors `displayFterm :: Context -> FTerm -> SExpr ()`. -/
def displayFterm (ctx : Context) : FTerm → SExpr Unit
  | .FSid s    => .num () s
  | .ofTerm t  => displayTerm ctx t

/-- Display a single fact.
    Mirrors `displayFact :: Context -> Fact -> SExpr ()`. -/
def displayFact (ctx : Context) (fact : Fact) : SExpr Unit :=
  .lst () (.sym () fact.name :: fact.terms.map (displayFterm ctx))

/-- Display the non-`trans` facts of a preskeleton.
    Mirrors `displayFacts :: Context -> [Fact] -> [SExpr ()]`. -/
def displayFacts (ctx : Context) (facts : List Fact) : List (SExpr Unit) :=
  facts.foldr (fun fact soFar =>
    if fact.name == "trans" then soFar
    else .lst () (.sym () fact.name :: fact.terms.map (displayFterm ctx)) :: soFar) []

-- ── displayPriority ───────────────────────────────────────────────────────────

/-- Display a priority annotation.
    Mirrors `displayPriority :: (Node, Int) -> SExpr ()`. -/
def displayPriority (np : Node × Int) : SExpr Unit :=
  .lst () [displayNode np.1, .num () np.2]

-- ── displayMaplet / displayInst ───────────────────────────────────────────────

/-- Display a single environment maplet.
    Mirrors `displayMaplet :: Context -> Context -> (Term, Term) -> SExpr ()`. -/
def displayMaplet (domain range : Context) (xt : Term × Term) : SExpr Unit :=
  .lst () [displayTerm domain xt.1, displayTerm range xt.2]

/-- Display a strand instance.
    Mirrors `displayInst :: Context -> Instance -> SExpr ()`. -/
def displayInst (ctx : Context) (inst : Instance) : SExpr Unit :=
  match listenerTerm inst with
  | some t => .lst () [.sym () "deflistener", displayTerm ctx t]
  | none   =>
      let r       := inst.role
      let domain  := r.rvars
      let rctx    := varsContext domain
      let maplets := sortWith (sansPtMaplets (reify domain inst.env))
      .lst () (.sym () "defstrand" ::
               .sym () r.rname ::
               .num () inst.height ::
               maplets.map (displayMaplet rctx ctx))

-- ── displayCmt / displayOpCmt / displayOpCmts ─────────────────────────────────

/-- Display a `CMT` value using a given context.
    Mirrors `displayCmt :: Context -> CMT -> SExpr ()`. -/
def displayCmt (ctx : Context) : CMT → SExpr Unit
  | .CM (.Plain t)    => displayTerm ctx t
  | .CM (.ChMsg _ ch t) => .lst () [.sym () "ch-msg", displayTerm ctx ch, displayTerm ctx t]
  | .TM t             => displayTerm ctx t

/-- Display a `CMT` after extending the context with its constituent terms.
    Mirrors `displayOpCmt :: Context -> CMT -> SExpr ()`. -/
def displayOpCmt (ctx : Context) (cm : CMT) : SExpr Unit :=
  displayCmt (addToContext ctx (cmtTerms cm)) cm

/-- Display a list of `CMT` values, all sharing a context extended by all their terms.
    Mirrors `displayOpCmts :: Context -> [CMT] -> [SExpr ()]`. -/
def displayOpCmts (ctx : Context) (ts : List CMT) : List (SExpr Unit) :=
  let ctx' := addToContext ctx (ts.flatMap cmtTerms)
  (sortWith ts).map (displayCmt ctx')

-- ── displayOperation ──────────────────────────────────────────────────────────

/-- Display the operation field of a preskeleton.
    Mirrors `displayOperation :: Preskel -> Context -> [SExpr ()] -> [SExpr ()]`. -/
def displayOperation (k : Preskel) (ctx : Context) (rest : List (SExpr Unit))
    : List (SExpr Unit) :=
  let displayDir : Direction → SExpr Unit
    | .Encryption => .sym () "encryption-test"
    | .Nonce      => .sym () "nonce-test"
    | .Channel    => .sym () "channel-test"
  let displayCauseOp (op : SExpr Unit) (cause : Cause) : List (SExpr Unit) :=
    .lst () (.sym () "operation" ::
             displayDir cause.direction ::
             op ::
             displayOpCmt ctx cause.cmt ::
             displayNode cause.node ::
             displayOpCmts ctx (LeanCPSA.Lib.RBSet.toList cause.cmts)) :: rest
  let displayMeth : Method → List (SExpr Unit)
    | .Deleted node      => [.sym () "deleted", displayNode node]
    | .Weakened (n0, n1) => [.sym () "weakened",
                              .lst () [displayNode n0, displayNode n1]]
    | .Separated t       => [.sym () "separated", displayOpCmt ctx (.TM t)]
    | .Forgot t          => [.sym () "forgot",    displayOpCmt ctx (.TM t)]
  match k.operation with
  | .New =>
      rest
  | .Contracted _ subst cause =>
      displayCauseOp (.lst () (.sym () "contracted" :: displaySubst ctx subst)) cause
  | .Displaced _ s s' role ht cause =>
      displayCauseOp (.lst () [.sym () "displaced",
                                .num () s, .num () s', .sym () role, .num () ht]) cause
  | .AddedStrand _ role ht cause =>
      displayCauseOp (.lst () [.sym () "added-strand", .sym () role, .num () ht]) cause
  | .AddedListener _ t cause =>
      displayCauseOp (.lst () [.sym () "added-listener",
                                displayOpCmt ctx (.CM (.Plain t))]) cause
  | .AddedAbsence _ t1 t2 cause =>
      displayCauseOp (.lst () [.sym () "added-absence",
                                displayOpCmt ctx (.TM t1),
                                displayOpCmt ctx (.TM t2)]) cause
  | .Generalized _ method =>
      .lst () (.sym () "operation" :: .sym () "generalization" :: displayMeth method) :: rest
  | .Collapsed _ s s' =>
      .lst () [.sym () "operation", .sym () "collapsed", .num () s, .num () s'] :: rest
  | .AppliedRules _ =>
      .lst () [.sym () "operation", .sym () "applied-rules"] :: rest

-- ── displayStrandMap ──────────────────────────────────────────────────────────

/-- Display the strand-map annotation when non-empty.
    Mirrors `displayStrandMap :: Preskel -> [SExpr ()] -> [SExpr ()]`. -/
def displayStrandMap (k : Preskel) (rest : List (SExpr Unit)) : List (SExpr Unit) :=
  match getStrandMap k.operation with
  | []  => rest
  | sm  => .lst () (.sym () "strand-map" :: sm.map (fun s => .num () s)) :: rest

-- ── displayRest ───────────────────────────────────────────────────────────────

/-- Display the fields after the variable/instance sections of a preskeleton.
    Mirrors `displayRest :: Preskel -> Context -> [SExpr ()] -> [SExpr ()]`. -/
def displayRest (k : Preskel) (ctx : Context) (rest : List (SExpr Unit))
    : List (SExpr Unit) :=
  let priorities := k.kpriority.map displayPriority
  let traces     := k.insts.map (fun i => .lst () (displayTrace ctx i.trace))
  displayOptional "precedes"     (displayOrdering k.orderings)
 (displayOptional "non-orig"     (displayTerms ctx (sansPts k.knon))
 (displayOptional "pen-non-orig" (displayTerms ctx (sansPts k.kpnon))
 (displayOptional "uniq-orig"    (displayTerms ctx (sansPts k.kunique))
 (displayOptional "uniq-gen"     (displayTerms ctx k.kuniqgen)
 (displayOptional "absent"       (displayTermPairs ctx k.kabsent)
 (displayOptional "precur"       (displayNodes k.kprecur)
 (displayOptional "gen-st"       (displayTerms ctx k.kgenSt)
 (displayOptional "conf"         (displayTerms ctx k.kconf)
 (displayOptional "auth"         (displayTerms ctx k.kauth)
 (displayOptional "facts"        (displayFacts ctx k.kfacts)
 (displayOptional "leads-to"     (displayOrdering (nodePairsOfSkel k))
 (displayOptional "priority"     priorities
  (kcomment k ++
  (displayOptional "rule"        ((sortWith k.krules).map (fun s => .sym () s))
  (displayOperation k ctx
  (displayStrandMap k
  (displayOptional "traces" traces rest)))))))))))))))))

-- ── displayPreskel ────────────────────────────────────────────────────────────

/-- Display a full preskeleton.
    Mirrors `displayPreskel :: Preskel -> [SExpr ()] -> SExpr ()`. -/
def displayPreskel (k : Preskel) (rest : List (SExpr Unit)) : SExpr Unit :=
  let vars := k.kfvars ++ kvars k
  let ctx  := varsContext vars
  .lst () (.sym () "defskeleton" ::
           .sym () (protocol k).pname ::
           .lst () (.sym () "vars" :: displayVars ctx vars) ::
           k.insts.foldr (fun i acc => displayInst ctx i :: acc)
             (displayRest k ctx rest))

end LeanCPSA.Displayer
