/-
Cpsa2Lean.Algebra

Stage 1: core type definitions.

Port of CPSA.Algebra (MITRE cpsa v4.4.8).
This file covers the data types, their instances, and the algebraic
helper functions through `group`/`separateVar`.  Later stages will add
`termWellFormed`, variable loading, substitution, matching/unification,
and display.

The file is compiled with the equivalent of `#define CHECK_CANONICAL`,
so `equalTerm`/`compareTerm` panic on non-canonical terms rather than
applying the reduction axioms.

Naming divergence from Haskell:
  `Sort`  → `ExptSort`   (`Sort` is a Lean universe keyword)
-/

import Cpsa2Lean.Lib.Utilities
import Cpsa2Lean.Lib.SExpr
import Cpsa2Lean.Lib.RBMap
import Cpsa2Lean.Signature

namespace Cpsa2Lean.Algebra

open Cpsa2Lean.Lib (SExpr Pos assertError adjoin subset)
open Cpsa2Lean.Signature (Sig)

-- ── Algebra name constants ────────────────────────────────────────────────────

def name  : String := "basic"
def algAlias : String := "diffie-hellman"

-- ── Id ───────────────────────────────────────────────────────────────────────

/-- An identifier: an integer tag plus a display name.
    `BEq` and `Ord` compare by integer tag only, ignoring the name.
    Mirrors `newtype Id = Id (Integer, String)` in `Algebra.hs`. -/
structure Id where
  num  : Int
  name : String
  deriving Repr

instance : BEq Id where
  beq x y := x.num == y.num

instance : Ord Id where
  compare x y := compare x.num y.num

instance : Inhabited Id := ⟨⟨0, ""⟩⟩

def idName (x : Id) : String := x.name

-- ── Gen ──────────────────────────────────────────────────────────────────────

/-- A counter for generating fresh identifiers.
    Mirrors `newtype Gen = Gen (Integer)`. -/
structure Gen where
  counter : Int
  deriving Repr, BEq

/-- The initial generator. -/
def origin : Gen := ⟨0⟩

instance : Inhabited Gen := ⟨origin⟩

/-- Merge two generators, keeping the larger counter. -/
def gmerge (g h : Gen) : Gen := ⟨max g.counter h.counter⟩

/-- Allocate a fresh identifier and advance the generator. -/
def freshId (g : Gen) (s : String) : Gen × Id :=
  (⟨g.counter + 1⟩, ⟨g.counter, s⟩)

/-- Clone an identifier, giving it a new integer tag. -/
def cloneId (g : Gen) (x : Id) : Gen × Id :=
  freshId g x.name

-- ── ExptSort, Coef, Desc ─────────────────────────────────────────────────────

/-- Sort of a variable in a Diffie-Hellman exponent group.
    `Rndx` is the basis (random) element sort; `Expt` is the general
    exponent sort (a supersort of `Rndx`).
    Named `ExptSort` here because `Sort` is a reserved Lean keyword;
    mirrors `data Sort = Rndx | Expt` in `Algebra.hs`. -/
inductive ExptSort where
  | Rndx
  | Expt
  deriving Repr, BEq, DecidableEq, Ord

/-- A non-zero integer coefficient in a group element. -/
abbrev Coef := Int

/-- A descriptor: sort and coefficient of one variable in a group element. -/
abbrev Desc := ExptSort × Coef


-- ── Group ────────────────────────────────────────────────────────────────────

/-- An Abelian group element (exponent monomial): a map from `Id`s to
    `(ExptSort, Coef)` pairs.  Represents x₁^c₁ · x₂^c₂ · … · xₙ^cₙ.
    Mirrors `type Group = Map Id Desc`. -/
abbrev Group := Cpsa2Lean.Lib.RBMap Id Desc


-- ── Symbol ───────────────────────────────────────────────────────────────────

/-- Operation symbols in the Basic Crypto Algebra.
    The constructor order matches the Haskell source (and thus the derived
    `Ord` ordering used by `compareTerm`). -/
inductive Symbol where
  | Data (s : String)   -- atom sort variable
  | Akey (s : String)   -- asymmetric key sort
  | Name                -- principal sort
  | Pval                -- store-point sort
  | Base                -- base of exponentiation
  | Ltk                 -- long-term shared symmetric key
  | Bltk                -- bidirectional ltk
  | Invk (s : String)   -- inverse of asymmetric key
  | Pubk                -- public asymmetric key of a principal
  | Chan                -- channel sort
  | Locn                -- location sort
  | Genr                -- DH generator constant
  | Exp                 -- exponentiation
  | Tupl (s : String)   -- tuple
  | Enc  (s : String)   -- encryption
  | Hash (s : String)   -- hash
  deriving Repr, BEq, DecidableEq

-- PDR: The derived Ord might be wrong. This was AI-generated.
private def Symbol.tag : Symbol → Nat
  | .Data _  => 0  | .Akey _  => 1  | .Name    => 2  | .Pval    => 3
  | .Base    => 4  | .Ltk     => 5  | .Bltk    => 6  | .Invk _  => 7
  | .Pubk    => 8  | .Chan    => 9  | .Locn    => 10 | .Genr    => 11
  | .Exp     => 12 | .Tupl _  => 13 | .Enc  _  => 14 | .Hash _  => 15

instance : Ord Symbol where
  compare s s' :=
    let t := s.tag; let t' := s'.tag
    if t != t' then compare t t'
    else match s, s' with
      | .Data x, .Data x' => compare x x'
      | .Akey x, .Akey x' => compare x x'
      | .Invk x, .Invk x' => compare x x'
      | .Tupl x, .Tupl x' => compare x x'
      | .Enc  x, .Enc  x' => compare x x'
      | .Hash x, .Hash x' => compare x x'
      | _,       _        => .eq

-- ── Term ─────────────────────────────────────────────────────────────────────

/-- A term in the Basic Crypto Algebra.

    Constructors:
    - `I x` — mesg variable
    - `C s` — tag constant (quoted string)
    - `F sym args` — function application
    - `G g` — exponent (Abelian group element)
    - `D x` — strand variable
    - `Z n` — strand constant
    - `X x` — index variable
    - `Y n` — index constant

    The CHECK_CANONICAL invariant: terms must be in canonical form.
    Non-canonical patterns (`invk(invk(-))`, `exp(-,one)`,
    `exp(exp(-,-),-)`) are treated as program errors by `equalTerm`
    and `compareTerm`. -/
inductive Term where
  | I : Id     → Term
  | C : String → Term
  | F : Symbol → List Term → Term
  | G : Group  → Term
  | D : Id     → Term
  | Z : Int    → Term
  | X : Id     → Term
  | Y : Int    → Term
  deriving Repr

instance : Inhabited Term  := ⟨.C ""⟩
instance : Inhabited Group := ⟨Lean.RBMap.empty⟩

-- ── Group comparison (needed by compareTerm for G constructor) ────────────

-- PDR: This should be checked against the Haskell derived ordering
private def compareDesc : Desc → Desc → Ordering
  | (s, c), (s', c') => match compare s s' with
    | .eq => compare c c'
    | o   => o

private def compareGroup (g g' : Group) : Ordering :=
  let rec cmpPairs : List (Id × Desc) → List (Id × Desc) → Ordering
    | [],      []        => .eq
    | [],      _ :: _    => .lt
    | _ :: _,  []        => .gt
    | (k, d) :: ps, (k', d') :: ps' =>
        match compare k k' with
        | .eq => match compareDesc d d' with
          | .eq => cmpPairs ps ps'
          | o   => o
        | o => o
  cmpPairs (Lean.RBMap.toList g) (Lean.RBMap.toList g')

-- ── Canonicality check ───────────────────────────────────────────────────────

-- The most-specific pattern (nested exp) must precede the general exp check.
private def isNonCanonical : Term → Bool
  | .F (.Invk _) [.F (.Invk _) [_]]    => true
  | .F .Exp [.F .Exp [_, .G _], .G _]  => true
  | .F .Exp [_, .G g]                  => Lean.RBMap.isEmpty g
  | _                                  => false

-- ── BEq Term ─────────────────────────────────────────────────────────────────

mutual
  -- PDR: Haskell seems not to enforce canonicity.
  -- May need to follow the CHECK_CANONICAL undefined paths
  private def equalTerm (t t' : Term) : Bool :=
    if isNonCanonical t  then assertError "EQ: non-canonical left term"
    else if isNonCanonical t' then assertError "EQ: non-canonical right term"
    else match t, t' with
    | .I x,   .I y   => x == y
    | .C c,   .C c'  => c == c'
    -- PDR: This could differ from Haskell due to derived order
    | .G g,   .G g'  => compareGroup g g' == .eq
    | .F .Bltk [t0, t1], .F .Bltk [t0', t1'] =>
        (equalTerm t0 t0' && equalTerm t1 t1') ||
        (equalTerm t0 t1' && equalTerm t1 t0')
    | .F s u, .F s' u' => s == s' && equalTermList u u'
    | .D x,   .D y   => x == y
    | .Z p,   .Z p'  => p == p'
    | .X x,   .X y   => x == y
    | .Y n,   .Y n'  => n == n'
    | _,      _      => false

  private def equalTermList : List Term → List Term → Bool
    | [],       []        => true
    | t :: us,  t' :: us' => equalTerm t t' && equalTermList us us'
    | _,        _         => false

end

instance : BEq Term where beq := equalTerm

instance : BEq Group where beq g g' := compareGroup g g' == .eq

-- ── Ord Term ─────────────────────────────────────────────────────────────────

-- Constructor tag for cross-constructor ordering.
-- Order (ascending): I < C < F < G < D < Z < X < Y
private def Term.tag : Term → Nat
  | .I _ => 0 | .C _ => 1 | .F _ _ => 2 | .G _ => 3
  | .D _ => 4 | .Z _ => 5 | .X _   => 6 | .Y _ => 7

mutual

  -- PDR: Try to get rid of partial for this mutual block
  private partial def compareTerm (t t' : Term) : Ordering :=
    if isNonCanonical t  then assertError "COM: non-canonical left term"
    else if isNonCanonical t' then assertError "COM: non-canonical right term"
    else match t, t' with
    | .I x,  .I y  => compare x y
    | .C c,  .C c' => compare c c'
    | .G g,  .G g' => compareGroup g g'
    | .F .Bltk [t0, t1], .F .Bltk [t0', t1'] =>
        let norm  := if compareTerm t0 t1  == .gt then (t1,  t0)  else (t0,  t1)
        let norm' := if compareTerm t0' t1' == .gt then (t1', t0') else (t0', t1')
        compareTermList [norm.1, norm.2] [norm'.1, norm'.2]
    | .F s u, .F s' u' => match compare s s' with
        | .eq => compareTermList u u'
        | o   => o
    | .D x,  .D y  => compare x y
    | .Z p,  .Z p' => compare p p'
    | .X x,  .X y  => compare x y
    | .Y n,  .Y n' => compare n n'
    | _,     _     => compare t.tag t'.tag

  private partial def compareTermList : List Term → List Term → Ordering
    | [],       []        => .eq
    | [],       _ :: _    => .lt
    | _ :: _,   []        => .gt
    | t :: us,  t' :: us' => match compareTerm t t' with
        | .eq => compareTermList us us'
        | o   => o

end

instance : Ord Term where compare := compareTerm

-- ── Group algebraic helpers ───────────────────────────────────────────────────

open Cpsa2Lean.Lib.RBMap in
/-- True when `t` represents a single variable (coefficient 1). -/
def isGroupVar (t : Group) : Bool :=
  size t == 1 && (elems t).head?.map Prod.snd == some 1

open Cpsa2Lean.Lib.RBMap in
/-- True when `t` is a single basis variable (ExptSort.Rndx, coefficient 1). -/
def isBasisVar (t : Group) : Bool :=
  size t == 1 && (elems t).head? == some (.Rndx, 1)

open Cpsa2Lean.Lib.RBMap in
/-- True when `t` is a single exponent variable (ExptSort.Expt, coefficient 1). -/
def isExprVar (t : Group) : Bool :=
  size t == 1 && (elems t).head? == some (.Expt, 1)

open Cpsa2Lean.Lib.RBMap in
/-- Extract the single identifier from a group variable.
    Precondition: `isGroupVar t`, `isBasisVar t`, or `isExprVar t`. -/
def getGroupVar (t : Group) : Id :=
  match (keys t).head? with
  | some x => x
  | none   => assertError "Algebra.getGroupVar: empty group"

open Cpsa2Lean.Lib.RBMap in
/-- All single-variable group elements making up `t`. -/
def groupVarsOfGroup (t : Group) : List Group :=
  foldrWithKey (fun x (s, _) acc => singleton x (s, 1) :: acc) [] t

/-- The singleton group element `{x ↦ (be, 1)}`. -/
def groupVarG (be : ExptSort) (x : Id) : Group :=
  Cpsa2Lean.Lib.RBMap.singleton x (be, 1)

/-- Wrap a group variable as a `Term`. -/
def groupVar (be : ExptSort) (x : Id) : Term :=
  .G (groupVarG be x)

/-- The singleton group element with sort `Expt`. -/
def groupVarGroup (x : Id) : Group :=
  groupVarG .Expt x

/-- Map a function over the coefficient of a `Desc`. -/
def dMapCoef (f : Coef → Coef) (d : Desc) : Desc :=
  (d.1, f d.2)

open Cpsa2Lean.Lib.RBMap in
/-- Negate all coefficients (group inverse). -/
def invert (t : Group) : Group :=
  map (dMapCoef Int.neg) t

open Cpsa2Lean.Lib.RBMap in
/-- Raise `t` to the `n`th power. -/
def expg (t : Group) (n : Int) : Group :=
  if n == 0 then empty
  else if n == 1 then t
  else map (dMapCoef (n * ·)) t

open Cpsa2Lean.Lib.RBMap in
/-- Group multiplication (addition of exponents).
    Mirrors the Haskell `mul` which folds `alter` over one map into the other. -/
def mul (t t' : Group) : Group :=
  foldrWithKey
    (fun x desc acc =>
      alter
        (fun existing =>
          match existing with
          | none => some desc
          | some (be', c') =>
            if desc.1 != be' then
              assertError "Algebra.mul: sort mismatch"
            else
              let c'' := desc.2 + c'
              if c'' == 0 then none else some (be', c''))
        x acc)
    t' t

-- ── Maplet helpers ───────────────────────────────────────────────────────────

/-- A single key-value pair of a `Group`. -/
abbrev Maplet := Id × Desc

/-- Map a function over the coefficient of a `Maplet`. -/
def mMapCoef (f : Coef → Coef) (m : Maplet) : Maplet :=
  (m.1, dMapCoef f m.2)

/-- Negate all coefficients in a list of maplets. -/
def mInverse (ms : List Maplet) : List Maplet :=
  ms.map (mMapCoef Int.neg)

/-- True when the maplet has a non-zero coefficient. -/
def isMapletNonzero (m : Maplet) : Bool :=
  m.2.2 != 0

open Cpsa2Lean.Lib.RBMap in
/-- Build a `Group` from a list of maplets, dropping zero-coefficient entries. -/
def group (ms : List Maplet) : Group :=
  fromList (ms.filter isMapletNonzero)

-- ── exprVars and separateVar ──────────────────────────────────────────────────

open Cpsa2Lean.Lib.RBMap in
/-- The list of group variables appearing in an exponent term.
    Mirrors `exprVars :: Term -> [Term]`. -/
def exprVars : Term → List Term
  | .G g => foldlWithKey (fun acc x (s, _) => groupVar s x :: acc) [] g
  | _    => assertError "Algebra.exprVars: not an exponent"

open Cpsa2Lean.Lib.RBMap in
/-- Separate variable `var` from `t`: returns `(singleton_negated, rest)`,
    or `none` if `var` does not appear in `t`.
    Mirrors `separateVar :: Id -> Group -> Maybe (Group, Group)`. -/
def separateVar (var : Id) (t : Group) : Option (Group × Group) :=
  match lookup var t with
  | none            => none
  | some (be, coef) =>
    some (singleton var (be, -coef), delete var t)

-- ── Term predicate helpers ────────────────────────────────────────────────────

/-- True when `s` is a variable-bearing symbol. -/
def varSym : Symbol → Bool
  | .Data _ | .Akey _ | .Name | .Pval | .Base | .Chan | .Locn => true
  | _ => false

/-- True when `t` is an algebra variable (of any sort). -/
def isVar : Term → Bool
  | .I _        => true
  | .F s [.I _] => varSym s
  | .G g        => isGroupVar g
  | _           => false

/-- True when `t` is a channel variable. -/
def isChan : Term → Bool
  | .F .Chan [.I _] => true
  | _               => false

/-- True when `t` is a location variable. -/
def isLocn : Term → Bool
  | .F .Locn [.I _] => true
  | _               => false

/-- True when `t` is a strand variable (`D x`). -/
def isStrdVar : Term → Bool
  | .D _ => true | _ => false

/-- True when `t` is an index variable (`X x`). -/
def isIndxVar : Term → Bool
  | .X _ => true | _ => false

/-- True when `t` is an index constant (`Y n`). -/
def isIndxConst : Term → Bool
  | .Y _ => true | _ => false

/-- Extract the integer from an index constant, or `none`. -/
def intOfIndex : Term → Option Int
  | .Y q => some q | _ => none

/-- Extract the `Id` from a variable term.  Panics on non-variables. -/
def varId : Term → Id
  | .I x                => x
  | .F (.Data _) [.I x] => x
  | .F (.Akey _) [.I x] => x
  | .F .Name     [.I x] => x
  | .F .Base     [.I x] => x
  | .F .Pval     [.I x] => x
  | .F .Chan     [.I x] => x
  | .F .Locn     [.I x] => x
  | .G g                => getGroupVar g
  | .D x                => x
  | .X x                => x
  | _                   => assertError "Algebra.varId: term not a variable"

/-- True when `t` is an acquired variable (mesg sort). -/
def isAcquiredVar : Term → Bool
  | .I _ => true | _ => false

/-- True when `t` is an obtained variable (expt base or expt variable). -/
def isObtainedVar : Term → Bool
  | .G x            => isExprVar x
  | .F .Base [.I _] => true
  | _               => false

-- ── Type aliases and newtypes ─────────────────────────────────────────────────

/-- A map from `Id`s to `Term`s, used for substitutions and environments. -/
abbrev IdMap := Cpsa2Lean.Lib.RBMap Id Term

def emptyIdMap : IdMap := Cpsa2Lean.Lib.RBMap.empty

/-- An environment tracking variable-to-variable sorts during well-formedness
    checking.  Mirrors `newtype VarEnv = VarEnv (Map Id Term)`. -/
structure VarEnv where
  map : IdMap

def emptyVarEnv : VarEnv := ⟨Cpsa2Lean.Lib.RBMap.empty⟩

/-- A path into a term (list of child indices).
    Mirrors `newtype Place = Place [Int]`. -/
structure Place where
  path : List Int
  deriving Repr, BEq

/-- A substitution: a map from `Id`s to `Term`s with no trivial
    (identity) bindings.  Mirrors `newtype Subst = Subst IdMap`. -/
structure Subst where
  map : IdMap
  deriving Repr

def emptySubst : Subst := ⟨Cpsa2Lean.Lib.RBMap.empty⟩

/-- A matching environment: a set of generated variable identifiers plus
    an `IdMap`.  Mirrors `newtype Env = Env (Set Id, IdMap)`. -/
structure Env where
  vars : Cpsa2Lean.Lib.RBSet Id
  map  : IdMap
  deriving Repr

def emptyEnv : Env := ⟨Lean.RBMap.empty, Cpsa2Lean.Lib.RBMap.empty⟩

private def eqIdMap (m m' : IdMap) : Bool :=
  Lean.RBMap.toList m == Lean.RBMap.toList m'

instance : BEq IdMap where beq := eqIdMap
instance : BEq Subst  where beq s s' := s.map == s'.map

private def eqRBSetId (s s' : Cpsa2Lean.Lib.RBSet Id) : Bool :=
  Lean.RBMap.toList s == Lean.RBMap.toList s'

instance : BEq (Cpsa2Lean.Lib.RBSet Id) where beq := eqRBSetId
instance : BEq Env    where beq e e' := e.vars == e'.vars && e.map == e'.map

instance : Inhabited Env := ⟨emptyEnv⟩

/-- A generator paired with a matching environment. -/
abbrev GenEnv := Gen × Env

instance : Inhabited GenEnv := ⟨(origin, emptyEnv)⟩

/-- A specification of variable lists grouped by sort name.
    Mirrors `type VarListSpec = [(String, [String])]`. -/
abbrev VarListSpec := List (String × List String)

/-- A display context: a list of `(Id, display-name)` pairs.
    Mirrors `newtype Context = Context [(Id, String)]`. -/
structure Context where
  pairs : List (Id × String)
  deriving Repr

def emptyContext : Context := ⟨[]⟩
instance : Inhabited Context := ⟨emptyContext⟩

-- ── Decision ─────────────────────────────────────────────────────────────────

/-- A set of sameness and distinctness decisions over pairs of values.
    Mirrors `data Decision t`. -/
structure Decision (t : Type) where
  same : List (t × t)
  dist : List (t × t)
  deriving Repr

/-- An initial (empty) decision set. -/
def mkDecis : Decision Id := ⟨[], []⟩

-- ── Stage 2: IdMap operations ─────────────────────────────────────────────────

/-- Look up a group element in an `IdMap`, returning the singleton group
    variable `{x ↦ (be, 1)}` if the key is absent.
    Panics if the key maps to a non-`G` term.
    Mirrors `groupLookup :: IdMap -> Sort -> Id -> Group`. -/
def groupLookup (subst : IdMap) (be : ExptSort) (x : Id) : Group :=
  match Cpsa2Lean.Lib.RBMap.findWithDefault (.G (groupVarG be x)) x subst with
  | .G t => t
  | _    => assertError s!"Algebra.groupLookup: Bad substitution for {idName x}"

-- `idSubst`, `expSubst`, and `groupSubst` are mutually recursive:
--   idSubst    calls expSubst (Exp case) and groupSubst (G case)
--   expSubst   calls groupSubst
--   groupSubst calls groupLookup (not recursive), expg, mul
mutual

  /-- Apply an `IdMap` as a substitution to a term.
      Reduces `invk(invk(t)) → t` and `exp(exp(g,x),y) → exp(g,mul(x,y))`.
      Mirrors `idSubst :: IdMap -> Term -> Term`. -/
  private partial def idSubst (subst : IdMap) : Term → Term
    | .F .Exp []         => assertError "Algebra.idSubst: Bad exponentiation"
    | .I x               => Cpsa2Lean.Lib.RBMap.findWithDefault (.I x) x subst
    | t@(.C _)           => t
    | .F (.Invk op) [t]  =>
        match idSubst subst t with
        | .F (.Invk _) [t'] => t'           -- invk(invk(t)) = t
        | t'                => .F (.Invk op) [t']
    | .F .Exp [t0, .G t1] =>
        match idSubst subst t0 with
        | .F .Exp [t0', .G t1'] =>
            let t2 := mul t1' (groupSubst subst t1)
            if Lean.RBMap.isEmpty t2 then t0'
            else .F .Exp [t0', .G t2]
        | t0' => expSubst subst t0' t1
    | .F s u             => .F s (u.map (idSubst subst))
    | .G t               => .G (groupSubst subst t)
    | .D x               => Cpsa2Lean.Lib.RBMap.findWithDefault (.D x) x subst
    | t@(.Z _)           => t
    | .X x               => Cpsa2Lean.Lib.RBMap.findWithDefault (.X x) x subst
    | t@(.Y _)           => t

  /-- Substitute into an exponent and apply `exp(g, one) = g`.
      Mirrors `expSubst :: IdMap -> Term -> Group -> Term`. -/
  private partial def expSubst (subst : IdMap) (t0 : Term) (t1 : Group) : Term :=
    let t1' := groupSubst subst t1
    if Lean.RBMap.isEmpty t1' then t0
    else .F .Exp [t0, .G t1']

  /-- Apply an `IdMap` substitution to every variable in a group element.
      Mirrors `groupSubst :: IdMap -> Group -> Group`. -/
  private partial def groupSubst (subst : IdMap) (t : Group) : Group :=
    Cpsa2Lean.Lib.RBMap.foldrWithKey
      (fun x (be, c) acc => mul (expg (groupLookup subst be x) c) acc)
      Lean.RBMap.empty t

end

/-- True when every variable in `t` is a key in `subst`.
    Mirrors `idMapped :: IdMap -> Term -> Bool`. -/
partial def idMapped (subst : IdMap) : Term → Bool
  | .I x    => Cpsa2Lean.Lib.RBMap.member x subst
  | .C _    => true
  | .F _ u  => u.all (idMapped subst)
  | .G t    => (Cpsa2Lean.Lib.RBMap.keys t).all (Cpsa2Lean.Lib.RBMap.member · subst)
  | .D x    => Cpsa2Lean.Lib.RBMap.member x subst
  | .Z _    => true
  | .X x    => Cpsa2Lean.Lib.RBMap.member x subst
  | .Y _    => true

/-- Variables in `t` whose identifier is NOT a key in `m`.
    Mirrors `idUnmapped :: IdMap -> Term -> [Term]`. -/
partial def idUnmapped (m : IdMap) : Term → List Term
  | .I x =>
      if Cpsa2Lean.Lib.RBMap.member x m then [] else [.I x]
  | .D x =>
      if Cpsa2Lean.Lib.RBMap.member x m then [] else [.D x]
  | .X x =>
      if Cpsa2Lean.Lib.RBMap.member x m then [] else [.X x]
  | .C _ | .Z _ | .Y _ => []
  | .G t =>
      (groupVarsOfGroup t).filter
        (fun g => !Cpsa2Lean.Lib.RBMap.member (getGroupVar g) m)
      |>.map .G
  | t@(.F s [.I x]) =>
      if varSym s then
        if Cpsa2Lean.Lib.RBMap.member x m then [] else [t]
      else idUnmapped m (.I x)
  | .F (.Akey str) [.F (.Invk _) [.I x]] =>
      if Cpsa2Lean.Lib.RBMap.member x m then []
      else [.F (.Akey str) [.I x]]
  | .F _ u => u.flatMap (idUnmapped m)

/-- The domain of an `IdMap` as a list of keys.
    Mirrors `idMapDomain :: IdMap -> [Id]`. -/
def idMapDomain (m : IdMap) : List Id :=
  Cpsa2Lean.Lib.RBMap.foldrWithKey (fun k _ ks => k :: ks) [] m

-- Not currently used in the CPSA source (commented out in Algebra.hs),
-- but preserved to match the Haskell comment "let's not wipe them out".

/-- True when `m1` is a sub-function of `m2` (same domain entries, same values). -/
private def idMapExtendsTo (m1 m2 : IdMap) : Bool :=
  Cpsa2Lean.Lib.RBMap.foldrWithKey
    (fun key val acc =>
      acc &&
      match Cpsa2Lean.Lib.RBMap.lookup key m2 with
      | some v => val == v
      | none   => false)
    true m1

/-- Identifiers that are in the domain of `m1` but not `m2`. -/
private def idMapDomainMinus (m1 m2 : IdMap) : List Id :=
  Cpsa2Lean.Lib.RBMap.foldrWithKey
    (fun key _ acc =>
      if Cpsa2Lean.Lib.RBMap.member key m2 then acc else key :: acc)
    [] m1

/-- True when `m1` is a sub-function of `m2` ignoring keys in `ids`.
    Mirrors `idMapExtendsOutside :: IdMap -> IdMap -> [Id] -> Bool`. -/
def idMapExtendsOutside (m1 m2 : IdMap) (ids : List Id) : Bool :=
  Cpsa2Lean.Lib.RBMap.foldrWithKey
    (fun key val acc =>
      acc &&
      (ids.contains key ||
        match Cpsa2Lean.Lib.RBMap.lookup key m2 with
        | some v => val == v
        | none   => false))
    true m1

/-- True when `m1` and `m2` agree on all keys outside `ids`.
    Mirrors `idMapsAgreeOutside :: IdMap -> IdMap -> [Id] -> Bool`. -/
def idMapsAgreeOutside (m1 m2 : IdMap) (ids : List Id) : Bool :=
  idMapExtendsOutside m1 m2 ids && idMapExtendsOutside m2 m1 ids

-- ── Stage 2: Subst operations ─────────────────────────────────────────────────

/-- Apply a `Subst` to a term.
    Mirrors `substitute :: Subst -> Term -> Term`. -/
def substitute (s : Subst) (t : Term) : Term :=
  idSubst s.map t

/-- The domain of a substitution.
    Mirrors `substDomain :: Subst -> [Id]`. -/
def substDomain (s : Subst) : List Id :=
  idMapDomain s.map

/-- True when every id in the domain of `s` is the `varId` of some term
    in `vars`.  Each term in `vars` is assumed to be a variable.
    Mirrors `substDomainWithin :: Subst -> [Term] -> Bool`. -/
def substDomainWithin (s : Subst) (vars : List Term) : Bool :=
  Cpsa2Lean.Lib.subset (substDomain s) (vars.map varId)

/-- True when `f` holds for every `Id` that appears as a leaf variable in `t`.
    Mirrors `allId :: (Id -> Bool) -> Term -> Bool`. -/
partial def allId (f : Id → Bool) : Term → Bool
  | .I x   => f x
  | .C _   => true
  | .F _ u => u.all (allId f)
  | .G g   => (Cpsa2Lean.Lib.RBMap.keys g).all f
  | .D x   => f x
  | .Z _   => true
  | .X x   => f x
  | .Y _   => true

/-- True when the domain of `s` is disjoint from the variables in `ts`.
    Mirrors `disjointDom :: Subst -> [Term] -> Bool`. -/
def disjointDom (s : Subst) (ts : List Term) : Bool :=
  let ks := Cpsa2Lean.Lib.RBMap.keysSet s.map
  ts.all (allId (fun x => Cpsa2Lean.Lib.RBSet.notMember x ks))

/-- True when `t` is NOT a trivial identity binding for `x`.
    Mirrors `nonTrivialBinding :: Id -> Term -> Bool`. -/
private def nonTrivialBinding (x : Id) : Term → Bool
  | .I y  => x != y
  | t@(.G _) => !(t == groupVar .Rndx x || t == groupVar .Expt x)
  | _     => true

/-- Compose two substitutions: `substitute (compose s0 s1) t = substitute s0 (substitute s1 t)`.
    Mirrors `compose :: Subst -> Subst -> Subst`. -/
def compose (s0 s1 : Subst) : Subst :=
  -- Step 1: apply s0 to the range of s1
  let s2 := Cpsa2Lean.Lib.RBMap.map (substitute s0) s1.map
  -- Step 3: drop trivial bindings from s2
  let s4 := Cpsa2Lean.Lib.RBMap.filterWithKey nonTrivialBinding s2
  -- Steps 2 & 4: left-biased union (s0 dominates where domains overlap)
  ⟨Cpsa2Lean.Lib.RBMap.union s4 s0.map⟩

/-- If `t` is a group variable, return a substitution mapping it to the
    group identity (the empty group / "one").  Otherwise `none`.
    Mirrors `destroyer :: Term -> Maybe Subst`. -/
def destroyer : Term → Option Subst
  | t@(.G m) =>
      if isVar t then
        match (Cpsa2Lean.Lib.RBMap.keys m).head? with
        | some x => some ⟨Cpsa2Lean.Lib.RBMap.singleton x (.G Lean.RBMap.empty)⟩
        | none   => assertError "Algebra.destroyer: isVar but empty group"
      else none
  | _ => none

-- `substInvertibly`, `substInvertibleOn`, and `absentEnv` are deferred to
-- Stage 6 because they depend on `match` (the term matcher).

-- ── Stage 3: Term analysis + well-formedness ──────────────────────────────────

/-- Ordered set of terms. -/
abbrev TermSet := Cpsa2Lean.Lib.RBSet Term

-- ── Well-formedness ───────────────────────────────────────────────────────────

/-- Extend `xts` with the binding `x ↦ t`, checking that any existing
    binding for `x` is consistent.
    Mirrors `extendVarEnv :: VarEnv -> Id -> Term -> Maybe VarEnv`. -/
def extendVarEnv (xts : VarEnv) (x : Id) (t : Term) : Option VarEnv :=
  match Cpsa2Lean.Lib.RBMap.lookup x xts.map with
  | none    => some ⟨Cpsa2Lean.Lib.RBMap.insert x t xts.map⟩
  | some t' => if t == t' then some xts else none

-- `termWellFormed` and `baseVarEnv` are mutually recursive:
-- `termWellFormed` dispatches to `baseVarEnv` for `F Base [t]` terms, and
-- `baseVarEnv` calls back to `termWellFormed` for `G t1` inside exp terms.
mutual

  /-- Check that a term has the correct structure and that every identifier
      is used consistently.  Returns the extended environment, or `none` if
      the term is ill-formed.
      Mirrors `termWellFormed :: VarEnv -> Term -> Maybe VarEnv`. -/
  private partial def termWellFormed (xts : VarEnv) : Term → Option VarEnv
    | t@(.I x)                                   => extendVarEnv xts x t
    | t@(.F (.Data _) [.I x])                    => extendVarEnv xts x t
    | .F (.Data "skey") [.F .Ltk  [.I x, .I y]] =>
        [.F .Name [.I x], .F .Name [.I y]].foldlM termWellFormed xts
    | .F (.Data "skey") [.F .Bltk [.I x, .I y]] =>
        [.F .Name [.I x], .F .Name [.I y]].foldlM termWellFormed xts
    | .F (.Akey op) [t] =>
        match t with
        | .I x =>
            extendVarEnv xts x (.F (.Akey op) [.I x])
        | .F (.Invk op') [.I x] =>
            if op' == op then extendVarEnv xts x (.F (.Akey op) [.I x]) else none
        | .F .Pubk [.I x] =>
            if op == "akey" then extendVarEnv xts x (.F .Name [.I x]) else none
        | .F .Pubk [.C _, .I x] =>
            if op == "akey" then extendVarEnv xts x (.F .Name [.I x]) else none
        | .F (.Invk "akey") [.F .Pubk [.I x]] =>
            if op == "akey" then extendVarEnv xts x (.F .Name [.I x]) else none
        | .F (.Invk "akey") [.F .Pubk [.C _, .I x]] =>
            if op == "akey" then extendVarEnv xts x (.F .Name [.I x]) else none
        | _ => none
    | t@(.F .Name [.I x])  => extendVarEnv xts x t
    | t@(.F .Pval [.I x])  => extendVarEnv xts x t
    | .F .Base [t]         => baseVarEnv xts t
    | .G t                 =>
        (Cpsa2Lean.Lib.RBMap.assocs t).foldlM
          (fun xts' (x, (be, _)) => extendVarEnv xts' x (groupVar be x))
          xts
    | .C _                 => some xts
    | .F (.Tupl _) ts      => ts.foldlM termWellFormed xts
    | .F (.Enc _) [t1, t2]  => [t1, t2].foldlM termWellFormed xts
    | .F (.Hash _) [t]     => termWellFormed xts t
    | _                    => none

  /-- Well-formedness check for the body of a `F Base [t]` term. -/
  private partial def baseVarEnv (xts : VarEnv) : Term → Option VarEnv
    | t@(.I x)                       => extendVarEnv xts x (.F .Base [t])
    | .F .Genr []                    => some xts
    | .F .Exp [.F .Exp _, _]         => none   -- non-canonical
    | .F .Exp [t0, .G t1]            => do
        let xts' ← baseVarEnv xts t0
        termWellFormed xts' (.G t1)
    | _                              => none

end

/-- True when every term in `u` is well-formed and uses each identifier
    consistently.
    Mirrors `termsWellFormed :: [Term] -> Bool`. -/
def termsWellFormed (u : List Term) : Bool :=
  let rec loop (env : VarEnv) : List Term → Bool
    | []      => true
    | t :: ts =>
        match termWellFormed env t with
        | none      => false
        | some env' => loop env' ts
  loop emptyVarEnv u

-- ── Key inversion ─────────────────────────────────────────────────────────────

/-- The inverse of an asymmetric key term, or `none` for non-keys.
    Mirrors `invertKey :: Term -> Maybe Term`. -/
def invertKey : Term → Option Term
  | .F (.Akey op) [.F (.Invk _) [t]] => some (.F (.Akey op) [t])
  | .F (.Akey op) [t]                => some (.F (.Akey op) [.F (.Invk op) [t]])
  | _                                => none

/-- Invert an asymmetric key term; panics on non-key and non-invertible terms.
    Mirrors `inv :: Term -> Term` (internal helper for `decompose`). -/
def inv : Term → Term
  | .F (.Akey op) [.F (.Invk _) [t]] => .F (.Akey op) [t]
  | .F (.Akey op) [t]                => .F (.Akey op) [.F (.Invk op) [t]]
  | t@(.F _ _)                       => t
  | t@(.G _)                         => t
  | _                                => assertError "Algebra.inv: cannot invert this term"

-- ── Atom predicates ───────────────────────────────────────────────────────────

/-- True when `t` is of a base atom sort (not `Base`; used for `nons`/`uniqs`).
    Mirrors `isAtom :: Term -> Bool`. -/
def isAtom : Term → Bool
  | .F .Base _  => false
  | .F s _      => varSym s
  | .G x        => isBasisVar x
  | _           => false

/-- True when `t` is numeric (a base or exponent term).
    Mirrors `isNum :: Term -> Bool`. -/
def isNum : Term → Bool
  | .F .Base _ => true
  | .G _       => true
  | _          => false

/-- The set of numeric sub-terms of `t`.
    Mirrors `subNums :: Term -> Set Term`. -/
partial def subNums : Term → TermSet
  | t@(.G _)  => Cpsa2Lean.Lib.RBSet.singleton t
  | .F _ ts   => Cpsa2Lean.Lib.RBSet.unions (ts.map subNums)
  | _         => Lean.RBMap.empty

-- ── Occurrence / subterm ──────────────────────────────────────────────────────

/-- True when `needle` is a structural sub-term (or equals) `haystack`.
    Used by `occursIn` and `constituent`.
    Mirrors `subterm :: Term -> Term -> Bool`. -/
partial def subterm (needle : Term) : Term → Bool
  | haystack =>
    if needle == haystack then true
    else match haystack with
    | .F _ u   => u.any (subterm needle)
    | .G t'    => match needle with
        | .I x => Cpsa2Lean.Lib.RBMap.member x t'
        | .G t => isGroupVar t && Cpsa2Lean.Lib.RBMap.member (getGroupVar t) t'
        | _    => false
    | _ => false

/-- True when variable `t` occurs in term `t'`.
    Mirrors `occursIn :: Term -> Term -> Bool`. -/
def occursIn (t t' : Term) : Bool :=
  if isVar t then subterm (.I (varId t)) t'
  else assertError "Algebra.occursIn: not a variable"

-- ── Variable folding ──────────────────────────────────────────────────────────

-- `foldVars` and `baseAddVars` are mutually recursive:
-- `foldVars` handles `F Base [t]` by calling `baseAddVars`, and
-- `baseAddVars` handles exp nodes by calling back to `foldVars`.
mutual

  /-- Fold `f` through every variable leaf of `t`.
      Mirrors `foldVars :: (a -> Term -> a) -> a -> Term -> a`. -/
  partial def foldVars {α : Type} [Inhabited α] (f : α → Term → α) (acc : α) : Term → α
    | t@(.I _)                                       => f acc t
    | t@(.F (.Data _) [.I _])                        => f acc t
    | .F (.Data _) [.F .Ltk  [.I x, .I y]]          =>
        f (f acc (.F .Name [.I x])) (.F .Name [.I y])
    | .F (.Data _) [.F .Bltk [.I x, .I y]]          =>
        f (f acc (.F .Name [.I x])) (.F .Name [.I y])
    | t@(.F (.Akey _) [.I _])                        => f acc t
    | .F op@(.Akey _) [.F (.Invk _) [.I x]]         => f acc (.F op [.I x])
    | .F (.Akey _)    [.F .Pubk [.I x]]             => f acc (.F .Name [.I x])
    | .F (.Akey _)    [.F .Pubk [.C _, .I x]]       => f acc (.F .Name [.I x])
    | .F (.Akey _)    [.F (.Invk _) [.F .Pubk [.I x]]]       =>
        f acc (.F .Name [.I x])
    | .F (.Akey _)    [.F (.Invk _) [.F .Pubk [.C _, .I x]]] =>
        f acc (.F .Name [.I x])
    | t@(.F .Name [.I _])                            => f acc t
    | t@(.F .Pval [.I _])                            => f acc t
    | t@(.F .Chan [.I _])                            => f acc t
    | t@(.F .Locn [.I _])                            => f acc t
    | .F .Base [t]                                   => baseAddVars f acc t
    | .G t                                           =>
        Cpsa2Lean.Lib.RBMap.foldlWithKey
          (fun acc' x (be, _) => f acc' (groupVar be x))
          acc t
    | .C _                                           => acc
    | .F (.Tupl _) ts                                =>
        ts.foldl (fun a t => foldVars f a t) acc
    | .F (.Enc _) [t0, t1]                           =>
        foldVars f (foldVars f acc t0) t1
    | .F (.Hash _) [t]                               => foldVars f acc t
    | t@(.D _)                                       => f acc t
    | .Z _                                           => acc
    | t@(.X _)                                       => f acc t
    | .Y _                                           => acc
    | _                                              =>
        assertError "Algebra.foldVars: Bad term"

  /-- Helper for `foldVars` that handles the body of a `F Base [t]` term. -/
  private partial def baseAddVars {α : Type} [Inhabited α] (f : α → Term → α) (acc : α) : Term → α
    | t@(.I _)               => f acc (.F .Base [t])
    | .F .Genr []            => acc
    | .F .Exp [t0, .G t1]    =>
        foldVars f (baseAddVars f acc t0) (.G t1)
    | _                      => assertError "Algebra.foldVars: Bad term in F Base"

end

/-- Fold `f` over each term carried by `t` (tuples and encryptions).
    Mirrors `foldCarriedTerms :: (a -> Term -> a) -> a -> Term -> a`. -/
partial def foldCarriedTerms {α : Type} (f : α → Term → α) (acc : α) : Term → α
  | t@(.F (.Tupl _) ts)      =>
      ts.foldl (fun a t => foldCarriedTerms f a t) (f acc t)
  | t@(.F (.Enc _) [t0, _])  => foldCarriedTerms f (f acc t) t0
  | t                        => f acc t

/-- True when `t` is carried by `t'` (i.e., `t'` contains `t` as a
    carried sub-term through tuples and encryptions).
    Mirrors `carriedBy :: Term -> Term -> Bool`. -/
partial def carriedBy (t : Term) : Term → Bool
  | t' => t == t' ||
    match t' with
    | .F (.Tupl _) ts     => ts.any (carriedBy t)
    | .F (.Enc _) [t0, _] => carriedBy t t0
    | _                   => false

/-- True when `t` (an atom) is a constituent of `t'`.
    Mirrors `constituent :: Term -> Term -> Bool`. -/
def constituent (t t' : Term) : Bool :=
  if isAtom t then subterm t t'
  else assertError "Algebra.constituent: not an atom"

/-- All sorted variables appearing in `t`, deduplicated.
    Mirrors `sortedVarsIn :: Term -> [Term]`. -/
def sortedVarsIn (t : Term) : List Term :=
  (foldVars (fun acc v => v :: acc) [] t).eraseDups

-- ── Decryption key / components / encryptions ─────────────────────────────────

/-- The decryption key for an encrypted term, or `none`.
    Mirrors `decryptionKey :: Term -> Maybe Term`. -/
def decryptionKey : Term → Option Term
  | .F (.Enc _) [_, t] => some (inv t)
  | _                  => none

/-- The flat list of component terms of a tuple, or `[t]` for non-tuples.
    Mirrors `components :: Term -> [Term]`. -/
partial def components : Term → List Term
  | .F (.Tupl _) ts => (ts.flatMap components).eraseDups
  | t               => [t]

private partial def encryptionsHelper :
    Term → List (Term × List Term) → List (Term × List Term)
  | .F (.Tupl _) ts, acc =>
      ts.foldl (fun a b => encryptionsHelper b a) acc
  | t@(.F (.Enc _) [t', t'']), acc =>
      encryptionsHelper t' (Cpsa2Lean.Lib.adjoin (t, [t'']) acc)
  | t@(.F (.Hash _) [t']), acc =>
      Cpsa2Lean.Lib.adjoin (t, [t']) acc
  | _, acc => acc

/-- Every encryption (and hash) carried by `t`, paired with its key.
    Mirrors `encryptions :: Term -> [(Term, [Term])]`. -/
def encryptions (t : Term) : List (Term × List Term) :=
  (encryptionsHelper t []).reverse

-- ── Buildable / decompose helpers ─────────────────────────────────────────────

/-- Identifiers of exponent variables in the unguessable set (approximation).
    Mirrors `getRndxOrigAssumptions :: Set Term -> [Id]`. -/
def getRndxOrigAssumptions (terms : TermSet) : List Id :=
  (Cpsa2Lean.Lib.RBSet.elems terms).flatMap fun
    | .G t => Cpsa2Lean.Lib.RBMap.keys t
    | _    => []

/-- Collapse nested `exp` applications into a single `exp`.
    Mirrors `expCollapse :: Term -> Term`. -/
private partial def expCollapse : Term → Term
  | .F .Base [.F .Genr ts]                         => .F .Base [.F .Genr ts]
  | .F .Base [.F .Exp [.F .Exp [b, .G e0], .G e1]] =>
      match expCollapse (.F .Base [.F .Exp [b, .G e0]]) with
      | .F .Base [.F .Exp [b', .G e0']] => .F .Base [.F .Exp [b', .G (mul e0' e1)]]
      | _ => assertError "Algebra.expCollapse: bad inner collapse"
  | .F .Base [.F .Exp [b, .G e]]                   => .F .Base [.F .Exp [b, .G e]]
  | .F .Base [.I t]                                 => .F .Base [.I t]
  | _                                              => assertError "Algebra.expCollapse: non-base element"

/-- Extract the base of a base-sort term (before any exponentiation).
    Mirrors `getBase :: Term -> Term`. -/
private def getBase : Term → Term
  | .F .Base [.F .Genr _]  => .F .Base [.F .Genr []]
  | t@(.F .Base _) =>
      match expCollapse t with
      | .F .Base [.F .Exp [b, _]] => b
      | _                         => t
  | t => t

private def eqGroup (g g' : Group) : Bool :=
  compareGroup g g' == .eq

/-- Compute the exponent indicator of `t` restricted to variables in `avoid`.
    Mirrors `indicator :: Set Term -> Term -> Group`. -/
private def indicator (avoid : TermSet) (t : Term) : Group :=
  let basisGroups : List Group :=
    (Cpsa2Lean.Lib.RBSet.elems avoid).filterMap fun
      | .G g => if isBasisVar g then some g else none
      | _    => none
  let indicatorBasis := basisGroups.foldl mul Lean.RBMap.empty
  match expCollapse t with
  | .F .Base [.F .Genr _]        => Lean.RBMap.empty
  | .F .Base [.I _]              => Lean.RBMap.empty
  | .F .Base [.F .Exp [_, .G m]] =>
      Cpsa2Lean.Lib.RBMap.intersection m indicatorBasis
  | _ => assertError "Algebra.indicator: expCollapse returned non-base element"

/-- True when `t1` and `t2` have the same indicator relative to `avoid`.
    Mirrors `relevant :: Set Term -> Term -> Term -> Bool`. -/
private def relevant (avoid : TermSet) : Term → Term → Bool
  | t1@(.F .Base _), t2@(.F .Base _) =>
      (indicator avoid t1) == (indicator avoid t2)
  | t1, t2 => t1 == t2

-- `buildable'`, `buildableBase`, and `buildableExpt` are mutually recursive.
mutual

  private partial def buildable' (knowns unguessable : TermSet) : Term → Bool
    | .I _              => true
    | .C _              => true
    | .F (.Tupl _) ts   => ts.all (buildable' knowns unguessable)
    | t@(.F (.Enc _) [t0, t1]) =>
        Cpsa2Lean.Lib.RBSet.member t knowns ||
        buildable' knowns unguessable t0 && buildable' knowns unguessable t1
    | t@(.F (.Hash _) [t1]) =>
        Cpsa2Lean.Lib.RBSet.member t knowns || buildable' knowns unguessable t1
    | t@(.F .Base _)    => buildableBase knowns unguessable t
    | .G t1             => buildableExpt unguessable t1
    | t                 => isAtom t && !Cpsa2Lean.Lib.RBSet.member t unguessable

  private partial def buildableBase (knowns unguessable : TermSet) : Term → Bool
    | .F .Base [.I _]         => true
    | .F .Base [.F .Genr _]   => true
    | t@(.F .Base [.F .Exp [t0, .G t1]]) =>
        (Cpsa2Lean.Lib.RBSet.elems knowns).any
          (fun t2 => getBase t2 == t0 && relevant unguessable t2 t)
        || buildableBase knowns unguessable (.F .Base [t0]) && buildableExpt unguessable t1
    | _ => false

  private partial def buildableExpt (unguessable : TermSet) (exp : Group) : Bool :=
    let ids := getRndxOrigAssumptions unguessable
    (Cpsa2Lean.Lib.RBMap.keys exp).all (fun x => !ids.contains x)

end

/-- True when `term` can be built from `knowns` given `unguessable` atoms.
    Mirrors `buildable :: Set Term -> Set Term -> Term -> Bool`. -/
def buildable (knowns unguessable : TermSet) (t : Term) : Bool :=
  buildable' knowns unguessable t

-- ── Decompose ────────────────────────────────────────────────────────────────

/-- Flatten a tuple term into a set, inserting non-tuple elements.
    Mirrors the `decat` helper inside `decompose`. -/
private partial def decat (t : Term) (s : TermSet) : TermSet :=
  match t with
  | .F (.Tupl _) ts => ts.foldl (fun acc b => decat b acc) s
  | t               => Lean.RBMap.insert s t ()

private partial def decomposeLoop
    (ug ks old : TermSet) (todo : List Term) : TermSet × TermSet :=
  match todo with
  | [] =>
      if Lean.RBMap.toList old == Lean.RBMap.toList ks then (ks, ug)
      else decomposeLoop ug ks ks (Cpsa2Lean.Lib.RBSet.elems ks)
  | t@(.F (.Tupl _) _) :: rest =>
      decomposeLoop ug (decat t (Cpsa2Lean.Lib.RBSet.delete t ks)) old rest
  | .F (.Enc _) [t0, t1] :: rest =>
      if buildable ks ug (inv t1) then
        decomposeLoop ug (decat t0 ks) old rest
      else
        decomposeLoop ug ks old rest
  | .F (.Hash _) [_] :: rest =>
      decomposeLoop ug ks old rest
  | .F .Base [.F .Exp [_, _]] :: rest =>
      decomposeLoop ug ks old rest
  | t@(.G _) :: rest =>
      if Cpsa2Lean.Lib.RBSet.notMember t ug then
        decomposeLoop ug ks old rest
      else
        decomposeLoop
          (Cpsa2Lean.Lib.RBSet.delete t ug) (Cpsa2Lean.Lib.RBSet.delete t ks) old rest
  | t :: rest =>
      decomposeLoop
        (Cpsa2Lean.Lib.RBSet.delete t ug) (Cpsa2Lean.Lib.RBSet.delete t ks) old rest

/-- Iteratively decompose `knowns` given `unguessable` atoms.
    Returns the final `(knowns, unguessable)` pair.
    Mirrors `decompose :: Set Term -> Set Term -> (Set Term, Set Term)`. -/
def decompose (knowns unguessable : TermSet) : TermSet × TermSet :=
  decomposeLoop unguessable knowns Lean.RBMap.empty []

/-- The encryptions in `ts` that are not buildable and carry `ct`.
    Mirrors `escapeSet :: Set Term -> Set Term -> Term -> Maybe (Set Term)`. -/
def escapeSet (ts a : TermSet) (ct : Term) : Option TermSet :=
  if buildable ts a ct then none
  else some (Cpsa2Lean.Lib.RBSet.filter
    (fun t => match t with
      | .F (.Enc _) [body, key] => carriedBy ct body && !buildable ts a (inv key)
      | _                       => false)
    ts)

-- ── Simple term predicates ────────────────────────────────────────────────────

def isBase : Term → Bool | .F .Base _ => true | _ => false
def isExpr : Term → Bool | .G _ => true | _ => false

/-- True when `t` is a group variable (exponent variable). -/
def isVarExpr : Term → Bool | .G g => isGroupVar g | _ => false

/-- True when `t` is a basis variable (rndx sort). -/
def isRndx : Term → Bool | .G t => isBasisVar t | _ => false

/-- The set of constants associated with a term's sort.
    Mirrors `consts :: Term -> [Term]`. -/
def consts : Term → List Term
  | .F .Base _ => [.F .Base [.F .Genr []]]
  | .G _       => [.G Lean.RBMap.empty]
  | _          => []

-- ── Location message helpers ──────────────────────────────────────────────────

/-- True when `t` is a location message `(cat (pval x) payload)`.
    Mirrors `isLocnMsg :: Term -> Bool`. -/
def isLocnMsg : Term → Bool
  | .F (.Tupl "cat") [.F .Pval [.I _], _] => true
  | _                                      => false

/-- Extract the payload of a location message, or return `t` unchanged.
    Mirrors `locnMsgPayload :: Term -> Term`. -/
def locnMsgPayload : Term → Term
  | m@(.F (.Tupl "cat") [pt, t]) =>
      match pt with | .F .Pval [.I _] => t | _ => m
  | t => t

/-- Extract the point of a location message, or fail.
    Mirrors `locnMsgPoint :: MonadFail m => Term -> m Term` as `Except String`. -/
def locnMsgPoint : Term → Except String Term
  | .F (.Tupl "cat") [pt, _] =>
      match pt with
      | .F .Pval [.I _] => .ok pt
      | _               => .error "locnMsgPoint: Bad point"
  | _ => .error "locnMsgPoint: Bad state message"

-- ── Stage 4A: Place operations ───────────────────────────────────────────────

/-- The list of places where `var` occurs within `source`.
    Mirrors `places :: Term -> Term -> [Place]`. -/
partial def places (var source : Term) : List Place :=
  let rec f (paths : List Place) (path : List Int) (t : Term) : List Place :=
    if var == t then ⟨path.reverse⟩ :: paths
    else match t with
    | .F _ u =>
        u.enum.foldl (fun ps (i, ti) => f ps ((i : Int) :: path) ti) paths
    | .G g =>
        if Lean.RBMap.contains g (varId var)
        then ⟨path.reverse⟩ :: paths
        else paths
    | _ => paths
  f [] [] source

/-- The list of places where `target` is carried by `source`
    (through tuples and the plaintext slot of encryptions).
    Mirrors `carriedPlaces :: Term -> Term -> [Place]`. -/
partial def carriedPlaces (target source : Term) : List Place :=
  let rec f (paths : List Place) (path : List Int) (t : Term) : List Place :=
    if target == t then ⟨path.reverse⟩ :: paths
    else match t with
    | .F (.Tupl _) ts =>
        ts.enum.foldl (fun ps (i, ti) => f ps ((i : Int) :: path) ti) paths
    | .F (.Enc _) [t0, _] => f paths (0 :: path) t0
    | _ => paths
  f [] [] source

/-- Like `carriedPlaces` but using `relevant` in place of equality.
    Mirrors `carriedRelPlaces :: Term -> Term -> Set Term -> [Place]`. -/
partial def carriedRelPlaces (target source : Term) (avoid : TermSet) : List Place :=
  let rec f (paths : List Place) (path : List Int) (t : Term) : List Place :=
    if relevant avoid t target then ⟨path.reverse⟩ :: paths
    else match t with
    | .F (.Tupl _) ts =>
        ts.enum.foldl (fun ps (i, ti) => f ps ((i : Int) :: path) ti) paths
    | .F (.Enc _) [t0, _] => f paths (0 :: path) t0
    | _ => paths
  f [] [] source

/-- Replace the sub-term at `pl` within `source` with `var`.
    Mirrors `replace :: Term -> Place -> Term -> Term`. -/
def replace (var : Term) (pl : Place) (source : Term) : Term :=
  let rec loop : List Int → Term → Term
    | [],        _      => var
    | i :: path, .F s u =>
        let n := i.toNat
        match u.get? n with
        | some ti => .F s (Cpsa2Lean.Lib.replaceNth (loop path ti) n u)
        | none    => assertError "Algebra.replace: Bad path to term"
    | _,         _      => assertError "Algebra.replace: Bad path to term"
  loop pl.path source

/-- Expand a group into a list of maplets with multiplicity.
    Positive coefficient `n` → `n` copies of `(x, (be, 1))`;
    negative `n` → `|n|` copies of `(x, (be, -1))`.
    Mirrors `factors :: Group -> [Maplet]`. -/
def factors (t : Group) : List Maplet :=
  Cpsa2Lean.Lib.RBMap.foldrWithKey
    (fun x (be, n) acc =>
      if n >= 0
      then List.replicate n.toNat (x, (be, 1)) ++ acc
      else List.replicate (-n).toNat (x, (be, -1)) ++ acc)
    [] t

/-- Return the ancestor terms along `pl` within `source`.
    Mirrors `ancestors :: Term -> Place -> [Term]`. -/
def ancestors (source : Term) (pl : Place) : List Term :=
  let rec loop (ts : List Term) : List Int → Term → List Term
    | [],        _           => ts
    | i :: path, t@(.F _ u) =>
        match u.get? i.toNat with
        | some t' => loop (t :: ts) path t'
        | none    => assertError "Algebra.ancestors: Bad path to term"
    | [_],       t@(.G _)   => t :: ts
    | _,         _           => assertError "Algebra.ancestors: Bad path to term"
  loop [] pl.path source

/-- True when `p` is a prefix of `p'`.
    Mirrors `placeIsPrefixOf :: Place -> Place -> Bool`. -/
def placeIsPrefixOf (p p' : Place) : Bool :=
  let rec isPre : List Int → List Int → Bool
    | [],      _        => true
    | _,       []       => false
    | i :: l,  i' :: l' => i == i' && isPre l l'
  isPre p.path p'.path

/-- Strip `p` as a prefix from `p'`, returning the suffix.
    Mirrors `placeStripPrefix :: Place -> Place -> Maybe Place`. -/
def placeStripPrefix (p p' : Place) : Option Place :=
  let rec loop : List Int → List Int → Option Place
    | [],       l'         => some ⟨l'⟩
    | i :: l,   i' :: l'  => if i == i' then loop l l' else none
    | _ :: _,   []         => none
  loop p.path p'.path

/-- Rename all identifiers in `t` with fresh ones drawn from `gen`.
    Mirrors `clone :: Gen -> Term -> (Gen, Term)`. -/
partial def clone (gen : Gen) (t : Term) : Gen × Term :=
  let rec cloneTerm (alist : List (Id × Id)) (gen : Gen) (t : Term)
      : List (Id × Id) × Gen × Term :=
    match t with
    | .I x =>
        match List.lookup x alist with
        | some y => (alist, gen, .I y)
        | none   =>
            let (gen', y) := cloneId gen x
            ((x, y) :: alist, gen', .I y)
    | .C c => (alist, gen, .C c)
    | .F sym u =>
        let (alist', gen', uRev) := u.foldl
          (fun (al, g, us) ti =>
            let (al', g', t') := cloneTerm al g ti
            (al', g', t' :: us))
          (alist, gen, [])
        (alist', gen', .F sym uRev.reverse)
    | .G g =>
        let (alist', gen', msRev) :=
          Cpsa2Lean.Lib.RBMap.foldlWithKey
            (fun (al, ge, ms) x (be, n) =>
              match List.lookup x al with
              | some y => (al, ge, (y, (be, n)) :: ms)
              | none   =>
                  let (ge', y) := cloneId ge x
                  ((x, y) :: al, ge', (y, (be, n)) :: ms))
            (alist, gen, []) g
        (alist', gen', .G (group msRev))
    | .D x =>
        match List.lookup x alist with
        | some y => (alist, gen, .D y)
        | none   =>
            let (gen', y) := cloneId gen x
            ((x, y) :: alist, gen', .D y)
    | .Z p => (alist, gen, .Z p)
    | .X x =>
        match List.lookup x alist with
        | some y => (alist, gen, .X y)
        | none   =>
            let (gen', y) := cloneId gen x
            ((x, y) :: alist, gen', .X y)
    | .Y p => (alist, gen, .Y p)
  let (_, gen', t') := cloneTerm [] gen t
  (gen', t')

/-- Simplify a base-sort exponentiation term by collapsing trivial
    (empty-exponent) and nested exponentiations.
    Mirrors `simplifyBase :: Term -> Term`. -/
partial def simplifyBase : Term → Term
  | .F .Exp [.F .Exp [t, .G g0], .G g1] =>
      simplifyBase (.F .Exp [t, .G (mul g0 g1)])
  | .F .Exp [t, .G g] =>
      if Lean.RBMap.isEmpty g then simplifyBase t
      else .F .Exp [t, .G g]
  | t => t

/-- Build a pair `(cat (base e^{-w}) w)` where `w` is a fresh exponent
    variable.  Used to compute "base precursors" in bundle analysis.
    Mirrors `basePrecursor :: Gen -> Term -> (Gen, Term)`. -/
def basePrecursor (g : Gen) : Term → Gen × Term
  | .F .Base [t] =>
      let (g', x) := freshId g "w"
      let x' := groupVarG .Expt x
      (g', .F (.Tupl "cat")
        [.F .Base [simplifyBase (.F .Exp [t, .G (invert x')])],
         .G x'])
  | _ => assertError "Algebra.basePrecursor: Bad term"

/-- Build a pair `(cat (base (gen^{g ∖ {var}})) (rndx-var))` from
    group `g` and one of its basis variables `var`.
    Mirrors `baseBuild :: Group -> Id -> Term`. -/
def baseBuild (g : Group) (var : Id) : Term :=
  .F (.Tupl "cat")
    [.F .Base [.F .Exp [.F .Genr [], .G (Lean.RBMap.erase g var)]],
     groupVar .Rndx var]

/-- If `t` is `(base (exp (gen) g))` where `g` has more than one
    basis variable (all `Rndx`), split it into `baseBuild` pairs.
    Mirrors `baseRndx :: Term -> Maybe [Term]`. -/
def baseRndx : Term → Option (List Term)
  | .F .Base [.F .Exp [.F .Genr [], .G g]] =>
      if Lean.RBMap.size g > 1 then
        let rec loop (acc : List Term) : List (Id × Desc) → Option (List Term)
          | []                        => some acc
          | (_, (.Expt, _)) :: _     => none
          | (id, (.Rndx, _)) :: rest => loop (baseBuild g id :: acc) rest
        loop [] (Cpsa2Lean.Lib.RBMap.assocs g)
      else none
  | _ => none

-- ── Stage 4B: Chase operations ────────────────────────────────────────────────

mutual
  /-- Apply an `IdMap` substitution to a group element by replacing each
      group variable with its looked-up group (or itself if absent).
      Mirrors `chaseGroup :: IdMap -> Group -> Group`. -/
  private partial def chaseGroup (s : IdMap) (t : Group) : Group :=
    Cpsa2Lean.Lib.RBMap.foldrWithKey
      (fun x (be, c) acc => mul (expg (chaseGroupLookup s be x) c) acc)
      Lean.RBMap.empty t

  /-- Look up `x` in `s`; if bound to a group, chase that group;
      otherwise return the singleton group `{x ↦ (be, 1)}`.
      Mirrors `chaseGroupLookup :: IdMap -> Sort -> Id -> Group`. -/
  private partial def chaseGroupLookup (s : IdMap) (be : ExptSort) (x : Id) : Group :=
    match Cpsa2Lean.Lib.RBMap.lookup x s with
    | none       => groupVarG be x
    | some (.G t) => chaseGroup s t
    | some _     => assertError "Algebra.chaseGroupLookup: Bad substitution"
end

/-- If `t1` is empty return `t0`; otherwise wrap as `(exp t0 t1)`.
    Mirrors `chaseExpFinalize :: Term -> Group -> Term`. -/
def chaseExpFinalize (t0 : Term) (t1 : Group) : Term :=
  if Lean.RBMap.isEmpty t1 then t0
  else .F .Exp [t0, .G t1]

mutual
  /-- Find the canonical representative of a term under substitution `s`.
      Mirrors `chase :: Subst -> Term -> Term`. -/
  partial def chase (s : Subst) : Term → Term
    | .I x =>
        match Cpsa2Lean.Lib.RBMap.lookup x s.map with
        | none   => .I x
        | some t => chase s t
    | .D x =>
        match Cpsa2Lean.Lib.RBMap.lookup x s.map with
        | none   => .D x
        | some t => chase s t
    | .F (.Invk op) [t]    => chaseInvk s op t
    | .F .Exp [t0, .G t1]  => chaseExp s t0 t1
    | .G t                  => .G (chaseGroup s.map t)
    | t                     => t

  /-- Chase through an `Invk` wrapper.
      Mirrors `chaseInvk :: Subst -> String -> Term -> Term`. -/
  private partial def chaseInvk (s : Subst) (op : String) : Term → Term
    | .I x =>
        match Cpsa2Lean.Lib.RBMap.lookup x s.map with
        | none   => .F (.Invk op) [.I x]
        | some t => chaseInvk s op t
    | .F (.Invk _) [t] => chase s t
    | t                => .F (.Invk op) [t]

  /-- Chase through an `Exp` wrapper, merging exponents.
      Mirrors `chaseExp :: Subst -> Term -> Group -> Term`. -/
  private partial def chaseExp (s : Subst) (t0 : Term) (t1 : Group) : Term :=
    if Lean.RBMap.isEmpty t1 then chase s t0
    else match t0 with
    | .I _ =>
        match chase s t0 with
        | .F .Exp [t0', .G t1'] =>
            chaseExpFinalize t0' (mul t1' (chaseGroup s.map t1))
        | t0' => chaseExpFinalize t0' (chaseGroup s.map t1)
    | .F .Exp [t0', .G t1'] => chaseExp s t0' (mul t1 t1')
    | _ => chaseExpFinalize t0 (chaseGroup s.map t1)
end

/-- A chasing version of substitution: applies `chase` then recursively
    rebuilds the term.
    Mirrors `substChase :: Subst -> Term -> Term`. -/
partial def substChase (subst : Subst) : Term → Term
  | t =>
    match chase subst t with
    | t@(.I _) => t
    | t@(.C _) => t
    | .F (.Invk op) [t] =>
        match substChase subst t with
        | .F (.Invk op') [t'] => if op == op' then t' else .F (.Invk op) [.F (.Invk op') [t']]
        | t'                  => .F (.Invk op) [t']
    | .F .Exp [t0, .G t1] =>
        match substChase subst t0 with
        | .F .Exp [t0', .G t1'] =>
            let t2 := mul t1' (chaseGroup subst.map t1)
            if Lean.RBMap.isEmpty t2 then t0' else .F .Exp [t0', .G t2]
        | t0' => chaseExp subst t0' t1
    | .F s u => .F s (u.map (substChase subst))
    | .G t   => .G (chaseGroup subst.map t)
    | t@(.D _) => t
    | t@(.Z _) => t
    | t@(.X _) => t
    | t@(.Y _) => t

/-- Apply `substChase` to every value in the range of `s`.
    Mirrors `chaseMap :: Subst -> Subst`. -/
def chaseMap (s : Subst) : Subst :=
  ⟨Cpsa2Lean.Lib.RBMap.map (substChase s) s.map⟩

-- ── Stage 4B: Environment operations ─────────────────────────────────────────

/-- Apply the environment's map to `t`.
    Mirrors `instantiate :: Env -> Term -> Term`. -/
def instantiate (e : Env) (t : Term) : Term := idSubst e.map t

/-- True when every variable in `t` is in the domain of the environment.
    Mirrors `matched :: Env -> Term -> Bool`. -/
def matched (e : Env) (t : Term) : Bool := idMapped e.map t

/-- True when every unmatched variable of `t` that appears in `idUnmapped`
    is contained in `vars`.
    Mirrors `unmatchedVarsWithin :: Env -> Term -> [Term] -> Bool`. -/
def unmatchedVarsWithin (e : Env) (t : Term) (vars : List Term) : Bool :=
  (idUnmapped e.map t).all (vars.contains ·)

/-- Filter `vars` to those variables not in the environment's domain.
    Mirrors `varsMinusEnvDomain :: Env -> [Term] -> [Term]`. -/
def varsMinusEnvDomain (e : Env) (vars : List Term) : List Term :=
  vars.filter (fun v => isVar v && !idMapped e.map v)

/-- True when `e1` and `e2` agree on all `vars` outside each other's domain.
    Mirrors `envsAgreeOutside :: Env -> Env -> [Term] -> Bool`. -/
def envsAgreeOutside (e1 e2 : Env) (vars : List Term) : Bool :=
  idMapsAgreeOutside e1.map e2.map (vars.map varId)

/-- Build an environment from a list of `(param, var)` pairs, keeping the
    first binding for each parameter variable.
    Mirrors `envOfParamVarPairs :: [(Term,Term)] -> Env`. -/
def envOfParamVarPairs (pairs : List (Term × Term)) : Env :=
  pairs.foldl
    (fun e (p, v) =>
      if idMapped e.map p then e
      else { e with map := Cpsa2Lean.Lib.RBMap.insert (varId p) v e.map })
    emptyEnv

/-- Build an environment that maps each variable to itself.
    Mirrors `envIdentityOnVars :: [Term] -> Env`. -/
def envIdentityOnVars (vars : List Term) : Env :=
  envOfParamVarPairs (vars.zip vars)

/-- True when every strand value in the range of `e` is within `strands`.
    Mirrors `envStrandsWithin :: Env -> [Int] -> Bool`. -/
def envStrandsWithin (e : Env) (strands : List Int) : Bool :=
  Cpsa2Lean.Lib.RBMap.foldr
    (fun t acc =>
      match t with
      | .Z i => acc && strands.contains i
      | _    => acc)
    true e.map

/-- True when the domain of `e1` is a subset of the domain of `e2` and
    they agree on the domain of `e1`.
    Mirrors `envDisjointExtension :: Env -> Env -> Bool`. -/
def envDisjointExtension (e1 e2 : Env) : Bool :=
  let d1 := idMapDomain e1.map
  let d2 := idMapDomain e2.map
  Cpsa2Lean.Lib.subset d1 d2 && idMapsAgreeOutside e1.map e2.map d1

/-- Apply substitution `s` to every term in the range of `e`.
    Mirrors `substUpdate :: Env -> Subst -> Env`. -/
def substUpdate (e : Env) (s : Subst) : Env :=
  { e with map := Cpsa2Lean.Lib.RBMap.map (substitute s) e.map }

/-- True when every id in `e.vars` and every key and value-id in `e.map`
    was generated before `gen`.
    Mirrors `checkGenEnv :: GenEnv -> Bool`. -/
partial def checkGenTerm (g : Int) : Term → Bool
  | .I x  => g > x.num
  | .C _  => true
  | .F _ xs => xs.all (checkGenTerm g)
  | .G t  =>
      Cpsa2Lean.Lib.RBMap.foldlWithKey
        (fun acc x _ => acc && g > x.num)
        true t
  | _     => true

def checkGenEnv (ge : GenEnv) : Bool :=
  let (g, e) := ge
  let gn := g.counter
  (Cpsa2Lean.Lib.RBSet.toList e.vars |>.all (fun x => gn > x.num)) &&
  (Cpsa2Lean.Lib.RBMap.assocs e.map |>.all (fun (x, t) =>
    gn > x.num && checkGenTerm gn t))

def validateGenEnv (ge : GenEnv) : GenEnv :=
  if checkGenEnv ge then ge
  else assertError "Algebra.validateGenEnv: Bad genenv"

/-- Cast an environment into a substitution by filtering trivial bindings.
    Mirrors `substitution :: Env -> Subst`. -/
def substitution (e : Env) : Subst :=
  ⟨Cpsa2Lean.Lib.RBMap.filterWithKey nonTrivialBinding e.map⟩

/-- Find the smallest strand index `i+1` such that `Z i` appears in `e`.
    Mirrors `strandBoundEnv :: Env -> Int`. -/
def strandBoundEnv (e : Env) : Int :=
  Cpsa2Lean.Lib.RBMap.foldl
    (fun bnd t => match t with | .Z i => max bnd (i + 1) | _ => bnd)
    0 e.map

-- ── Stage 4D part 1: Group matching solver ────────────────────────────────────

/-- Apply `r` to the LHS group `t`, moving matched entries to the RHS `t'`.
    Mirrors `merge :: Group -> Group -> IdMap -> (Group, Group)`. -/
def mergeGroups (t t' : Group) (r : IdMap) : Group × Group :=
  let (rawLHS, rhs) :=
    Cpsa2Lean.Lib.RBMap.foldlWithKey
      (fun (lhsAcc, rhsAcc) x (be, c) =>
        match Cpsa2Lean.Lib.RBMap.lookup x r with
        | none        => ((x, (be, c)) :: lhsAcc, rhsAcc)
        | some (.G g) => (lhsAcc, mul (expg g (-c)) rhsAcc)
        | some _      => assertError "Algebra.merge: expecting a group")
      ([], t') t
  (group rawLHS, rhs)

/-- For each non-freshly-generated variable in `t`, create a clone and
    add a mapping from old → new.
    Mirrors `genVars :: Set Id -> Gen -> Group -> IdMap -> (Set Id, Gen, IdMap)`. -/
def genVars (v : Cpsa2Lean.Lib.RBSet Id) (g : Gen) (t : Group) (r : IdMap)
    : Cpsa2Lean.Lib.RBSet Id × Gen × IdMap :=
  Cpsa2Lean.Lib.RBMap.foldlWithKey
    (fun (v', g', r') x (be, _) =>
      if Cpsa2Lean.Lib.RBSet.member x v' then (v', g', r')
      else
        let (g'', x') := cloneId g' x
        (Cpsa2Lean.Lib.RBSet.insert x' v', g'',
         Cpsa2Lean.Lib.RBMap.insert x (groupVar be x') r'))
    (v, g, r) t

/-- Build an initial decision set that keeps all non-fresh `Rndx`
    variables in `t` distinct.
    Mirrors `mkInitMatchDecis :: Set Id -> Group -> Decision Id`. -/
def mkInitMatchDecis (vs : Cpsa2Lean.Lib.RBSet Id) (t : Group) : Decision Id :=
  let v := (Cpsa2Lean.Lib.RBMap.assocs t).filterMap
    (fun (x, (be, _)) =>
      if be == .Rndx && !Cpsa2Lean.Lib.RBSet.member x vs then some x else none)
  { mkDecis with
    dist := v.flatMap (fun x =>
      v.filterMap (fun y => if x != y then some (x, y) else none)) }

/-- Split `t0` and `t1` into variable and constant parts.
    Mirrors `partition :: Group -> Group -> Set Id -> ([Maplet], [Maplet])`. -/
def groupPartition (t0 t1 : Group) (v : Cpsa2Lean.Lib.RBSet Id)
    : List Maplet × List Maplet :=
  let isExpt (d : Desc) := d.1 != .Rndx
  let (v1, c1) := Cpsa2Lean.Lib.RBMap.partitionWithKey
    (fun x d => Cpsa2Lean.Lib.RBSet.member x v && isExpt d) t1
  let (v0, c0) := Cpsa2Lean.Lib.RBMap.partition isExpt t0
  let lhs := mul v0 (invert v1)
  let rhs := mul c1 (invert c0)
  (Cpsa2Lean.Lib.RBMap.assocs lhs, Cpsa2Lean.Lib.RBMap.assocs rhs)

/-- Find the canonical representative of `x` under the `same` list.
    Mirrors `listChase :: Eq t => [(t, t)] -> t -> t`. -/
partial def listChase {α : Type} [BEq α] (d : List (α × α)) (x : α) : α :=
  match d.find? (fun (k, _) => k == x) with
  | none        => x
  | some (_, y) => listChase d y

/-- Find pairs of variables for which no decision has been made.
    Mirrors `nextDecis :: Decision Id -> [Maplet] -> [(Id, Id)]`. -/
def nextDecis (d : Decision Id) (t : List Maplet) : List (Id × Id) :=
  let vars := t.filterMap (fun (x, (be, _)) => if be == .Rndx then some x else none)
  let chase := listChase d.same
  let decided (x y : Id) : Bool :=
    let u := chase x; let v := chase y
    u == v || d.dist.any (fun (w, z) => chase w == u && chase z == v)
  vars.flatMap (fun x => vars.filterMap (fun y =>
    if compare x y == .lt && !decided x y then some (x, y) else none))

/-- Orient each undecided pair so the first element is a fresh variable.
    Mirrors `orientDecis :: Set Id -> [(Id, Id)] -> [(Id, Id)]`. -/
def orientDecis (v : Cpsa2Lean.Lib.RBSet Id) (pairs : List (Id × Id)) : List (Id × Id) :=
  pairs.map (fun (x, y) =>
    if Cpsa2Lean.Lib.RBSet.notMember x v then (y, x) else (x, y))

/-- Replace all occurrences of `x` by `y` in maplet list `t`, then
    remove any zero-coefficient entries and the `x` entry.
    Mirrors `identify :: Id -> Id -> [Maplet] -> [Maplet]`. -/
def identify (x y : Id) (t : List Maplet) : List Maplet :=
  match t.find? (fun (z, _) => z == x) with
  | none             => assertError "Algebra.identify: bad lookup"
  | some (_, (_, c)) =>
      (t.map (fun (z, (be, d)) =>
        if z == y then (z, (be, c + d)) else (z, (be, d)))).filter
      (fun (z, (_, d)) => z != x && d != 0)

/-- Apply `idSubst (M.singleton x t)` to every value in `r`.
    Mirrors `eliminate :: Id -> Term -> IdMap -> IdMap`. -/
def eliminate (x : Id) (t : Term) (r : IdMap) : IdMap :=
  Cpsa2Lean.Lib.RBMap.map
    (idSubst (Cpsa2Lean.Lib.RBMap.singleton x t))
    r

/-- Drop the element at position `n` from a list.
    Mirrors `omit :: Int -> [a] -> [a]`. -/
partial def omitNth {α : Type} (n : Int) : List α → List α
  | []      =>
      if n == 0 then []
      else assertError "Algebra.omitNth: number given to omitNth too large"
  | _ :: l  =>
      if n < 0 then assertError "Algebra.omitNth: negative number given to omitNth"
      else if n == 0 then l
      else omitNth (n - 1) l

def divisible (ci : Int) (t : List Maplet) : Bool :=
  t.all (fun (_, (_, c)) => c % ci == 0)

def divide (ci : Int) (t : List Maplet) : List Maplet :=
  t.map (fun (x, (be, c)) => (x, (be, c / ci)))

def modulo (ci : Int) (t : List Maplet) : List Maplet :=
  t.filterMap (fun (x, (be, c)) =>
    let c' := c % ci
    if c' != 0 then some (x, (be, c')) else none)

/-- Find the maplet with smallest non-zero absolute coefficient.
    Returns `(variable, coefficient, position)`.
    Mirrors `smallest :: [Maplet] -> (Id, Int, Int)`. -/
def smallest (t : List Maplet) : Id × Int × Int :=
  match t with
  | [] => assertError "Algebra.smallest: empty list"
  | (x0, (_, c0)) :: rest =>
      rest.enum.foldl
        (fun (v, ci, pos) (j, (x, (_, c))) =>
          if (j + 1 : Int) >= 0 && c.natAbs > 0 && c.natAbs < ci.natAbs
          then (x, c, j + 1)
          else (v, ci, pos))
        (x0, c0, 0)

private partial def constSolve1 (t : List Maplet) (v : Cpsa2Lean.Lib.RBSet Id) (g : Gen)
    (r : IdMap) (d : Decision Id) : List (Cpsa2Lean.Lib.RBSet Id × Gen × IdMap) :=
  if t.isEmpty then [(v, g, r)]
  else
    match orientDecis v (nextDecis d t) with
    | [] => []
    | (x, y) :: _ =>
        let neq := { d with dist := (x, y) :: (y, x) :: d.dist }
        let distinct := constSolve1 t v g r neq
        let y' := groupVar .Rndx y
        let d' := { d with same := (x, y) :: d.same }
        let t' := identify x y t
        let v' := Cpsa2Lean.Lib.RBSet.delete x v
        let r' := eliminate x y' r
        let identified := constSolve1 t' v' g r' d'
        distinct ++ identified

/-- Solve when there are no expr variables on the LHS.
    Mirrors `constSolve`. -/
def constSolve (t : List Maplet) (v : Cpsa2Lean.Lib.RBSet Id) (g : Gen) (r : IdMap)
    (d : Decision Id) : List (Cpsa2Lean.Lib.RBSet Id × Gen × IdMap) :=
  if t.any (fun (_, (be, _)) => be != .Rndx) then []
  else constSolve1 t v g r d

mutual
  /-- Solve the linear equation `t0 = t1` over group variables (expr case).
      Mirrors `solve`. -/
  private partial def solve
      (t0 t1 : List Maplet) (v : Cpsa2Lean.Lib.RBSet Id) (g : Gen) (r : IdMap)
      (d : Decision Id) : List (Cpsa2Lean.Lib.RBSet Id × Gen × IdMap) :=
    let (x, ci, i) := smallest t0
    if ci > 0 then agSolve x ci i t0 t1 v g r d
    else if ci < 0 then agSolve x (-ci) i (mInverse t0) (mInverse t1) v g r d
    else assertError "Algebra.solve: zero coefficient found"

  /-- One step of the AG algorithm.  Mirrors `agSolve`. -/
  private partial def agSolve
      (x : Id) (ci i : Int) (t0 t1 : List Maplet) (v : Cpsa2Lean.Lib.RBSet Id)
      (g : Gen) (r : IdMap) (d : Decision Id)
      : List (Cpsa2Lean.Lib.RBSet Id × Gen × IdMap) :=
    if ci == 1 then
      let t := .G (group (t1 ++ mInverse (omitNth i t0)))
      [(Cpsa2Lean.Lib.RBSet.delete x v, g, eliminate x t r)]
    else if divisible ci t0 then
      if divisible ci t1 then agSolve x 1 i (divide ci t0) (divide ci t1) v g r d
      else identSolve x ci i t0 t1 v g r d
    else
      let (g', x') := cloneId g x
      let t := .G (group ((x', (.Expt, 1)) :: mInverse (divide ci (omitNth i t0))))
      let r' := eliminate x t r
      let t0' := (x', (.Expt, ci)) :: modulo ci (omitNth i t0)
      solve t0' t1 (Cpsa2Lean.Lib.RBSet.insert x' (Cpsa2Lean.Lib.RBSet.delete x v)) g' r' d

  /-- Explore two choices (distinct vs identified) for a pair of rndx vars.
      Mirrors `identSolve`. -/
  private partial def identSolve
      (z : Id) (ci i : Int) (t0 t1 : List Maplet) (v : Cpsa2Lean.Lib.RBSet Id)
      (g : Gen) (r : IdMap) (d : Decision Id)
      : List (Cpsa2Lean.Lib.RBSet Id × Gen × IdMap) :=
    match orientDecis v (nextDecis d t1) with
    | [] => []
    | (x, y) :: _ =>
        let neq := { d with dist := (x, y) :: (y, x) :: d.dist }
        let distinct := identSolve z ci i t0 t1 v g r neq
        let y' := groupVar .Rndx y
        let d' := { d with same := (x, y) :: d.same }
        let t1' := identify x y t1
        let v' := Cpsa2Lean.Lib.RBSet.delete x v
        let r' := eliminate x y' r
        let identified := agSolve z ci i t0 t1' v' g r' d'
        distinct ++ identified
end

/-- Unify pattern group `t0` against target group `t1` under
    environment `(v, g, r)`.
    Mirrors `matchGroup`. -/
def matchGroup (t0 t1 : Group) (v : Cpsa2Lean.Lib.RBSet Id) (g : Gen) (r : IdMap)
    : List (Cpsa2Lean.Lib.RBSet Id × Gen × IdMap) :=
  let (t0', t1') := mergeGroups t0 t1 r
  let (v', g', r') := genVars v g t0' r
  let d := mkInitMatchDecis v' t1'
  match groupPartition (groupSubst r' t0') t1' v' with
  | ([], [])   => [(v', g', r')]
  | ([], t)    => constSolve t v' g' r' d
  | (ts0, ts1) => solve ts0 ts1 v' g' r' d

-- ── Stage 4C: Unification ─────────────────────────────────────────────────────

/-- True when identifier `x` occurs in term `t`.
    Mirrors `occurs :: Id -> Term -> Bool`. -/
partial def occurs (x : Id) : Term → Bool
  | .I y    => x == y
  | .C _    => false
  | .F _ u  => u.any (occurs x)
  | .G t    => Lean.RBMap.contains t x
  | .D y    => x == y
  | .Z _    => false
  | .X y    => x == y
  | .Y _    => false

/-- A generator paired with a substitution; used internally during unification. -/
abbrev GenSubst := Gen × Subst

mutual
  /-- Chase both terms then unify.
      Mirrors `unifyChase :: Term -> Term -> GenSubst -> [GenSubst]`. -/
  private partial def unifyChase (t t' : Term) (gs : GenSubst) : List GenSubst :=
    unifyTerms (chase gs.2 t) (chase gs.2 t') gs

  /-- Unify two (already-chased) terms.
      Mirrors `unifyTerms`. -/
  private partial def unifyTerms (t t' : Term) (gs : GenSubst) : List GenSubst :=
    let (g, ⟨s⟩) := gs
    match t, t' with
    | .I x, .I y =>
        if x == y then [gs]
        else [(g, ⟨Cpsa2Lean.Lib.RBMap.insert x (.I y) s⟩)]
    | .I x, _ =>
        if occurs x t' then []
        else [(g, ⟨Cpsa2Lean.Lib.RBMap.insert x t' s⟩)]
    | _, .I _ => unifyTerms t' t gs
    | .C c, .C c' => if c == c' then [gs] else []
    | .F (.Invk "akey") [.I x], .F .Pubk [.I y] =>
        unifyTerms (.I x) (.F (.Invk "akey") [.F .Pubk [.I y]]) gs
    | .F (.Invk "akey") [.I x], .F .Pubk [.C c, .I y] =>
        unifyTerms (.I x) (.F (.Invk "akey") [.F .Pubk [.C c, .I y]]) gs
    | .F .Pubk [.I x], .F (.Invk "akey") [.I y] =>
        unifyTerms (.I y) (.F (.Invk "akey") [.F .Pubk [.I x]]) gs
    | .F .Pubk [.C c, .I x], .F (.Invk "akey") [.I y] =>
        unifyTerms (.I y) (.F (.Invk "akey") [.F .Pubk [.C c, .I x]]) gs
    | .F .Bltk u, .F .Bltk u' =>
        (unifyTermLists u u' gs ++ unifyTermLists u u'.reverse gs).eraseDups
    | .F .Base [t0], .F .Base [t1] =>
        unifyBase (chase gs.2 t0) (chase gs.2 t1) gs
    | .F sym u, .F sym' u' =>
        if sym == sym' then unifyTermLists u u' gs else []
    | .G t0, .G t1 => unifyGroup t0 t1 gs
    | .D x, .D y =>
        if x == y then [gs]
        else [(g, ⟨Cpsa2Lean.Lib.RBMap.insert x (.D y) s⟩)]
    | .D x, .Z p => [(g, ⟨Cpsa2Lean.Lib.RBMap.insert x (.Z p) s⟩)]
    | _, .D _ => unifyTerms t' t gs
    | .Z p, .Z p' => if p == p' then [gs] else []
    | _, _ => []

  /-- Unify two base-sort terms (stripped of their `F Base` wrapper).
      Mirrors `unifyBase`. -/
  private partial def unifyBase (t0 t1 : Term) (gs : GenSubst) : List GenSubst :=
    match t0, t1 with
    | .F .Exp [b0, .G e0], .F .Exp [b1, .G e1] => unifyExp b0 e0 b1 e1 gs
    | .F .Exp [b0, .G e0], .I x                => unifyExp b0 e0 (.I x) Lean.RBMap.empty gs
    | .F .Exp [b0, .G e0], .F .Genr []         => unifyExp b0 e0 (.F .Genr []) Lean.RBMap.empty gs
    | .I x, .F .Exp [b1, .G e1]                => unifyExp (.I x) Lean.RBMap.empty b1 e1 gs
    | .I x, .I y                               => unifyExp (.I x) Lean.RBMap.empty (.I y) Lean.RBMap.empty gs
    | .I x, .F .Genr []                        => unifyExp (.I x) Lean.RBMap.empty (.F .Genr []) Lean.RBMap.empty gs
    | _, _                                     => unifyTerms t0 t1 gs

  /-- Unify two exponential forms `t0^e0` and `t0'^e1`.
      Mirrors `unifyExp`. -/
  private partial def unifyExp (t0 : Term) (e0 : Group) (t0' : Term) (e1 : Group)
      (gs : GenSubst) : List GenSubst :=
    let (g, ⟨s⟩) := gs
    match t0, t0' with
    | .F .Exp _, _ => assertError "Algebra.unifyExp: non-canonical form"
    | _, .F .Exp _ => assertError "Algebra.unifyExp: non-canonical form"
    | _, _ =>
      if t0 == t0' then unifyGroup e0 e1 gs
      else match t0, t0' with
      | .I x1, .I x2 =>
          let (g', zid) := freshId g "z"
          let z := groupVarGroup zid
          unifyGroup (mul e0 z) e1 (g', ⟨Cpsa2Lean.Lib.RBMap.insert x1 (.F .Exp [.I x2, .G z]) s⟩)
      | .I x, .F .Genr [] =>
          if e0 == e1 then [(g, ⟨Cpsa2Lean.Lib.RBMap.insert x (.F .Genr []) s⟩)]
          else [(g, ⟨Cpsa2Lean.Lib.RBMap.insert x (.F .Exp [.F .Genr [], .G (mul e1 (invert e0))]) s⟩)]
      | .F .Genr [], .I _ => unifyExp t0' e1 t0 e0 gs
      | _, _ => []

  /-- Unify two lists of terms pointwise.
      Mirrors `unifyTermLists`. -/
  private partial def unifyTermLists (u u' : List Term) (gs : GenSubst) : List GenSubst :=
    match u, u' with
    | [],      []       => [gs]
    | t :: us, t' :: us' => (unifyChase t t' gs).flatMap (fun gs' => unifyTermLists us us' gs')
    | _,       _        => []

  /-- Unify two group elements by solving their difference.
      Mirrors `unifyGroup`. -/
  private partial def unifyGroup (t0 t1 : Group) (gs : GenSubst) : List GenSubst :=
    let (g, ⟨s⟩) := gs
    let t := groupSubst s (mul t0 (invert t1))
    (matchGroup t Lean.RBMap.empty Lean.RBMap.empty g s).map
      (fun (_, g', s') => (g', ⟨s'⟩))
end

/-- The exported unifier: unify and apply `chaseMap` to normalise.
    Mirrors `unify :: Term -> Term -> GenSubst -> [GenSubst]`. -/
def unify (t t' : Term) (gs : GenSubst) : List GenSubst :=
  (unifyChase t t' gs).map (fun (g, s) => (g, chaseMap s))

-- ── Stage 4D part 2: Matching ─────────────────────────────────────────────────

/-- Decompose a base term into its base and exponent components.
    Mirrors `calcBase :: Term -> (Term, Group)`. -/
partial def calcBase : Term → Term × Group
  | .I x                                                  => (.I x, Lean.RBMap.empty)
  | .F .Genr _                                            => (.F .Genr [], Lean.RBMap.empty)
  | .F .Exp [.I x, .G e]                                 => (.I x, e)
  | .F .Exp [.F .Genr _, .G e]                            => (.F .Genr [], e)
  | .F .Exp [.F .Exp [b, .G e1], .G e2]                  => calcBase (.F .Exp [b, .G (mul e1 e2)])
  | .F .Base [.I x]                                       => (.F .Base [.I x], Lean.RBMap.empty)
  | .F .Base [.F .Genr _]                                 => (.F .Base [.F .Genr []], Lean.RBMap.empty)
  | .F .Base [.F .Exp [.I x, .G e]]                       => (.F .Base [.I x], e)
  | .F .Base [.F .Exp [.F .Genr _, .G e]]                 => (.F .Base [.F .Genr []], e)
  | .F .Base [.F .Exp [.F .Exp [b, .G e1], .G e2]]        => calcBase (.F .Base [.F .Exp [b, .G (mul e1 e2)]])
  | t                                                      => (t, Lean.RBMap.empty)

mutual
  /-- The internal matching workhorse.
      Mirrors `xmatch :: Term -> Term -> GenEnv -> [GenEnv]`. -/
  private partial def xmatch (t t' : Term) (ge : GenEnv) : List GenEnv :=
    let (g, e) := ge
    match t, t' with
    | .I x, _ =>
        match Cpsa2Lean.Lib.RBMap.lookup x e.map with
        | none    => [(g, { e with map := Cpsa2Lean.Lib.RBMap.insert x t' e.map })]
        | some t'' => if t' == t'' then [ge] else []
    | .C c, .C c'           => if c == c' then [ge] else []
    | .F .Base [t0], .F .Base [t1] => matchBase t0 t1 ge
    | .F .Bltk u, .F .Bltk u' =>
        (matchLists u u' ge ++ matchLists u u'.reverse ge).eraseDups
    | .F s u, .F s' u' =>
        if s == s' then matchLists u u' ge else []
    | .F (.Invk op) [t0], _ => xmatch t0 (.F (.Invk op) [t']) ge
    | .G tg, .G tg' =>
        (matchGroup tg tg' e.vars g e.map).map
          (fun (v', g', r') => (g', { vars := v', map := r' }))
    | .D x, _ =>
        match Cpsa2Lean.Lib.RBMap.lookup x e.map with
        | none    => [(g, { e with map := Cpsa2Lean.Lib.RBMap.insert x t' e.map })]
        | some t'' => if t' == t'' then [ge] else []
    | .Z p, .Z p'           => if p == p' then [ge] else []
    | .X x, _ =>
        match Cpsa2Lean.Lib.RBMap.lookup x e.map with
        | none    => [(g, { e with map := Cpsa2Lean.Lib.RBMap.insert x t' e.map })]
        | some t'' => if t' == t'' then [ge] else []
    | .Y p, .Y p'           => if p == p' then [ge] else []
    | _, _                  => []

  /-- Match two base-sort terms.
      Mirrors `matchBase`. -/
  private partial def matchBase (t0 t1 : Term) (ge : GenEnv) : List GenEnv :=
    match t0, t1 with
    | .F .Exp [b0, .G e0], .F .Exp [b1, .G e1]  => matchExp b0 e0 b1 e1 ge
    | .F .Exp [b0, .G e0], .I x                 => matchExp b0 e0 (.I x) Lean.RBMap.empty ge
    | .F .Exp [b0, .G e0], .F .Genr []          => matchExp b0 e0 (.F .Genr []) Lean.RBMap.empty ge
    | .I x, .F .Exp [b1, .G e1]                 => matchExp (.I x) Lean.RBMap.empty b1 e1 ge
    | .I x, .I y                                => xmatch (.I x) (.I y) ge
    | .I x, .F .Genr []                         => matchExp (.I x) Lean.RBMap.empty (.F .Genr []) Lean.RBMap.empty ge
    | _, _                                      => xmatch t0 t1 ge

  /-- Match two exponential forms.
      Mirrors `matchExp`. -/
  private partial def matchExp (t0 : Term) (e0 : Group) (t0' : Term) (e1 : Group)
      (ge : GenEnv) : List GenEnv :=
    let (g, e) := ge
    match t0, t0' with
    | .F .Exp _, _ => assertError "Algebra.matchExp: non-canonical form"
    | _, .F .Exp _ => assertError "Algebra.matchExp: non-canonical form"
    | .I x, _ =>
        match Cpsa2Lean.Lib.RBMap.lookup x e.map with
        | some t =>
            if (calcBase t0').1 == (calcBase t).1 then
              xmatch (.G e0)
                (.G (mul e1 (mul (calcBase t0').2 (invert (calcBase t).2)))) ge
            else []
        | none =>
            let (g', wid) := freshId g "w"
            let w := groupVarGroup wid
            matchLists [.I x, .G e0]
              [.F .Exp [t0', .G w], .G (mul e1 (invert w))]
              (g', { e with vars := Cpsa2Lean.Lib.RBSet.insert wid e.vars })
    | .F .Genr [], _ =>
        matchLists [.F .Genr [], .G e0] [t0', .G e1] ge
    | _, _ => assertError "Algebra.matchExp: Bad match term"

  /-- Match two lists of terms pointwise.
      Mirrors `matchLists`. -/
  private partial def matchLists (u u' : List Term) (ge : GenEnv) : List GenEnv :=
    match u, u' with
    | [],      []        => [ge]
    | t :: us, t' :: us' => (xmatch t t' ge).flatMap (fun ge' => matchLists us us' ge')
    | _,       _         => []
end

/-- The exported matcher.
    Mirrors `match :: Term -> Term -> GenEnv -> [GenEnv]`
    (renamed `termMatch` because `match` is a Lean keyword). -/
def termMatch (t t' : Term) (ge : GenEnv) : List GenEnv :=
  xmatch t t' ge

-- ── Stage 4D part 3: Match-dependent operations ───────────────────────────────

/-- If `subst t` can be matched back to `t`, return `subst t`.
    Mirrors `substInvertibly :: Gen -> Subst -> Term -> Maybe Term`. -/
def substInvertibly (gen : Gen) (subst : Subst) (t : Term) : Option Term :=
  let ts := substitute subst t
  if (termMatch ts t (gen, emptyEnv)).isEmpty then none else some ts

/-- True when `substInvertibly` succeeds.
    Mirrors `substInvertibleOn`. -/
def substInvertibleOn (gen : Gen) (subst : Subst) (t : Term) : Bool :=
  (substInvertibly gen subst t).isSome

/-- Extend `gs` to satisfy an absence assertion `(v, t)`.
    Mirrors `absentEnv :: GenEnv -> (Term, Term) -> [GenEnv]`. -/
def absentEnv (gs : GenEnv) (pair : Term × Term) : List GenEnv :=
  match pair with
  | (.G v, .G t) =>
      if isGroupVar v then
        match separateVar (getGroupVar v) t with
        | none         => [gs]
        | some (_, t') => termMatch (.G t) (.G t') gs
      else assertError "Algebra.absentEnv: Bad absent pair"
  | _ => assertError "Algebra.absentEnv: Bad absent pair"

/-- True when every value in the range of `env` is a variable.
    Mirrors `matchRangeIsVars`. -/
def matchRangeIsVars (ge : GenEnv) : Bool :=
  Cpsa2Lean.Lib.RBMap.foldr (fun v acc => acc && isVar v) true ge.2.map

/-- Match `t` against `t'` and check that the range consists of variables
    in both directions.
    Mirrors `matchRename`. -/
def matchRename (t t' : Term) (ge : GenEnv) : List GenEnv :=
  match (termMatch t t' ge).filter matchRangeIsVars with
  | []    => []
  | cands =>
      match (termMatch t' t ge).filter matchRangeIsVars with
      | [] => []
      | _  => cands

/-- Clone all variables in `vs` and return new gen, an env mapping each
    old var to its clone, and the list of clones.
    Mirrors `renamerAndNewVars :: [Term] -> Gen -> (Gen, Env, [Term])`. -/
partial def renamerAndNewVars (vs : List Term) (g : Gen) : Gen × Env × List Term :=
  let rec iter (vs : List Term) (g : Gen) (e : Env) (acc : List Term) : Gen × Env × List Term :=
    match vs with
    | [] => (g, e, acc)
    | v :: rest =>
        match termMatch v v (g, e) with
        | [] => assertError "Algebra.renamerAndNewVars: repeated variable"
        | _  =>
            let (g', v') := clone g v
            match termMatch v v' (g', e) with
            | (g'', e') :: _ => iter rest g'' e' (v' :: acc)
            | []              => assertError "Algebra.renamerAndNewVars: clone failed"
  iter vs g emptyEnv []

/-- Add sort information to each binding in `env` using `domain`.
    Mirrors `reify :: [Term] -> Env -> [(Term, Term)]`. -/
partial def reify (domain : List Term) (e : Env) : List (Term × Term) :=
  let rec findSortedVar (dom : List Term) (y : Id) (t : Term) : Term × Term :=
    match dom with
    | [] => assertError "Algebra.reify: variable missing from domain"
    | .I x :: rest =>
        if x == y then (.I x, t) else findSortedVar rest y t
    | .F op@(.Data _) [.I x] :: rest =>
        if x == y then (.F op [.I x], .F op [t]) else findSortedVar rest y t
    | .F op@(.Akey _) [.I x] :: rest =>
        if x == y then (.F op [.I x], .F op [t]) else findSortedVar rest y t
    | .F .Name [.I x] :: rest =>
        if x == y then (.F .Name [.I x], .F .Name [t]) else findSortedVar rest y t
    | .F .Pval [.I x] :: rest =>
        if x == y then (.F .Pval [.I x], .F .Pval [t]) else findSortedVar rest y t
    | .F .Chan [.I x] :: rest =>
        if x == y then (.F .Chan [.I x], .F .Chan [t]) else findSortedVar rest y t
    | .F .Locn [.I x] :: rest =>
        if x == y then (.F .Locn [.I x], .F .Locn [t]) else findSortedVar rest y t
    | .F .Base [.I x] :: rest =>
        if x == y then (.F .Base [.I x], .F .Base [t]) else findSortedVar rest y t
    | .G grp :: rest =>
        if isGroupVar grp && varId (.G grp) == y then
          (.G grp, .G (match t with | .G g => g | _ => Lean.RBMap.empty))
        else findSortedVar rest y t
    | .D x :: rest =>
        if x == y then (.D x, t) else findSortedVar rest y t
    | .X x :: rest =>
        if x == y then (.X x, t) else findSortedVar rest y t
    | _ :: rest => findSortedVar rest y t
  Cpsa2Lean.Lib.RBMap.assocs e.map |>.map (fun (y, t) => findSortedVar domain y t)

-- ── Stage 4D: Strand / index helpers ─────────────────────────────────────────

def strdMatch (t : Term) (p : Int) (ge : GenEnv) : List GenEnv :=
  termMatch t (.Z p) ge

def strdLookup (e : Env) (t : Term) : Option Int :=
  match instantiate e t with
  | .Z p => some p
  | _    => none

def strdUpdate (e : Env) (f : Int → Int) : Env :=
  let m := Cpsa2Lean.Lib.RBMap.map (fun t => match t with | .Z z => .Z (f z) | t => t) e.map
  { e with map := m }

def indxMatch (t : Term) (p : Int) (ge : GenEnv) : List GenEnv :=
  termMatch t (.Y p) ge

def indxLookup (e : Env) (t : Term) : Option Int :=
  match instantiate e t with
  | .Y p => some p
  | _    => none

def indxUpdate (e : Env) (f : Int → Int) : Env :=
  let m := Cpsa2Lean.Lib.RBMap.map (fun t => match t with | .Y z => .Y (f z) | t => t) e.map
  { e with map := m }

def indxOfInt (i : Int) : Term := .Y i
def strdOfInt (i : Int) : Term := .Z i

-- ── Stage 4E: Term loading ────────────────────────────────────────────────────

open Cpsa2Lean.Signature (Operator)

instance : ToString Id where toString x := x.name

/-- Look up a variable by name in a list of terms, returning the term or an
    error message.
    Mirrors `loadLookup :: Pos -> [Term] -> String -> Either String Term`. -/
def loadLookup (pos : Pos) (vars : List Term) (name : String) : Except String Term :=
  match vars.find? (fun t => idName (varId t) == name) with
  | some t => .ok t
  | none   => .error s!"{pos}Identifier {name} unknown"

/-- Like `loadLookup` but rejects bare exponent (non-rndx group) variables.
    Mirrors `loadLookupStrict`. -/
def loadLookupStrict (pos : Pos) (vars : List Term) (name : String) : Except String Term := do
  let t ← loadLookup pos vars name
  if isExpr t && !isRndx t then
    .error s!"{pos}Identifier {name} is an expt--must be a rndx"
  else .ok t

/-- Look up `name` and require it to be a `name`-sorted term.
    Mirrors `loadLookupName`. -/
def loadLookupName (pos : Pos) (vars : List Term) (name : String) : Except String Term := do
  let t ← loadLookup pos vars name
  match t with
  | .F .Name [.I _] => .ok t
  | _ => .error s!"{pos}Expecting {name} to be a name"

/-- Look up `name` and require it to be an akey-sorted term.
    Returns `(op, term)`.
    Mirrors `loadLookupAkey`. -/
def loadLookupAkey (pos : Pos) (vars : List Term) (name : String)
    : Except String (String × Term) := do
  let t ← loadLookup pos vars name
  match t with
  | .F (.Akey op) [.I _] => .ok (op, t)
  | _ => .error s!"{pos}Expecting {name} to be an akey"

/-- True when `t` is an akey that is not an invk.
    Mirrors `isAkeyNotInvk`. -/
def isAkeyNotInvk : Term → Bool
  | .F (.Akey _) [.F (.Invk _) _] => false
  | .F (.Akey _) _                 => true
  | _                              => false

/-- Create a variable term from a sort name and fresh `Id`.
    Mirrors `mkVar :: MonadFail m => Sig -> Pos -> String -> Id -> m Term`.
    `variablesOfSortBase` is hardcoded `false` (deprecated in CPSA 4.4.8). -/
def mkVar (sig : Sig) (pos : Pos) (sort : String) (x : Id) : Except String Term :=
  if sort == "name"  then .ok (.F .Name [.I x])
  else if sort == "pval"  then .ok (.F .Pval [.I x])
  else if sort == "chan"  then .ok (.F .Chan [.I x])
  else if sort == "locn"  then .ok (.F .Locn [.I x])
  else if sort == "base"  then .error s!"{pos}mkVar:  Variables of sort base are now deprecated {x}"
  else if sort == "expt"  then .ok (groupVar .Expt x)
  else if sort == "rndx"  then .ok (groupVar .Rndx x)
  else if sort == "mesg"  then .ok (.I x)
  else if sort == "strd"  then .ok (.D x)
  else if sort == "indx"  then .ok (.X x)
  else if sig.akeys.contains sort then .ok (.F (.Akey sort) [.I x])
  else if sig.atoms.contains sort then .ok (.F (.Data sort) [.I x])
  else .error s!"{pos}Sort {sort} not recognized"

/-- Split a non-empty list into `(all-but-last, last)`.
    Mirrors `splitLast :: a -> [a] -> ([a], a)`. -/
def splitLast {α : Type} (x : α) (xs : List α) : List α × α :=
  let rec loop (z : List α) (cur : α) : List α → List α × α
    | []      => (z.reverse, cur)
    | y :: ys => loop (cur :: z) y ys
  loop [] x xs

/-- Parse a `(v₁ v₂ … sort)` declaration into a list of `(var-sexpr, sort-sexpr)` pairs.
    Mirrors `loadVarPair`. -/
def loadVarPair (s : SExpr Pos) : Except String (List (SExpr Pos × SExpr Pos)) :=
  match s with
  | .lst _ (x :: y :: rest) =>
      match (x :: y :: rest).reverse with
      | t :: vs => .ok (vs.reverse.map (fun v => (v, t)))
      | []      => .error "Algebra.loadVarPair: impossible"
  | x => .error s!"{x.annotation}Malformed vars declaration"

/-- Fold one `(var-sexpr, sort-sexpr)` pair into the accumulator.
    Mirrors `loadVar`. -/
def loadOneVar (sig : Sig) (acc : Gen × List Term) (p : SExpr Pos × SExpr Pos)
    : Except String (Gen × List Term) :=
  let (gen, vars) := acc
  match p with
  | (.sym pos name, .sym pos' sort) =>
      match loadLookup pos vars name with
      | .ok _ => .error s!"{pos}Duplicate variable declaration for {name}"
      | .error _ =>
          let (gen', x) := freshId gen name
          do let t ← mkVar sig pos' sort x
             .ok (gen', t :: vars)
  | (x, _) => .error s!"{x.annotation}Bad variable syntax"

/-- Parse a list of variable declarations and return `(gen, vars)`.
    Mirrors `loadVars :: MonadFail m => Sig -> Gen -> [SExpr Pos] -> m (Gen, [Term])`. -/
def loadVars (sig : Sig) (gen : Gen) (sexprs : List (SExpr Pos))
    : Except String (Gen × List Term) := do
  let pairs ← sexprs.mapM loadVarPair
  let (g, vars) ← pairs.flatten.foldlM (loadOneVar sig) (gen, [])
  .ok (g, vars.reverse)

set_option linter.unusedVariables false in
mutual
  /-- Load a term from an S-expression.
      `strict` forbids bare exponent variables (use `rndx` instead).
      Mirrors `loadTerm`. -/
  private partial def loadTermImpl (sig : Sig) (vars : List Term) (strict : Bool)
      : SExpr Pos → Except String Term
    | .sym pos s =>
        if strict then loadLookupStrict pos vars s
        else loadLookup pos vars s
    | .str _ t => .ok (.C t)
    | .lst _ [.sym _ "idx", .num _ i] => .ok (.Y i)
    | .lst pos (.sym _ s :: l) =>
        if      s == "pubk"  then loadPubk  sig pos vars strict l
        else if s == "privk" then loadPrivk sig pos vars strict l
        else if s == "invk"  then loadInvk  sig pos vars strict l
        else if s == "ltk"   then loadLtk   sig pos vars strict l
        else if s == "bltk"  then loadBltk  sig pos vars strict l
        else if s == "gen"   then loadGen   sig pos vars strict l
        else if s == "exp"   then loadExp   sig pos vars strict l
        else if s == "one"   then loadOne   sig pos vars strict l
        else if s == "rec"   then loadRec   sig pos vars strict l
        else if s == "mul"   then loadMul   sig pos vars strict l
        else if s == "cat"   then loadCat   sig pos vars strict l
        else match Cpsa2Lean.Signature.findOper s sig.opers with
          | none    => .error s!"{pos}Keyword {s} unknown"
          | some op => loadOperImpl sig pos vars strict op l
    | x => .error s!"{x.annotation}Malformed term"

  /-- Load a base-sort term (strips `(base ...)` if needed).
      Mirrors `loadBase`. -/
  private partial def loadBaseImpl (sig : Sig) (vars : List Term) (x : SExpr Pos)
      : Except String Term := do
    let t ← loadTermImpl sig vars false x
    match t with
    | .F .Base [b] => .ok b
    | _ => .error s!"{x.annotation}Malformed base"

  /-- Load a group/exponent from an S-expression.
      Mirrors `loadExpr`. -/
  private partial def loadExprImpl (sig : Sig) (vars : List Term) (strict : Bool)
      (x : SExpr Pos) : Except String Group := do
    let t ← loadTermImpl sig vars false x
    match t with
    | .G g => .ok g
    | _    => .error s!"{x.annotation}Malformed exponent"

  /-- Handle `(pubk name)` and `(pubk "const" name)`. -/
  private partial def loadPubk (sig : Sig) (pos : Pos) (vars : List Term) (strict : Bool)
      (l : List (SExpr Pos)) : Except String Term :=
    match l with
    | [.sym pos' s] => do
        let t ← loadLookupName pos' vars s
        .ok (.F (.Akey "akey") [.F .Pubk [.I (varId t)]])
    | [.str _ c, .sym pos' s] => do
        let t ← loadLookupName pos' vars s
        .ok (.F (.Akey "akey") [.F .Pubk [.C c, .I (varId t)]])
    | _ => .error s!"{pos}Malformed pubk"

  /-- Handle `(privk name)` and `(privk "const" name)`. -/
  private partial def loadPrivk (sig : Sig) (pos : Pos) (vars : List Term) (strict : Bool)
      (l : List (SExpr Pos)) : Except String Term :=
    match l with
    | [.sym pos' s] => do
        let t ← loadLookupName pos' vars s
        .ok (.F (.Akey "akey") [.F (.Invk "akey") [.F .Pubk [.I (varId t)]]])
    | [.str _ c, .sym pos' s] => do
        let t ← loadLookupName pos' vars s
        .ok (.F (.Akey "akey") [.F (.Invk "akey") [.F .Pubk [.C c, .I (varId t)]]])
    | _ => .error s!"{pos}Malformed privk"

  /-- Handle `(invk ...)` in its many forms. -/
  private partial def loadInvk (sig : Sig) (pos : Pos) (vars : List Term) (strict : Bool)
      (l : List (SExpr Pos)) : Except String Term :=
    match l with
    | [.sym pos' s] => do
        let (op, t) ← loadLookupAkey pos' vars s
        .ok (.F (.Akey op) [.F (.Invk op) [.I (varId t)]])
    | [.lst _ [.sym _ "pubk", .sym pos' s]] => do
        let t ← loadLookupName pos' vars s
        .ok (.F (.Akey "akey") [.F (.Invk "akey") [.F .Pubk [.I (varId t)]]])
    | [.lst _ [.sym _ "pubk", .str _ c, .sym pos' s]] => do
        let t ← loadLookupName pos' vars s
        .ok (.F (.Akey "akey") [.F (.Invk "akey") [.F .Pubk [.C c, .I (varId t)]]])
    | [.lst _ [.sym _ "privk", .sym pos' s]] => do
        let t ← loadLookupName pos' vars s
        .ok (.F (.Akey "akey") [.F .Pubk [.I (varId t)]])
    | [.lst _ [.sym _ "privk", .str _ c, .sym pos' s]] => do
        let t ← loadLookupName pos' vars s
        .ok (.F (.Akey "akey") [.F .Pubk [.C c, .I (varId t)]])
    | [.lst _ [.sym _ "invk", inner]] => do
        let a ← loadTermImpl sig vars strict inner
        match a with
        | .F (.Akey _) _ => .ok a
        | _ => .error s!"{inner.annotation}Expecting an akey"
    | _ => .error s!"{pos}Malformed invk"

  /-- Handle `(ltk name name)`. -/
  private partial def loadLtk (sig : Sig) (pos : Pos) (vars : List Term) (strict : Bool)
      (l : List (SExpr Pos)) : Except String Term :=
    match l with
    | [.sym pos' s, .sym pos'' s'] => do
        let t  ← loadLookupName pos' vars s
        let t' ← loadLookupName pos'' vars s'
        .ok (.F (.Data "skey") [.F .Ltk [.I (varId t), .I (varId t')]])
    | _ => .error s!"{pos}Malformed ltk"

  /-- Handle `(bltk name name)`. -/
  private partial def loadBltk (sig : Sig) (pos : Pos) (vars : List Term) (strict : Bool)
      (l : List (SExpr Pos)) : Except String Term :=
    match l with
    | [.sym pos' s, .sym pos'' s'] => do
        let t  ← loadLookupName pos' vars s
        let t' ← loadLookupName pos'' vars s'
        .ok (.F (.Data "skey") [.F .Bltk [.I (varId t), .I (varId t')]])
    | _ => .error s!"{pos}Malformed bltk"

  /-- Handle `(gen)`. -/
  private partial def loadGen (sig : Sig) (pos : Pos) (vars : List Term) (strict : Bool)
      (l : List (SExpr Pos)) : Except String Term :=
    match l with
    | [] => .ok (.F .Base [.F .Genr []])
    | _  => .error s!"{pos}Malformed gen"

  /-- Handle `(exp base expt)`. -/
  private partial def loadExp (sig : Sig) (pos : Pos) (vars : List Term) (strict : Bool)
      (l : List (SExpr Pos)) : Except String Term :=
    match l with
    | [x, x'] => do
        let t  ← loadBaseImpl sig vars x
        let t' ← loadExprImpl sig vars false x'
        .ok (.F .Base [idSubst emptyIdMap (.F .Exp [t, .G t'])])
    | _ => .error s!"{pos}Malformed exponentiation"

  /-- Handle `(one)` — the identity element of the group. -/
  private partial def loadOne (sig : Sig) (pos : Pos) (vars : List Term) (strict : Bool)
      (l : List (SExpr Pos)) : Except String Term :=
    if strict then .error s!"{pos}Disallowed bare exponent"
    else match l with
    | [] => .ok (.G Lean.RBMap.empty)
    | _  => .error s!"{pos}Malformed one"

  /-- Handle `(rec expt)` — group inverse. -/
  private partial def loadRec (sig : Sig) (pos : Pos) (vars : List Term) (strict : Bool)
      (l : List (SExpr Pos)) : Except String Term :=
    if strict then .error s!"{pos}Disallowed bare exponent"
    else match l with
    | [x] => do
        let t ← loadExprImpl sig vars false x
        .ok (.G (invert t))
    | _ => .error s!"{pos}Malformed rec"

  /-- Handle `(mul expt₁ expt₂ …)` — group product. -/
  private partial def loadMul (sig : Sig) (pos : Pos) (vars : List Term) (strict : Bool)
      (l : List (SExpr Pos)) : Except String Term :=
    if strict then .error s!"{pos}Disallowed bare exponent"
    else do
      let ts ← l.mapM (loadExprImpl sig vars false)
      .ok (.G (ts.foldl (fun acc t => mul t acc) Lean.RBMap.empty))

  /-- Handle `(cat t₁ t₂ …)` — right-associated tuple. -/
  private partial def loadCat (sig : Sig) (pos : Pos) (vars : List Term) (strict : Bool)
      (l : List (SExpr Pos)) : Except String Term :=
    match l with
    | [] => .error s!"{pos}Malformed cat"
    | _  => do
        let ts ← l.mapM (loadTermImpl sig vars strict)
        .ok (match ts.reverse with
               | [] => .C ""
               | last :: rest => rest.foldl (fun acc x => .F (.Tupl "cat") [x, acc]) last)

  /-- Load a custom operator application.
      Mirrors `loadOper`. -/
  private partial def loadOperImpl (sig : Sig) (pos : Pos) (vars : List Term) (strict : Bool)
      (op : Operator) (l : List (SExpr Pos)) : Except String Term :=
    match op with
    | .enc sym =>
        match l with
        | fst :: snd :: rest =>
            let (butLast, last) := splitLast fst (snd :: rest)
            do let t  ← loadCat sig pos vars strict butLast
               let t' ← loadTermImpl sig vars false last
               .ok (.F (.Enc sym) [t, t'])
        | _ => .error s!"{pos}Malformed enc"
    | .senc sym =>
        match l with
        | fst :: snd :: rest =>
            let (butLast, last) := splitLast fst (snd :: rest)
            do let t  ← loadCat sig pos vars strict butLast
               let t' ← loadTermImpl sig vars false last
               match t' with
               | .F (.Akey _) _ => .error s!"{pos}Expecting a symmetric key"
               | _ => .ok (.F (.Enc sym) [t, t'])
        | _ => .error s!"{pos}Malformed senc"
    | .aenc sym =>
        match l with
        | fst :: snd :: rest =>
            let (butLast, last) := splitLast fst (snd :: rest)
            do let t  ← loadCat sig pos vars strict butLast
               let t' ← loadTermImpl sig vars false last
               if isAkeyNotInvk t' then .ok (.F (.Enc sym) [t, t'])
               else .error s!"{pos}Expecting an asymmetric key"
        | _ => .error s!"{pos}Malformed aenc"
    | .sign sym =>
        match l with
        | fst :: snd :: rest =>
            let (butLast, last) := splitLast fst (snd :: rest)
            do let t  ← loadCat sig pos vars strict butLast
               let t' ← loadTermImpl sig vars false last
               match t' with
               | .F (.Akey _) [.F (.Invk _) _] => .ok (.F (.Enc sym) [t, t'])
               | _ => .error s!"{pos}Expecting an asymmetric inverse key"
        | _ => .error s!"{pos}Malformed sign"
    | .hash sym =>
        match l with
        | _ :: _ =>
            do let ts ← l.mapM (loadTermImpl sig vars false)
               .ok (.F (.Hash sym) [match ts.reverse with
               | [] => .C ""
               | last :: rest => rest.foldl (fun acc x => .F (.Tupl "cat") [x, acc]) last])
        | _ => .error s!"{pos}Malformed hash"
    | .tupl sym arity =>
        if l.length == arity then do
          let ts ← l.mapM (loadTermImpl sig vars strict)
          .ok (.F (.Tupl sym) ts)
        else .error s!"{pos}Bad tuple length {sym} should be {arity}"

end

/-- Public entry point for loading a term.
    Mirrors `loadTerm :: MonadFail m => Sig -> [Term] -> Bool -> SExpr Pos -> m Term`. -/
def loadTerm (sig : Sig) (vars : List Term) (strict : Bool) (x : SExpr Pos) : Except String Term :=
  loadTermImpl sig vars strict x

/-- Public entry point for loading a base-sort term. -/
def loadBase (sig : Sig) (vars : List Term) (x : SExpr Pos) : Except String Term :=
  loadBaseImpl sig vars x

-- ── Stage 4F: Display ─────────────────────────────────────────────────────────

/-- Strip any trailing `-N` numeric suffix to get the root name.
    Mirrors `rootName :: String -> String`. -/
def rootName (name : String) : String :=
  let cs := name.toList
  let rec findHyphen (i : Nat) : List Char → Option Nat
    | []       => none
    | c :: rest =>
        if c == '-' then
          let suffix := rest
          if suffix.all (fun ch => ch.isDigit) && !suffix.isEmpty then some i
          else findHyphen (i + 1) rest
        else findHyphen (i + 1) rest
  match findHyphen 0 cs with
  | none   => name
  | some i => String.mk (cs.take i)

/-- True when the context already contains a binding for `x`. -/
def hasId (ctx : Context) (x : Id) : Bool :=
  ctx.pairs.any (fun (y, _) => y == x)

/-- True when the context already contains a binding with display name `name`. -/
def hasName (ctx : Context) (name : String) : Bool :=
  ctx.pairs.any (fun (_, n) => n == name)

/-- Add a `(x, name)` binding to a context. -/
def extendContext (ctx : Context) (x : Id) (name : String) : Context :=
  ⟨(x, name) :: ctx.pairs⟩

/-- Generate a fresh display name by appending `-N` where N is the first
    non-conflicting index, given that `name` already exists.
    Mirrors `genName :: Context -> String -> String`. -/
partial def genCtxName (ctx : Context) (name : String) : String :=
  let rec loop (n : Nat) : String :=
    let candidate := name ++ "-" ++ toString n
    if hasName ctx candidate then loop (n + 1) else candidate
  loop 0

/-- Add a variable to a context, using `rootName` as the preferred display name
    and generating a fresh suffix when needed.
    Mirrors `varContext :: Context -> Term -> Context`. -/
def varContext (ctx : Context) (t : Term) : Context :=
  let x := varId t
  let name := rootName (idName x)
  if hasId ctx x then ctx
  else if hasName ctx name then extendContext ctx x (genCtxName ctx name)
  else extendContext ctx x name

/-- Extend a context with all variables that appear in the list of terms.
    Mirrors `addToContext :: Context -> [Term] -> Context`. -/
def addToContext (ctx : Context) (ts : List Term) : Context :=
  ts.foldl (foldVars varContext) ctx

/-- Wrap a non-sorted term in its inferred sort wrapper.
    Mirrors `inferSort :: Term -> Term`. -/
def inferSort : Term → Term
  | t@(.F (.Invk _) _)  => .F (.Akey "akey") [t]
  | t@(.F .Pubk _)      => .F (.Akey "akey") [t]
  | t@(.F .Ltk _)       => .F (.Data "skey") [t]
  | t@(.F .Bltk _)      => .F (.Data "skey") [t]
  | t@(.F .Genr _)      => .F .Base [t]
  | t@(.F .Exp _)       => .F .Base [t]
  | t                   => t

/-- Display an `Id` as its context-assigned name.
    Panics if the id is not in the context.
    Mirrors `displayId :: Context -> Id -> SExpr ()`. -/
def displayId (ctx : Context) (x : Id) : SExpr Unit :=
  match ctx.pairs.find? (fun (y, _) => y == x) with
  | some (_, name) => .sym () name
  | none           =>
      assertError s!"Algebra.displayId: Cannot find variable {x.name} in display context"

/-- Display an `Id` with its sort as a pair `(SExpr, SExpr)`.
    Mirrors `displaySortId`. -/
def displaySortId (sort : String) (ctx : Context) (x : Id) : SExpr Unit × SExpr Unit :=
  (displayId ctx x, .sym () sort)

/-- Display a variable term together with its sort.
    Mirrors `displayVar :: Context -> Term -> (SExpr (), SExpr ())`. -/
def displayVar (ctx : Context) : Term → SExpr Unit × SExpr Unit
  | .I x                  => displaySortId "mesg" ctx x
  | .F (.Data sort) [.I x] => displaySortId sort ctx x
  | .F (.Akey sort) [.I x] => displaySortId sort ctx x
  | .F .Name [.I x]       => displaySortId "name" ctx x
  | .F .Pval [.I x]       => displaySortId "pval" ctx x
  | .F .Chan [.I x]       => displaySortId "chan" ctx x
  | .F .Locn [.I x]       => displaySortId "locn" ctx x
  | .F .Base [.I x]       => displaySortId "base" ctx x
  | t@(.G grp) =>
      if isBasisVar grp then displaySortId "rndx" ctx (varId t)
      else displaySortId "expt" ctx (varId t)
  | .D x => displaySortId "strd" ctx x
  | .X x => displaySortId "indx" ctx x
  | _    => assertError "Algebra.displayVar: term not a variable with its sort"

mutual
  /-- Flatten a right-associated `cat` into a display list.
      Mirrors `displayList :: Context -> Term -> [SExpr ()]`. -/
  partial def displayList (ctx : Context) : Term → List (SExpr Unit)
    | .F (.Tupl "cat") [t0, t1] => displayTerm ctx t0 :: displayList ctx t1
    | t => [displayTerm ctx t]

  /-- Flatten the enc/sign arguments: split the ciphertext into a flat sequence.
      Mirrors `displayEnc :: Context -> Term -> Term -> [SExpr ()]`. -/
  partial def displayEnc (ctx : Context) : Term → Term → List (SExpr Unit)
    | .F (.Tupl "cat") [t0, t1], t => displayTerm ctx t0 :: displayEnc ctx t1 t
    | t0, t1 => [displayTerm ctx t0, displayTerm ctx t1]

  /-- Display a `Term` as a unit-annotated S-expression.
      Mirrors `displayTerm :: Context -> Term -> SExpr ()`. -/
  partial def displayTerm (ctx : Context) : Term → SExpr Unit
  | .I x => displayId ctx x
  | .F (.Data _) [.I x] => displayId ctx x
  | .F (.Data _) [.F .Ltk [.I x, .I y]] =>
      .lst () [.sym () "ltk", displayId ctx x, displayId ctx y]
  | .F op@(.Data _) [.F .Bltk [.I x, .I y]] =>
      if x.num > y.num then displayTerm ctx (.F op [.F .Bltk [.I y, .I x]])
      else .lst () [.sym () "bltk", displayId ctx x, displayId ctx y]
  | .F (.Akey _) [t] =>
      match t with
      | .I x                         => displayId ctx x
      | .F (.Invk _) [.I x]          => .lst () [.sym () "invk", displayId ctx x]
      | .F .Pubk [.I x]              => .lst () [.sym () "pubk", displayId ctx x]
      | .F .Pubk [.C c, .I x]        => .lst () [.sym () "pubk", .str () c, displayId ctx x]
      | .F (.Invk _) [.F .Pubk [.I x]]        => .lst () [.sym () "privk", displayId ctx x]
      | .F (.Invk _) [.F .Pubk [.C c, .I x]]  => .lst () [.sym () "privk", .str () c, displayId ctx x]
      | _ => assertError "Algebra.displayAkey: Bad akey term"
  | .F .Name [.I x]  => displayId ctx x
  | .F .Pval [.I x]  => displayId ctx x
  | .F .Chan [.I x]  => displayId ctx x
  | .F .Locn [.I x]  => displayId ctx x
  | .F .Base [t] =>
      let rec displayBase : Term → SExpr Unit
        | .I x => displayId ctx x
        | .F .Genr [] => .lst () [.sym () "gen"]
        | .F .Exp [t0, .G t1] =>
            .lst () [.sym () "exp", displayBase t0, displayTerm ctx (.G t1)]
        | .G m => .lst () [.sym () "exp", displayTerm ctx (.G m)]
        | _ => assertError "Algebra.displayBase: Bad base term"
      displayBase t
  | .G t =>
      let displayFactor (x : Id) (d : Desc) : SExpr Unit :=
        if d.2 >= 0 then displayId ctx x
        else .lst () [.sym () "rec", displayId ctx x]
      let fs := factors t
      if fs.isEmpty then .lst () [.sym () "one"]
      else match fs with
      | [(x, d)] => displayFactor x d
      | _        => .lst () (.sym () "mul" :: fs.map (fun (x, d) => displayFactor x d))
  | .C t => .str () t
  | .F (.Tupl "cat") [t0, t1] =>
      .lst () (.sym () "cat" :: displayTerm ctx t0 :: displayList ctx t1)
  | .F (.Tupl op) ts =>
      .lst () (.sym () op :: ts.map (displayTerm ctx))
  | .F (.Enc op) [t0, t1] =>
      .lst () (.sym () op :: displayEnc ctx t0 t1)
  | .F (.Hash op) [t] =>
      .lst () (.sym () op :: displayList ctx t)
  | .D x => displayId ctx x
  | .Z z => .num () z
  | .X x => displayId ctx x
  | .Y z => .lst () [.sym () "idx", .num () z]
  | _ => assertError "Algebra.displayTerm: Bad term"
end

/-- Display all bindings of an environment as a list of `(lhs rhs)` pairs.
    Mirrors `displayEnv :: Context -> Context -> Env -> [SExpr ()]`. -/
def displayEnv (ctx ctx' : Context) (e : Env) : List (SExpr Unit) :=
  let bindings := Cpsa2Lean.Lib.RBMap.assocs e.map |>.map
    (fun (x, t) => (.I x, inferSort t))
  let ctx'' := addToContext ctx' (bindings.map Prod.snd)
  bindings.map (fun (lhs, rhs) =>
    .lst () [displayTerm ctx lhs, displayTerm ctx'' rhs])

-- ── Stage 5: Variable creation helpers ───────────────────────────────────────

/-- Like `mkVar` but returns `Term` directly (panic on unknown sort rather than
    `Except`), defaulting to `I x` for unrecognised sorts.
    Mirrors `mkVarUnfailingly :: Sig -> String -> Id -> Term`. -/
def mkVarUnfailingly (sig : Sig) (sort : String) (x : Id) : Term :=
  if sort == "name"  then .F .Name [.I x]
  else if sort == "pval"  then .F .Pval [.I x]
  else if sort == "chan"  then .F .Chan [.I x]
  else if sort == "locn"  then .F .Locn [.I x]
  else if sort == "base"  then
    assertError s!"mkVarUnfailingly: Variables of sort base are now deprecated {x}"
  else if sort == "expt"  then groupVar .Expt x
  else if sort == "rndx"  then groupVar .Rndx x
  else if sort == "mesg"  then .I x
  else if sort == "strd"  then .D x
  else if sort == "indx"  then .X x
  else if sig.akeys.contains sort then .F (.Akey sort) [.I x]
  else if sig.atoms.contains sort then .F (.Data sort) [.I x]
  else .I x  -- fallback: treat as mesg

/-- Allocate a fresh variable of the given name and sort under `sig`.
    Mirrors `newVar :: Sig -> Gen -> String -> String -> (Gen, Term)`. -/
def newVar (sig : Sig) (g : Gen) (varN varSort : String) : Gen × Term :=
  let (g', x) := freshId g varN
  (g', mkVarUnfailingly sig varSort x)

/-- `newVar` specialised to the default signature.
    Mirrors `newVarDefault :: Gen -> String -> String -> (Gen, Term)`. -/
def newVarDefault (g : Gen) (varN varSort : String) : Gen × Term :=
  newVar Cpsa2Lean.Signature.defaultSig g varN varSort

/-- The human-readable name of a variable term.
    Mirrors `varName :: Term -> String`. -/
def varName (t : Term) : String := idName (varId t)

/-- Build `(cat pt t)` to associate a location variable with a message.
    Mirrors `locnMesg :: Term -> Term -> Term`. -/
def locnMesg (pt t : Term) : Term := .F (.Tupl "cat") [pt, t]

/-- Load a location variable from two S-expressions (variable name and sort),
    returning `(gen', pt, cat pt t)`.
    Mirrors `loadLocnTerm`. -/
def loadLocnTerm (sig : Sig) (gen : Gen) (ptSexpr pvalSexpr : SExpr Pos) (t : Term)
    : Except String (Gen × Term × Term) := do
  let (gen', vars) ← loadOneVar sig (gen, []) (ptSexpr, pvalSexpr)
  match vars with
  | []       => .error s!"{ptSexpr.annotation}No variable generated by loadOneVar in loadLocnTerm"
  | pt :: _  => .ok (gen', pt, locnMesg pt t)

-- ── Stage 7: VarListSpec and display helpers ──────────────────────────────────

/-- Extract the sort name and variable name from a variable term.
    Mirrors `sortNameAndVarName :: Term -> (String, String)`. -/
def sortNameAndVarName : Term → String × String
  | .I x                   => ("mesg",  x.name)
  | .F (.Data sort) [.I x] => (sort,    x.name)
  | .F (.Akey sort) [.I x] => (sort,    x.name)
  | .F .Name [.I x]        => ("name",  x.name)
  | .F .Pval [.I x]        => ("pt",    x.name)
  | .F .Chan [.I x]        => ("chan",  x.name)
  | .F .Locn [.I x]        => ("locn",  x.name)
  | .F .Base [.I x]        => ("base",  x.name)
  | .D x                   => ("strd",  x.name)
  | .X x                   => ("indx",  x.name)
  | .G grp =>
      if isBasisVar grp then ("rndx", (getGroupVar grp).name)
      else if isExprVar grp then ("expt", (getGroupVar grp).name)
      else assertError s!"sortNameAndVarName: Non-var group member"
  | _ => assertError "sortNameAndVarName: Non-var term"

/-- Try to add `(sortName, varName)` to an existing sort group in a `VarListSpec`.
    Returns `none` if `sortName` is not already present.
    Mirrors `addSortNameToVarListSpec`. -/
def addSortNameToVarListSpec (sn vn : String) : VarListSpec → Option VarListSpec
  | []                     => none
  | (sn', vns) :: rest =>
      if sn == sn' then
        some ((sn, Cpsa2Lean.Lib.adjoin vn vns) :: rest)
      else
        addSortNameToVarListSpec sn vn rest |>.map (fun added => (sn', vns) :: added)

/-- Build a `VarListSpec` grouping variable terms by sort.
    Mirrors `varListSpecOfVars :: [Term] -> VarListSpec`. -/
def varListSpecOfVars : List Term → VarListSpec
  | []         => []
  | t :: rest  =>
      let (sn, vn) := sortNameAndVarName t
      let specRest := varListSpecOfVars rest
      match addSortNameToVarListSpec sn vn specRest with
      | none       => (sn, [vn]) :: specRest
      | some added => added

/-- True when `t` is NOT a pval variable.
    Mirrors `notPt :: Term -> Bool`. -/
def notPt : Term → Bool
  | .F .Pval [.I _] => false
  | _               => true

/-- Display a variable list grouped by sort as a list of `(v₁ v₂ … sort)` sexps.
    Mirrors `displayVars :: Context -> [Term] -> [SExpr ()]`. -/
partial def displayVars (ctx : Context) (vars : List Term) : List (SExpr Unit) :=
  match vars with
  | [] => []
  | _ =>
      let pairs := vars.map (displayVar ctx)
      match pairs with
      | [] => assertError "Algebra.displayVars: [] vars cannot happen"
      | (v, sort) :: rest =>
          let rec loop (curSort : SExpr Unit) (accRev : List (SExpr Unit))
              : List (SExpr Unit × SExpr Unit) → List (SExpr Unit)
            | [] => [.lst () (accRev.reverse ++ [curSort])]
            | (v', sort') :: xs =>
                if curSort == sort' then loop sort' (v' :: accRev) xs
                else .lst () (accRev.reverse ++ [curSort]) :: loop sort' [v'] xs
          loop sort [v] rest

/-- Like `displayTerm` but suppresses pval variables (shows `""` or skips them
    in cat chains).
    Mirrors `displayTermNoPt :: Context -> Term -> SExpr ()`. -/
partial def displayTermNoPt (ctx : Context) : Term → SExpr Unit
  | .I x => displayId ctx x
  | .F (.Data _) [.I x] => displayId ctx x
  | .F (.Data _) [.F .Ltk [.I x, .I y]] =>
      .lst () [.sym () "ltk", displayId ctx x, displayId ctx y]
  | .F op@(.Data _) [.F .Bltk [.I x, .I y]] =>
      if x.num > y.num then displayTermNoPt ctx (.F op [.F .Bltk [.I y, .I x]])
      else .lst () [.sym () "bltk", displayId ctx x, displayId ctx y]
  | .F (.Akey _) [t] =>
      match t with
      | .I x                                      => displayId ctx x
      | .F (.Invk _) [.I x]                       => .lst () [.sym () "invk", displayId ctx x]
      | .F .Pubk [.I x]                           => .lst () [.sym () "pubk", displayId ctx x]
      | .F .Pubk [.C c, .I x]                     => .lst () [.sym () "pubk", .str () c, displayId ctx x]
      | .F (.Invk _) [.F .Pubk [.I x]]            => .lst () [.sym () "privk", displayId ctx x]
      | .F (.Invk _) [.F .Pubk [.C c, .I x]]      => .lst () [.sym () "privk", .str () c, displayId ctx x]
      | _ => assertError "Algebra.displayTermNoPt: Bad akey term"
  | .F .Name [.I x]  => displayId ctx x
  | .F .Pval [.I _]  => .sym () ""
  | .F .Chan [.I x]  => displayId ctx x
  | .F .Locn [.I x]  => displayId ctx x
  | .F .Base [t] =>
      let rec displayBase : Term → SExpr Unit
        | .I x                  => displayId ctx x
        | .F .Genr []           => .lst () [.sym () "gen"]
        | .F .Exp [t0, .G t1]  =>
            .lst () [.sym () "exp", displayBase t0, displayTerm ctx (.G t1)]
        | _ => assertError "Algebra.displayTermNoPt: Bad base term"
      displayBase t
  | .G t =>
      let displayFactor (x : Id) (d : Desc) : SExpr Unit :=
        if d.2 >= 0 then displayId ctx x
        else .lst () [.sym () "rec", displayId ctx x]
      let fs := factors t
      if fs.isEmpty then .lst () [.sym () "one"]
      else match fs with
      | [(x, d)] => displayFactor x d
      | _        => .lst () (.sym () "mul" :: fs.map (fun (x, d) => displayFactor x d))
  | .C t => .str () t
  | .F (.Tupl "cat") [t0, t1] =>
      match t0 with
      | .F .Pval [.I _] => displayTermNoPt ctx t1
      | _ => .lst () (.sym () "cat" :: displayTermNoPt ctx t0 :: displayList ctx t1)
  | .F (.Tupl op) ts =>
      .lst () (.sym () op :: ts.map (displayTerm ctx))
  | .F (.Enc op) [t0, t1] =>
      .lst () (.sym () op :: displayEnc ctx t0 t1)
  | .F (.Hash op) [t] =>
      .lst () (.sym () op :: displayList ctx t)
  | .D x => displayId ctx x
  | .Z z => .num () z
  | .X x => displayId ctx x
  | .Y z => .num () z
  | _ => assertError "Algebra.displayTermNoPt: Bad term"

/-- Display env bindings, excluding any variable whose pval-wrapped form appears
    in `vars`.
    Mirrors `displayEnvSansPts :: [Term] -> Context -> Context -> Env -> [SExpr ()]`. -/
def displayEnvSansPts (vars : List Term) (ctx ctx' : Context) (e : Env) : List (SExpr Unit) :=
  let nonPt (t : Term) : Bool := !vars.contains (.F .Pval [t])
  let bindings :=
    Cpsa2Lean.Lib.RBMap.assocs (Cpsa2Lean.Lib.RBMap.filter nonPt e.map) |>.map
      (fun (x, t) => (.I x, inferSort t))
  let ctx'' := addToContext ctx' (bindings.map Prod.snd)
  bindings.map (fun (lhs, rhs) => .lst () [displayTerm ctx lhs, displayTerm ctx'' rhs])

/-- Display a substitution as a list of `(lhs rhs)` pairs.
    Mirrors `displaySubst :: Context -> Subst -> [SExpr ()]`. -/
def displaySubst (ctx : Context) (s : Subst) : List (SExpr Unit) :=
  let bindings :=
    Cpsa2Lean.Lib.RBMap.assocs s.map |>.map
      (fun (x, t) => (.I x, inferSort t))
  let ctx' := bindings.foldl (fun c (x, t) => addToContext c [x, t]) ctx
  bindings.map (fun (lhs, rhs) => .lst () [displayTerm ctx' lhs, displayTerm ctx' rhs])

end Cpsa2Lean.Algebra
