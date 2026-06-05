/-
LeanCPSA.Channel

Port of CPSA.Channel (MITRE cpsa v4.4.9).

Copyright (c) 2026 Paul D. Rowe

Channels and Channel Messages

Copyright (c) 2009 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.

Defines channel messages (`ChMsg`), channel-or-term values (`CMT`),
and the operations on them used throughout the CPSA bundle analysis.

A "channel" in CPSA is simply a variable of sort `chan`.  A channel
message is either a plain `Term` or a `(channel, payload)` pair.
-/

import LeanCPSA.Algebra

namespace LeanCPSA.Channel

open LeanCPSA.Algebra
open LeanCPSA.Lib (assertError)

-- ── ChType ────────────────────────────────────────────────────────────────────

/-- Discriminates channel messages from location messages.
    Mirrors `data ChType = Chan | Locn`. -/
inductive ChType where
  | Chan : ChType
  | Locn : ChType
  deriving Repr, BEq, Ord

-- ── ChMsg ─────────────────────────────────────────────────────────────────────

/-- A channel message: either a plain term or a (type, channel, payload) triple.
    Mirrors `data ChMsg = Plain Term | ChMsg ChType Term Term`. -/
inductive ChMsg where
  | Plain : Term → ChMsg
  | ChMsg : ChType → Term → Term → ChMsg
  deriving Repr, BEq, Ord

-- ── CMT ───────────────────────────────────────────────────────────────────────

/-- A channel message or an internal term.
    Mirrors `data CMT = TM Term | CM ChMsg`. -/
inductive CMT where
  | TM : Term  → CMT
  | CM : ChMsg → CMT
  deriving Repr, BEq, Ord

/- PDR: Probably what is derived above

instance : BEq CMT where
  beq
    | .TM t,  .TM t'  => t == t'
    | .CM cm, .CM cm' => cm == cm'
    | _,      _       => false

instance : Ord CMT where
  compare
    | .TM t,  .TM t'  => compare t t'
    | .TM _,  .CM _   => .lt
    | .CM _,  .TM _   => .gt
    | .CM cm, .CM cm' => compare cm cm' -/

-- ── ChMsg operations ──────────────────────────────────────────────────────────

/-- Extract the payload term from a channel message.
    Mirrors `cmTerm :: ChMsg -> Term`. -/
def cmTerm : ChMsg → Term
  | .Plain t       => t
  | .ChMsg _ _ t   => t

/-- Extract all terms (channel + payload, or just payload) as a list.
    Mirrors `cmTerms :: ChMsg -> [Term]`. -/
def cmTerms : ChMsg → List Term
  | .Plain t        => [t]
  | .ChMsg _ ch t   => [ch, t]

/-- Extract the channel component, if any.
    Mirrors `cmChan :: ChMsg -> Maybe Term`. -/
def cmChan : ChMsg → Option Term
  | .Plain _        => none
  | .ChMsg _ ch _   => some ch

/-- Apply `f` to the payload (and channel, if present).
    Mirrors `cmMap :: (Term -> Term) -> ChMsg -> ChMsg`. -/
def cmMap (f : Term → Term) : ChMsg → ChMsg
  | .Plain t        => .Plain (f t)
  | .ChMsg ct ch t  => .ChMsg ct (f ch) (f t)

/-- Match one channel message against another.  Messages of different
    `ChType` never match.
    Mirrors `cmMatch :: ChMsg -> ChMsg -> GenEnv -> [GenEnv]`. -/
def cmMatch : ChMsg → ChMsg → GenEnv → List GenEnv
  | .Plain t,         .Plain t',          ge => termMatch t t' ge
  | .ChMsg ct ch t,   .ChMsg ct' ch' t',  ge =>
      if ct != ct' then []
      else (termMatch ch ch' ge).flatMap (fun ge' => termMatch t t' ge')
  | _,                _,                  _  => []

/-- Match insisting on renamings of fresh variables.
    Mirrors `cmMatchRename :: ChMsg -> ChMsg -> GenEnv -> [GenEnv]`. -/
def cmMatchRename : ChMsg → ChMsg → GenEnv → List GenEnv
  | .Plain t,         .Plain t',          ge => matchRename t t' ge
  | .ChMsg ct ch t,   .ChMsg ct' ch' t',  ge =>
      if ct != ct' then []
      else (matchRename ch ch' ge).flatMap (fun ge' => matchRename t t' ge')
  | _,                _,                  _  => []

/-- Unify two channel messages.  Messages of different `ChType` never unify.
    Mirrors `cmUnify :: ChMsg -> ChMsg -> GenSubst -> [GenSubst]`. -/
def cmUnify : ChMsg → ChMsg → GenSubst → List GenSubst
  | .Plain t,         .Plain t',          gs => unify t t' gs
  | .ChMsg ct ch t,   .ChMsg ct' ch' t',  gs =>
      if ct != ct' then []
      else (unify ch ch' gs).flatMap (fun gs' => unify t t' gs')
  | _,                _,                  _  => []

/-- Apply a substitution to a channel message.
    Mirrors `cmSubstitute :: Subst -> ChMsg -> ChMsg`. -/
def cmSubstitute (subst : Subst) (cm : ChMsg) : ChMsg :=
  cmMap (substitute subst) cm

/-- Fold `f` over every carried subterm of a channel message,
    wrapping each in `CMT.TM`; for a `ChMsg` variant the whole message
    is also passed as `CMT.CM` before the fold.
    Mirrors `cmFoldCarriedTerms`. -/
def cmFoldCarriedTerms {α : Type} [Inhabited α]
    (f : α → CMT → α) (acc : α) (cm : ChMsg) : α :=
  let g (a : α) (t : Term) : α := f a (.TM t)
  match cm with
  | .ChMsg _ _ t => foldCarriedTerms g (f acc (.CM cm)) t
  | .Plain t   => foldCarriedTerms g acc t

-- ── CMT operations ────────────────────────────────────────────────────────────

/-- Apply `f` to the underlying term(s).
    Mirrors `cmtMap :: (Term -> Term) -> CMT -> CMT`. -/
def cmtMap (f : Term → Term) : CMT → CMT
  | .CM cm => .CM (cmMap f cm)
  | .TM t  => .TM (f t)

/-- Extract all constituent terms.
    Mirrors `cmtTerms :: CMT -> [Term]`. -/
def cmtTerms : CMT → List Term
  | .CM cm => cmTerms cm
  | .TM t  => [t]

/-- Unify two `CMT` values.
    Mirrors `cmtUnify :: CMT -> CMT -> GenSubst -> [GenSubst]`. -/
def cmtUnify : CMT → CMT → GenSubst → List GenSubst
  | .CM cm, .CM cm', gs => cmUnify cm cm' gs
  | .TM t,  .TM t',  gs => unify t t' gs
  | _,      _,       _  => []

/-- Extract the primary term.
    Mirrors `cmtTerm :: CMT -> Term`. -/
def cmtTerm : CMT → Term
  | .CM cm => cmTerm cm
  | .TM t  => t

/-- Apply a substitution to a `CMT`.
    Mirrors `cmtSubstitute :: Subst -> CMT -> CMT`. -/
def cmtSubstitute (subst : Subst) (cmt : CMT) : CMT :=
  cmtMap (substitute subst) cmt

-- ── Place helpers ─────────────────────────────────────────────────────────────

/-- Prepend index `n` to a place path.
    Mirrors `prefix :: Int -> Place -> Place`. -/
def prefixPlace (n : Int) (p : Place) : Place := ⟨n :: p.path⟩

/-- The places within `cm` at which `ct` is carried.
    Mirrors `cmtCarriedPlaces :: CMT -> ChMsg -> [Place]`. -/
def cmtCarriedPlaces (ct : CMT) (cm : ChMsg) : List Place :=
  match ct, cm with
  | .TM t, .Plain t'    => (carriedPlaces t t').map (prefixPlace 0)
  | .TM t, .ChMsg _ _ t'  => (carriedPlaces t t').map (prefixPlace 1)
  | .CM c, _            => if c == cm then [⟨[]⟩] else []

/-- The `CMT` ancestors of `cm` along place `pl`.
    Mirrors `cmtAncestors :: ChMsg -> Place -> [CMT]`. -/
def cmtAncestors (cm : ChMsg) (pl : Place) : List CMT :=
  match cm, pl.path with
  | _,           []               => []
  | .Plain t,    (0 : Int) :: path =>
      .CM cm :: (ancestors t ⟨path⟩).map .TM
  | .ChMsg _ _ t,  (1 : Int) :: path =>
      .CM cm :: (ancestors t ⟨path⟩).map .TM
  | _,           _               =>
      assertError "Channel.cmtAncestors: Bad path to term"

end LeanCPSA.Channel
