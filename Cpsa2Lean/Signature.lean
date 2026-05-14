/-
Cpsa2Lean.Signature

Port of the data model from `src/CPSA/Signature.hs` (MITRE cpsa v4.4.8).
Defines `Sig`, `Operator`, `defaultSig`, and `findOper`.

The S-expression loader `loadSig` is intentionally NOT ported in this
iteration — it requires `Cpsa2Lean.Lib.SExpr`, which has not yet been
translated.  See the TODO block at the end of this file.
-/

namespace Cpsa2Lean.Signature

/-- Operators that may appear in an algebra's signature.  Each carries the
    user-facing symbol used in the surface syntax (e.g. `"enc"`, `"hash"`,
    or a custom name).

    Mirrors `data Operator` in `CPSA.Signature`. -/
inductive Operator where
  /-- An "enc"-like operator. -/
  | enc  (sym : String) : Operator
  /-- An "enc"-like operator for use with symmetric keys. -/
  | senc (sym : String) : Operator
  /-- An "enc"-like operator for use with asymmetric keys. -/
  | aenc (sym : String) : Operator
  /-- A digital-signature-like operator. -/
  | sign (sym : String) : Operator
  /-- A "hash"-like operator. -/
  | hash (sym : String) : Operator
  /-- A "cat"-like (tuple) operator.  `arity` is expected to be at least 1;
      the loader enforces this invariant. -/
  | tupl (sym : String) (arity : Nat) : Operator
  deriving Repr, BEq, DecidableEq

/-- The surface symbol associated with an operator. -/
def Operator.sym : Operator → String
  | .enc s | .senc s | .aenc s | .sign s | .hash s | .tupl s _ => s

/-- A signature for an algebra: lists of atom sorts, akey sorts, and
    operators.

    Mirrors `data Sig` in `CPSA.Signature`.  Field names match the Haskell
    source so qualified references like `Sig.atoms s` carry over unchanged. -/
structure Sig where
  /-- Sorts that are not `chan` or `locn`. -/
  atoms : List String
  /-- Asymmetric-key sorts; expected to be a subset of `atoms`. -/
  akeys : List String
  /-- Operators declared in this signature. -/
  opers : List Operator
  deriving Repr, BEq, DecidableEq

/-- The default signature used when no `(lang ...)` form is supplied in a
    CPSA input: four atom sorts (`text`, `data`, `skey`, `akey`), one akey
    sort (`akey`), and two operators (`enc`, `hash`). -/
def defaultSig : Sig :=
  { atoms := ["text", "data", "skey", "akey"],
    akeys := ["akey"],
    opers := [.enc "enc", .hash "hash"] }

/-- Look up an operator by its surface symbol.  Returns the first operator
    in the list whose `sym` matches, or `none`.

    The Haskell source contains two duplicate `Enc` clauses in the middle
    of this function (lines 44–45 of `Signature.hs`); those are dead code
    and are deliberately omitted here. -/
def findOper (sym : String) : List Operator → Option Operator
  | []          => none
  | op :: rest  => if op.sym == sym then some op else findOper sym rest

/-- True when every entry in `akeys` is also in `atoms`.  This is the
    invariant enforced by `loadSig`; `Sig` values constructed by other
    means are not required to satisfy it. -/
def Sig.isValidAkeys (s : Sig) : Bool :=
  s.akeys.all (s.atoms.contains ·)

/-
TODO: port `loadSig` once `Cpsa2Lean.Lib.SExpr` exists.

Haskell source signature:
    loadSig :: MonadFail m => Pos -> [SExpr Pos] -> m Sig

Likely Lean shape:
    def loadSig (pos : Pos) (decls : List (SExpr Pos)) : Except String Sig

The parser needs to:
  * fold over declarations starting from `defaultSig` (NOT empty lists)
  * reject atoms in {"mesg", "name", "chan", "locn", "indx", "pval", "strd"}
  * reject operator symbols in {"pubk", "privk", "invk", "ltk", "cat"}
  * reject `tupl _ n` with `n < 1`
  * enforce `Sig.isValidAkeys`
  * enforce that operator symbols are pairwise distinct
  * deduplicate (`List.eraseDups` / Haskell `nub`) atoms and akeys before
    storing
-/

end Cpsa2Lean.Signature
