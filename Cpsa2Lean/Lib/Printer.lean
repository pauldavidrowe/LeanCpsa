/-
Cpsa2Lean.Lib.Printer

Port of CPSA.Lib.Printer (MITRE cpsa v4.4.8).
CPSA-specific S-expression pretty printer built on `Cpsa2Lean.Lib.Pretty`.

Special layout rules:
  - `defprotocol` bodies get per-element line breaks.
  - `defrole` and `defrule` sub-forms inside `defprotocol` get group/formula layout.
  - `defgoal` bodies use formula (forall/implies-aware) layout.
  - `defmacro` uses group layout; `herald` uses block layout.
  - Everything else uses group layout.

The `loop` helpers from the Haskell `where` clauses are hoisted to
standalone private functions and bundled in a single `mutual` block.
-/

import Cpsa2Lean.Lib.SExpr
import Cpsa2Lean.Lib.Pretty

namespace Cpsa2Lean.Lib

open Pretty (str brk blo grp)

-- ── Mutually recursive layout functions ───────────────────────────────────────

mutual

  -- ── block ──────────────────────────────────────────────────────────────────

  /-- Block-style layout: atoms inline, list items separated by break-1. -/
  private def blockFmt {α : Type} (indent : Int) : SExpr α → Pretty
    | .sym _ s  => str s
    | .str _ s  => str (SExpr.showQuoted s)
    | .num _ n  => str (toString n)
    | .lst _ [] => str "()"
    | .lst _ (x :: xs) =>
        blockLoop indent [blockFmt indent x, str "("] xs

  private def blockLoop {α : Type} (indent : Int)
      (es : List Pretty) : List (SExpr α) → Pretty
    | []      => blo indent (es.reverse ++ [str ")"])
    | x :: xs => blockLoop indent (blockFmt indent x :: brk 1 :: es) xs

  -- ── group ──────────────────────────────────────────────────────────────────

  /-- Group-style layout: atoms/numbers inline, lists and quoted strings on breaks. -/
  private def groupFmt {α : Type} (indent : Int) : SExpr α → Pretty
    | .lst _ (x :: xs) => groupLoop indent [blockFmt indent x, str "("] xs
    | x => blockFmt indent x

  private def groupLoop {α : Type} (indent : Int)
      (es : List Pretty) : List (SExpr α) → Pretty
    | []      => grp indent (es.reverse ++ [str ")"])
    | x :: xs =>
      match x with
      | .sym _ _ | .num _ _ =>
          groupLoop indent (blockFmt indent x :: str " " :: es) xs
      | _ =>
          groupLoop indent (blockFmt indent x :: brk 1 :: es) xs

  -- ── disj ───────────────────────────────────────────────────────────────────

  /-- Disjunction layout: `or`-headed lists get group style; others get block. -/
  private def disjFmt {α : Type} (indent : Int) : SExpr α → Pretty
    | x@(.lst _ (.sym _ "or" :: _)) => groupFmt indent x
    | x => blockFmt indent x

  -- ── formula ────────────────────────────────────────────────────────────────

  /-- Formula layout for `defgoal`/`defrule` bodies. -/
  private def formulaFmt {α : Type} (indent : Int)
      (x : SExpr α) (forms : List (SExpr α)) : Pretty :=
    formulaLoop indent [blockFmt indent x, str "("] forms

  /-- Loop helper for `formulaFmt`.  Recognises `(forall decs (implies antec concl))`. -/
  private def formulaLoop {α : Type} (indent : Int)
      (es : List Pretty) : List (SExpr α) → Pretty
    | [] => grp indent (es.reverse ++ [str ")"])
    | .lst _ [.sym _ "forall", decs, .lst _ [.sym _ "implies", antec, concl]] :: xs =>
        let inner :=
          grp indent
            [ str "(implies", brk 1,
              blockFmt indent antec, brk 1,
              disjFmt indent concl ]
        let forallBlk :=
          blo indent
            [ str "(forall", brk 1,
              blockFmt indent decs, brk 1,
              inner,
              str "))" ]
        formulaLoop indent (forallBlk :: brk 1 :: es) xs
    | x :: xs =>
      match x with
      | .sym _ _ | .num _ _ =>
          formulaLoop indent (blockFmt indent x :: str " " :: es) xs
      | _ =>
          formulaLoop indent (blockFmt indent x :: brk 1 :: es) xs

  -- ── pretty ─────────────────────────────────────────────────────────────────

  /-- Top-level layout dispatcher. -/
  private def prettyFmt {α : Type} (indent : Int) : SExpr α → Pretty
    | .lst _ (head@(.sym _ "defprotocol") :: xs) =>
        prettyLoop indent [blockFmt indent head, str "("] xs
    | .lst _ (head@(.sym _ "defgoal") :: forms) =>
        formulaFmt indent head forms
    | x@(.lst _ (.sym _ "defmacro" :: _)) => groupFmt indent x
    | x@(.lst _ (.sym _ "herald" :: _))   => blockFmt indent x
    | x => groupFmt indent x

  /-- Loop helper for `defprotocol` bodies. -/
  private def prettyLoop {α : Type} (indent : Int)
      (es : List Pretty) : List (SExpr α) → Pretty
    | [] => grp indent (es.reverse ++ [str ")"])
    | x@(.sym _ _) :: xs =>
        prettyLoop indent (blockFmt indent x :: str " " :: es) xs
    | x@(.str _ _) :: xs =>
        prettyLoop indent (blockFmt indent x :: brk 1 :: es) xs
    | x@(.num _ _) :: xs =>
        prettyLoop indent (blockFmt indent x :: str " " :: es) xs
    | x@(.lst _ (.sym _ "defrole" :: _)) :: xs =>
        prettyLoop indent (groupFmt indent x :: brk 1 :: es) xs
    | (.lst _ (head@(.sym _ "defrule") :: forms)) :: xs =>
        prettyLoop indent (formulaFmt indent head forms :: brk 1 :: es) xs
    | x@(.lst _ _) :: xs =>
        prettyLoop indent (blockFmt indent x :: brk 1 :: es) xs

end

-- ── Public entry point ────────────────────────────────────────────────────────

/-- Pretty-print an S-expression with the given margin and indent.
    Mirrors `pp :: Int -> Int -> SExpr a -> String`. -/
def pp {α : Type} (margin indent : Int) (sexpr : SExpr α) : String :=
  Pretty.pr margin (prettyFmt indent sexpr)

end Cpsa2Lean.Lib
