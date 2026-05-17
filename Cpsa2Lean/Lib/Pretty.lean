/-
Cpsa2Lean.Lib.Pretty

Port of CPSA.Lib.Pretty (MITRE cpsa v4.4.8).
A simple pretty printer. Algorithm by Lawrence C. Paulson, simplifying
one by Derek C. Oppen.

`pr` is simplified from `ShowS` (a `String → String` difference list)
to return a plain `String`; `printing` is restructured to be
strictly left-to-right so it works without lazy evaluation.
-/

namespace Cpsa2Lean.Lib

-- ── Pretty document type ──────────────────────────────────────────────────────

/-- A pretty-printing document.
    Mirrors `data Pretty = Str String | Brk Int | Blo [Pretty] Int Int | ...`. -/
inductive Pretty where
  | Str : String → Pretty
  | Brk : Int → Pretty
  /-- Block: if any break is taken, the minimum number are taken.
      Fields: items, indent, total pre-break size. -/
  | Blo : List Pretty → Int → Int → Pretty
  /-- Group: if any break is taken, all breaks are taken.
      Fields: items, indent, total pre-break size. -/
  | Grp : List Pretty → Int → Int → Pretty

instance : Inhabited Pretty := ⟨.Str ""⟩

namespace Pretty

-- ── Size helpers ──────────────────────────────────────────────────────────────

private def prettySize : Pretty → Int
  | .Str s     => (s.length : Int)
  | .Brk n     => n
  | .Blo _ _ n => n
  | .Grp _ _ n => n

private def prettyLen : List Pretty → Int → Int
  | [],      k => k
  | e :: es, k => prettyLen es (prettySize e + k)

-- ── Public constructors ───────────────────────────────────────────────────────

/-- Create a string atom.  Mirrors `str`. -/
def str (s : String) : Pretty := .Str s

/-- Create a breakable space of width `n`.  Mirrors `brk`. -/
def brk (n : Int) : Pretty := .Brk n

/-- Create a block (minimum breaks).  Mirrors `blo`. -/
def blo (indent : Int) (es : List Pretty) : Pretty :=
  .Blo es indent (prettyLen es 0)

/-- Create a group (all-or-nothing breaks).  Mirrors `grp`. -/
def grp (indent : Int) (es : List Pretty) : Pretty :=
  .Grp es indent (prettyLen es 0)

-- ── Core printer ──────────────────────────────────────────────────────────────

-- Distance in characters to the nearest break point (or `after` if none).
private def breakdist : List Pretty → Int → Int
  | .Str s :: es,     after => (s.length : Int) + breakdist es after
  | .Brk _ :: _,      _     => 0
  | .Blo _ _ n :: es, after => n + breakdist es after
  | .Grp _ _ n :: es, after => n + breakdist es after
  | [],               after => after

-- Strict left-to-right reformulation of Paulson's `printing`.
-- Returns `(remaining_space, string_fragment)`.
-- The original Haskell version uses a lazy `ShowS` accumulator;
-- here we concatenate left-to-right in a strict setting.
private def printing (margin : Int) (es : List Pretty)
    (blockspace after : Int) (force : Bool) (space : Int) : Int × String :=
  match es with
  | [] => (space, "")
  | e :: rest =>
    match e with
    | .Str s =>
      let (sp, frag) := printing margin rest blockspace after force
                          (space - (s.length : Int))
      (sp, s ++ frag)
    | .Brk n =>
      let after' := breakdist rest after
      if !force && n + after' <= space then
        -- No break: emit `n` spaces.
        let (sp, frag) := printing margin rest blockspace after force (space - n)
        (sp, String.mk (List.replicate n.toNat ' ') ++ frag)
      else
        -- Break: newline then indent to `blockspace`.
        let ind : Int := margin - blockspace
        let (sp, frag) := printing margin rest blockspace after force (margin - ind)
        (sp, "\n" ++ String.mk (List.replicate ind.toNat ' ') ++ frag)
    | .Blo bes indent _ =>
      let after'      := breakdist rest after
      let (sp2, s2)   := printing margin bes (space - indent) after' false space
      let (sp3, frag) := printing margin rest blockspace after force sp2
      (sp3, s2 ++ frag)
    | .Grp bes indent n =>
      let dist        := breakdist rest after
      let (sp2, s2)   := printing margin bes (space - indent) dist (n + dist > space) space
      let (sp3, frag) := printing margin rest blockspace after force sp2
      (sp3, s2 ++ frag)

/-- Pretty-print `e` with right margin `margin`.
    Mirrors `pr :: Int -> Pretty -> ShowS` (collapsed to return `String`). -/
def pr (margin : Int) (e : Pretty) : String :=
  (printing margin [e] margin 0 false margin).2

end Pretty

end Cpsa2Lean.Lib
