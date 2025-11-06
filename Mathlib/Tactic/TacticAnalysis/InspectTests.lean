import Mathlib.Tactic.TacticAnalysis.Inspect

open Lean
/--
info: inspect:
---
  intro a h
  have := h
  inspect_lhs
  inspect_rhs
  inspect h
  inspect this
  simpa
---

Syntax.node Parser.Tactic.tacticSeq, SourceInfo.none
|-Syntax.node Parser.Tactic.tacticSeq1Indented, SourceInfo.none
|   |-Syntax.node null, SourceInfo.none
|   |   |-Syntax.node Parser.Tactic.intro, SourceInfo.none
|   |   |   |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- 'intro'
|   |   |   |-Syntax.node null, SourceInfo.none
|   |   |   |   |-Syntax.ident SourceInfo.original: ⟨⟩⟨ ⟩-- (a,a) -- []
|   |   |   |   |-Syntax.ident SourceInfo.original: ⟨⟩⟨⏎  ⟩-- (h,h) -- []
|   |   |-Syntax.node null, SourceInfo.none
|   |   |-Syntax.node Parser.Tactic.tacticHave__, SourceInfo.none
|   |   |   |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- 'have'
|   |   |   |-Syntax.node Parser.Term.letConfig, SourceInfo.none
|   |   |   |   |-Syntax.node null, SourceInfo.none
|   |   |   |-Syntax.node Parser.Term.letDecl, SourceInfo.none
|   |   |   |   |-Syntax.node Parser.Term.letIdDecl, SourceInfo.none
|   |   |   |   |   |-Syntax.node Parser.Term.letId, SourceInfo.none
|   |   |   |   |   |   |-Syntax.node hygieneInfo, SourceInfo.none
|   |   |   |   |   |   |   |-Syntax.ident SourceInfo.original: ⟨⟩⟨⟩-- (,[anonymous]) -- []
|   |   |   |   |   |-Syntax.node null, SourceInfo.none
|   |   |   |   |   |-Syntax.node null, SourceInfo.none
|   |   |   |   |   |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- ':='
|   |   |   |   |   |-Syntax.ident SourceInfo.original: ⟨⟩⟨⏎  ⟩-- (h,h) -- []
|   |   |-Syntax.node null, SourceInfo.none
|   |   |-Syntax.node InspectExpr.tacticInspect_lhs, SourceInfo.none
|   |   |   |-Syntax.atom SourceInfo.original: ⟨⟩⟨⏎  ⟩-- 'inspect_lhs'
|   |   |-Syntax.node null, SourceInfo.none
|   |   |-Syntax.node InspectExpr.tacticInspect_rhs, SourceInfo.none
|   |   |   |-Syntax.atom SourceInfo.original: ⟨⟩⟨⏎  ⟩-- 'inspect_rhs'
|   |   |-Syntax.node null, SourceInfo.none
|   |   |-Syntax.node InspectExpr.tacticInspect, SourceInfo.none
|   |   |   |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- 'inspect'
|   |   |   |-Syntax.node null, SourceInfo.none
|   |   |   |   |-Syntax.ident SourceInfo.original: ⟨⟩⟨⏎  ⟩-- (h,h) -- []
|   |   |-Syntax.node null, SourceInfo.none
|   |   |-Syntax.node InspectExpr.tacticInspect, SourceInfo.none
|   |   |   |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- 'inspect'
|   |   |   |-Syntax.node null, SourceInfo.none
|   |   |   |   |-Syntax.ident SourceInfo.original: ⟨⟩⟨⏎  ⟩-- (this,this) -- []
|   |   |-Syntax.node null, SourceInfo.none
|   |   |-Syntax.node Parser.Tactic.simpa, SourceInfo.none
|   |   |   |-Syntax.atom SourceInfo.original: ⟨⟩⟨⏎⏎⟩-- 'simpa'
|   |   |   |-Syntax.node null, SourceInfo.none
|   |   |   |-Syntax.node null, SourceInfo.none
|   |   |   |-Syntax.node Parser.Tactic.simpaArgsRest, SourceInfo.none
|   |   |   |   |-Syntax.node Parser.Tactic.optConfig, SourceInfo.none
|   |   |   |   |   |-Syntax.node null, SourceInfo.none
|   |   |   |   |-Syntax.node null, SourceInfo.none
|   |   |   |   |-Syntax.node null, SourceInfo.none
|   |   |   |   |-Syntax.node null, SourceInfo.none
|   |   |   |   |-Syntax.node null, SourceInfo.none
---
info: inspect: 'a + a ≠ 0 + 0'

'Ne' -- app
|-'Nat' '[]' -- const
|-'HAdd.hAdd' -- app
|   |-'Nat' '[]' -- const
|   |-'Nat' '[]' -- const
|   |-'Nat' '[]' -- const
|   |-'instHAdd' -- app
|   |   |-'Nat' '[]' -- const
|   |   |-'instAddNat' '[]' -- const
|   |-'_uniq.128' -- fvar
|   |-'_uniq.128' -- fvar
|-'HAdd.hAdd' -- app
|   |-'Nat' '[]' -- const
|   |-'Nat' '[]' -- const
|   |-'Nat' '[]' -- const
|   |-'instHAdd' -- app
|   |   |-'Nat' '[]' -- const
|   |   |-'instAddNat' '[]' -- const
|   |-'OfNat.ofNat' -- app
|   |   |-'Nat' '[]' -- const
|   |   |-'0' -- lit
|   |   |-'instOfNatNat' -- app
|   |   |   |-'0' -- lit
|   |-'OfNat.ofNat' -- app
|   |   |-'Nat' '[]' -- const
|   |   |-'0' -- lit
|   |   |-'instOfNatNat' -- app
|   |   |   |-'0' -- lit
---
info: inspect: 'False'

'False' '[]' -- const
---
info: inspect: 'a ≠ 0'

'Ne' -- app
|-'Nat' '[]' -- const
|-'_uniq.128' -- fvar
|-'OfNat.ofNat' -- app
|   |-'Nat' '[]' -- const
|   |-'0' -- lit
|   |-'instOfNatNat' -- app
|   |   |-'0' -- lit
---
info: inspect: 'a ≠ 0'

'_uniq.135' -- mvar
-/
#guard_msgs in
example {a : Nat} (h : a ≠ 0) : (a + a ≠ 0 + 0) ≠ False := by
  revert a
  inspect
  intro a h
  have := h
  inspect_lhs
  inspect_rhs
  inspect h
  inspect this
  simpa

/--
info: inspect:
---
/-- I am a doc-string -/
@[simp, grind =]
private nonrec theorem X (a : Nat) (b : Int) : a + b = b + a := by apply Int.add_comm
---

Syntax.node Parser.Command.declaration, SourceInfo.none
|-Syntax.node Parser.Command.declModifiers, SourceInfo.none
| |-Syntax.node null, SourceInfo.none
| | |-Syntax.node Parser.Command.docComment, SourceInfo.none
| | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- '/--'
| | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨⏎⟩-- 'I am a doc-string -/'
| |-Syntax.node null, SourceInfo.none
| | |-Syntax.node Parser.Term.attributes, SourceInfo.none
| | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨⟩-- '@['
| | | |-Syntax.node null, SourceInfo.none
| | | | |-Syntax.node Parser.Term.attrInstance, SourceInfo.none
| | | | | |-Syntax.node Parser.Term.attrKind, SourceInfo.none
| | | | | | |-Syntax.node null, SourceInfo.none
| | | | | |-Syntax.node Parser.Attr.simp, SourceInfo.none
| | | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨⟩-- 'simp'
| | | | | | |-Syntax.node null, SourceInfo.none
| | | | | | |-Syntax.node null, SourceInfo.none
| | | | | | |-Syntax.node null, SourceInfo.none
| | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- ','
| | | | |-Syntax.node Parser.Term.attrInstance, SourceInfo.none
| | | | | |-Syntax.node Parser.Term.attrKind, SourceInfo.none
| | | | | | |-Syntax.node null, SourceInfo.none
| | | | | |-Syntax.node Parser.Attr.grind, SourceInfo.none
| | | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- 'grind'
| | | | | | |-Syntax.node null, SourceInfo.none
| | | | | | | |-Syntax.node Parser.Attr.grindMod, SourceInfo.none
| | | | | | | | |-Syntax.node Parser.Attr.grindEq, SourceInfo.none
| | | | | | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨⟩-- '='
| | | | | | | | | |-Syntax.node null, SourceInfo.none
| | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨⏎⟩-- ']'
| |-Syntax.node null, SourceInfo.none
| | |-Syntax.node Parser.Command.private, SourceInfo.none
| | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- 'private'
| |-Syntax.node null, SourceInfo.none
| |-Syntax.node null, SourceInfo.none
| |-Syntax.node null, SourceInfo.none
| |-Syntax.node null, SourceInfo.none
| | |-Syntax.node Parser.Command.nonrec, SourceInfo.none
| | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- 'nonrec'
|-Syntax.node Parser.Command.theorem, SourceInfo.none
| |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- 'theorem'
| |-Syntax.node Parser.Command.declId, SourceInfo.none
| | |-Syntax.ident SourceInfo.original: ⟨⟩⟨ ⟩-- (X,X) -- []
| | |-Syntax.node null, SourceInfo.none
| |-Syntax.node Parser.Command.declSig, SourceInfo.none
| | |-Syntax.node null, SourceInfo.none
| | | |-Syntax.node Parser.Term.explicitBinder, SourceInfo.none
| | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨⟩-- '('
| | | | |-Syntax.node null, SourceInfo.none
| | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨ ⟩-- (a,a) -- []
| | | | |-Syntax.node null, SourceInfo.none
| | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- ':'
| | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨⟩-- (Nat,Nat) -- []
| | | | |-Syntax.node null, SourceInfo.none
| | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- ')'
| | | |-Syntax.node Parser.Term.explicitBinder, SourceInfo.none
| | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨⟩-- '('
| | | | |-Syntax.node null, SourceInfo.none
| | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨ ⟩-- (b,b) -- []
| | | | |-Syntax.node null, SourceInfo.none
| | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- ':'
| | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨⟩-- (Int,Int) -- []
| | | | |-Syntax.node null, SourceInfo.none
| | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- ')'
| | |-Syntax.node Parser.Term.typeSpec, SourceInfo.none
| | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- ':'
| | | |-Syntax.node «term_=_», SourceInfo.none
| | | | |-Syntax.node «term_+_», SourceInfo.none
| | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨ ⟩-- (a,a) -- []
| | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- '+'
| | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨ ⟩-- (b,b) -- []
| | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- '='
| | | | |-Syntax.node «term_+_», SourceInfo.none
| | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨ ⟩-- (b,b) -- []
| | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- '+'
| | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨ ⟩-- (a,a) -- []
| |-Syntax.node Parser.Command.declValSimple, SourceInfo.none
| | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- ':='
| | |-Syntax.node Parser.Term.byTactic, SourceInfo.none
| | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨⏎  ⟩-- 'by'
| | | |-Syntax.node Parser.Tactic.tacticSeq, SourceInfo.none
| | | | |-Syntax.node Parser.Tactic.tacticSeq1Indented, SourceInfo.none
| | | | | |-Syntax.node null, SourceInfo.none
| | | | | | |-Syntax.node Parser.Tactic.apply, SourceInfo.none
| | | | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- 'apply'
| | | | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨⏎⟩-- (Int.add_comm,Int.add_comm) -- []
| | |-Syntax.node Parser.Termination.suffix, SourceInfo.none
| | | |-Syntax.node null, SourceInfo.none
| | | |-Syntax.node null, SourceInfo.none
| | |-Syntax.node null, SourceInfo.none
-/
#guard_msgs in
inspect compact
/-- I am a doc-string -/
@[simp, grind =]
private nonrec theorem X (a : Nat) (b : Int) : a + b = b + a := by
  apply Int.add_comm
