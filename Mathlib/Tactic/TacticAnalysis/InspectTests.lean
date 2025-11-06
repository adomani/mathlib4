import Mathlib.Tactic.TacticAnalysis.Inspect


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

Lean.Syntax.node Lean.Parser.Tactic.tacticSeq, Lean.SourceInfo.none
|-Lean.Syntax.node Lean.Parser.Tactic.tacticSeq1Indented, Lean.SourceInfo.none
|   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |-Lean.Syntax.node Lean.Parser.Tactic.intro, Lean.SourceInfo.none
|   |   |   |-Lean.Syntax.atom Lean.SourceInfo.original: ⟨⟩⟨ ⟩-- 'intro'
|   |   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |   |   |-Lean.Syntax.ident Lean.SourceInfo.original: ⟨⟩⟨ ⟩-- (a,a) -- []
|   |   |   |   |-Lean.Syntax.ident Lean.SourceInfo.original: ⟨⟩⟨⏎  ⟩-- (h,h) -- []
|   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |-Lean.Syntax.node Lean.Parser.Tactic.tacticHave__, Lean.SourceInfo.none
|   |   |   |-Lean.Syntax.atom Lean.SourceInfo.original: ⟨⟩⟨ ⟩-- 'have'
|   |   |   |-Lean.Syntax.node Lean.Parser.Term.letConfig, Lean.SourceInfo.none
|   |   |   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |   |-Lean.Syntax.node Lean.Parser.Term.letDecl, Lean.SourceInfo.none
|   |   |   |   |-Lean.Syntax.node Lean.Parser.Term.letIdDecl, Lean.SourceInfo.none
|   |   |   |   |   |-Lean.Syntax.node Lean.Parser.Term.letId, Lean.SourceInfo.none
|   |   |   |   |   |   |-Lean.Syntax.node hygieneInfo, Lean.SourceInfo.none
|   |   |   |   |   |   |   |-Lean.Syntax.ident Lean.SourceInfo.original: ⟨⟩⟨⟩-- (,[anonymous]) -- []
|   |   |   |   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |   |   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |   |   |   |-Lean.Syntax.atom Lean.SourceInfo.original: ⟨⟩⟨ ⟩-- ':='
|   |   |   |   |   |-Lean.Syntax.ident Lean.SourceInfo.original: ⟨⟩⟨⏎  ⟩-- (h,h) -- []
|   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |-Lean.Syntax.node InspectExpr.tacticInspect_lhs, Lean.SourceInfo.none
|   |   |   |-Lean.Syntax.atom Lean.SourceInfo.original: ⟨⟩⟨⏎  ⟩-- 'inspect_lhs'
|   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |-Lean.Syntax.node InspectExpr.tacticInspect_rhs, Lean.SourceInfo.none
|   |   |   |-Lean.Syntax.atom Lean.SourceInfo.original: ⟨⟩⟨⏎  ⟩-- 'inspect_rhs'
|   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |-Lean.Syntax.node InspectExpr.tacticInspect, Lean.SourceInfo.none
|   |   |   |-Lean.Syntax.atom Lean.SourceInfo.original: ⟨⟩⟨ ⟩-- 'inspect'
|   |   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |   |   |-Lean.Syntax.ident Lean.SourceInfo.original: ⟨⟩⟨⏎  ⟩-- (h,h) -- []
|   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |-Lean.Syntax.node InspectExpr.tacticInspect, Lean.SourceInfo.none
|   |   |   |-Lean.Syntax.atom Lean.SourceInfo.original: ⟨⟩⟨ ⟩-- 'inspect'
|   |   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |   |   |-Lean.Syntax.ident Lean.SourceInfo.original: ⟨⟩⟨⏎  ⟩-- (this,this) -- []
|   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |-Lean.Syntax.node Lean.Parser.Tactic.simpa, Lean.SourceInfo.none
|   |   |   |-Lean.Syntax.atom Lean.SourceInfo.original: ⟨⟩⟨⏎⟩-- 'simpa'
|   |   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |   |-Lean.Syntax.node Lean.Parser.Tactic.simpaArgsRest, Lean.SourceInfo.none
|   |   |   |   |-Lean.Syntax.node Lean.Parser.Tactic.optConfig, Lean.SourceInfo.none
|   |   |   |   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
|   |   |   |   |-Lean.Syntax.node null, Lean.SourceInfo.none
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
