import Lean
import Mathlib.adomaniLeanUtils.inspect_syntax
import Mathlib.adomaniLeanUtils.inspect_infotree

def showFirst (n : Nat) (s : String) : String :=
  if s.length ≤ n + 10 then s else
    s.take n ++ "…" ++ s.drop (s.length - 10)

open Lean

/--
`CInfo` is the information about a deprecated constant.
It contains:
* the kind of syntax that produced it (`ident`, `dotIdent`, `identProj`);
* the expression (which is the constant itself);
* the range of the syntax that produced it.
-/
structure CInfo where
  /--
  For instance, if the constant name is `Nat.mySucc` taking a `Nat` `m` as input,
  then the possible values are:
  * `ident`, for `Nat.mySucc m` or `mySucc m` with `open Nat`;
  * `Lean.Parser.Term.dotIdent`, for `.mySucc m` (when `Nat` is the expected type);
  * `Lean.Parser.Term.identProj`, for `m.mySucc` ("proper dot-notation").
  -/
  kind : SyntaxNodeKind
  /-- The expression: this is always of the form ``.const `name universeLevels`` -/
  expr : Expr
  /--
  The range of the syntax that produced this constant.
  In the case of a `dotIdent`, the range includes the leading dot.
  -/
  rg : String.Range
  deriving BEq, Hashable

def sortCInfos (h : Std.HashSet CInfo) : Array CInfo :=
  h.toArray.qsort (fun a b =>
    a.rg.start < b.rg.start || (a.rg.start == b.rg.start && a.rg.stop < b.rg.stop))

instance : ToString CInfo where
  toString c := s!"{c.expr} of kind {c.kind} @ {(c.rg.start, c.rg.stop)}"

def Lean.Elab.Info.Constant? : Info → Option CInfo
  | .ofTermInfo ti => match ti.expr with
    | .const .. => some ⟨ti.stx.getKind, ti.expr, ti.stx.getRange?.getD default⟩
    | _ => none
  | _ => none

partial
def Lean.Elab.InfoTree.toConstants : InfoTree → Std.HashSet CInfo
  | .context _i t => t.toConstants
  | .node i children =>
    children.foldl (·.insertMany ·.toConstants) (if let some ci := i.Constant? then {ci} else ∅)
    --(children.toArray.flatMap (·.toConstants)) ++ #[i.Constant?].reduceOption
  | .hole _mvarId => ∅

open Lean Elab Command PartialContextInfo Info
elab "rd " old:(ident)? " -|-> " new:(ident)? cmd:command : command => do
  let oldName := old.map (·.getId)
  let newName := new.map (·.getId)
  elabCommand cmd
  --let msg := (← get).messages.reportedPlusUnreported
  --let msgStart := match msg.size with
  --  | 1 => m!"there is 1 message"
  --  | _ => m!"there are {msg.size} messages"
  --logInfo <| m!"\n".joinSep
  --  (msgStart :: m!"" :: (msg.toArray.map fun m => m!"{(m.pos, m.endPos.getD m.pos)}").toList)
  --logInfo
  --  m!"Renaming '{oldName}' to '{newName}' in \
  --    {indentD <| m!"{showFirst 20 (cmd.raw.getSubstring?.get!).toString}"}"
  let newStx ← cmd.raw.replaceM fun s => do
    let id := s.getId
    if id.isAnonymous then return none else
    let comps := id.components
    let newComps : List Name :=
      comps.map fun
        | .str a b =>
          .str a (b.replace "le_refl_deprecated" "le_refl")
        | c => c
    let newId := newComps.foldl (init := .anonymous) (· ++ ·)
    --logInfoAt s m!"{newComps}: {.ofConstName newId}"
    return some <| mkIdentFrom s newId
  --logInfo newStx
  let trees ← getInfoTrees
  let substr := cmd.raw.getSubstring?.get!
  for tree in trees do
    for {kind := k, expr := e, rg := r} in tree.toConstants do
      let econst := e.constName!
      if let some oldName := oldName then
        if econst != oldName then continue
      logInfoAt (.ofRange r)
        m!"{econst} of kind '{k}', written as \
          '{({substr with startPos := r.start, stopPos := r.stop}).toString}'"
    --logInfo (m!"InfoTree has {tree.toConstants.size} constants: {m!"\n  ".joinSep <| "" :: ((sortCInfos tree.toConstants).map (m!"{·}")).toList}")
  elabCommand newStx

--inspect
rd trivial -|-> newTrivial
example : True := trivial

inspect
rd trivial  -|-> newTrivial
example : True := .intro

@[deprecated Nat.zero_le (since := "")] def Nat.ZeroLe (n : Nat) : 0 ≤ n := n.zero_le

inspectIT
example : True := trivial

@[deprecated Nat.succ (since := "")] def Nat.mySucc (n : Nat) := n.succ

open Nat
variable {m : Nat}

set_option linter.deprecated false

rd Nat.mySucc -|-> b example : Nat := Nat.mySucc <| .mySucc <| m.mySucc
rd a  -|-> b inspectIT example : Nat := Nat.mySucc <| .mySucc <| mySucc  m.mySucc

set_option linter.deprecated false in
open Nat in
variable {m : Nat} in
rd a  -|-> b
inspectIT
example : Nat := .mySucc <| mySucc m.mySucc

variable {m : Nat} in
inspectIT
example := m.mySucc

variable {m : Nat} in
#check m.succ
variable {m : Nat} in
#check Nat.succ m

variable {m n o : Nat} (mn : m ≤ n) (no : n ≤ o)
inspectIT
rd trivial  -|-> newTrivial
example : 0 ≤ m + 1 :=
  m.succ.ZeroLe

--rd trivial  -|-> newTrivial
inspectIT
example : m ≤ n := by
  assumption

@[deprecated Nat.le_trans (since := "")]
def LE.le.trans := Nat.le_trans mn no
@[deprecated Nat.le_refl (since := "")]
def Nat.le_refl_deprecated := Nat.le_refl m

--set_option linter.deprecated false

rd a  -|-> b
inspectIT
example : m ≤ m + 1 := by
  exact
    (m ).le_refl_deprecated.trans (Nat.le_succ m)

--#print dd

example : 0 ≤ 0 := Nat.zero_le 0

--#check Nat.le_rfl
