import Lean.Elab.Command
open Lean

namespace InspectGeneric

partial
def printMe {α} (printNode : α → MessageData) (recurse : α → Option (Array α)) (a : α) :
    MessageData :=
  let recs : Option (Array MessageData) := (recurse a).map (·.map (printMe printNode recurse))
  let msgs := #[printNode a] ++ recs.getD #[]
  m!"\n".joinSep msgs.toList

partial
def treeR {α} (printNode : α → MessageData) (recurse : α → Array α) (stx : α)
    (sep : MessageData := "\n") (indent : MessageData := "  ") :
    MessageData :=
  let (msg, es) := (printNode stx, recurse stx)
  let mes := es.map (treeR (sep := sep ++ indent) (indent := indent) printNode recurse)
  mes.foldl (fun x y => (x.compose sep).compose ((m!"|-").compose y)) msg

/-- The brackets corresponding to a given `BinderInfo`. Copied from `Mathlib.Lean.Expr.Basic`. -/
def bracks : BinderInfo → String × String
  | .implicit       => ("{", "}")
  | .strictImplicit => ("{{", "}}")
  | .instImplicit   => ("[", "]")
  | _               => ("(", ")")

/-- replaces line breaks with the literal string `⟨['\', 'n']⟩`
for better formatting of syntax that includes line breaks.
-/
def rmLB (s : String) : String :=
  s.replace "\n" "⏎"

#eval show Elab.Term.TermElabM _ from do
  guard ("hi⏎⏎" == rmLB "hi\n
")

/--
`showStx stx replaceLineBreaks flapLth` is a string representation of `stx` that shows at most
`flapLth` characters on either side of the string.

If `replaceLineBreaks` is `true`, then line breaks are replaced with `⏎` and the whole string
is enclosed in `'`.

If `flapLth` is `0`, then the entire string is shown.
-/
def showStx (stx : Syntax) (replaceLineBreaks : Bool := true) (flapLth : Nat := 10) : String :=
  let cand := stx.getSubstring?.getD default |>.toString.trim
  let cand := if replaceLineBreaks then rmLB cand else cand
  let tick := if replaceLineBreaks then "'" else ""
  if flapLth != 0 && 2 * flapLth + 1 < cand.length then
    s!"{tick}{cand.take flapLth}…{cand.takeRight flapLth}{tick}"
  else
    s!"{tick}{cand}{tick}"

end InspectGeneric

namespace InspectSyntax

open InspectGeneric Lean Elab Command

/-- Print out a `SourceInfo`. -/
def si : SourceInfo → MessageData
  | .original leading _pos trailing _endPos =>
    m!"{.ofConstName ``SourceInfo.original}: ⟨{rmLB leading.toString}⟩⟨{rmLB trailing.toString}⟩"
  | .synthetic _pos _endPos canonical => m!"{.ofConstName ``SourceInfo.synthetic} {canonical}"
  | .none => m!"{.ofConstName ``SourceInfo.none}"

def preRes : Syntax.Preresolved → MessageData
  | .namespace ns => m!"{ns.eraseMacroScopes}"
  | .decl name fields => m!"{name.eraseMacroScopes}: {fields}"

def printNode : Syntax → MessageData
  | .node info kind .. => m!"{.ofConstName ``Syntax.node} {.ofConstName kind}, {si info}"
  | .atom info val => m!"{.ofConstName ``Syntax.atom} {si info}-- '{val}'"
  | .ident info rawVal val pr => m!"{.ofConstName ``Syntax.ident} {si info}-- ({rawVal},{val.eraseMacroScopes}) -- {pr.map preRes}"
  | .missing => m!"{.ofConstName ``Syntax.missing}"

/--
`toMessageData stx` is the default formatting of the output of `treeR stx` that
uses `| ` to separate nodes.
-/
def toMessageData (stx : Syntax) (indent : String := "|   ") : MessageData :=
  treeR InspectSyntax.printNode Syntax.getArgs stx (indent := indent)

/--
`inspect_syntax cmd` displays the tree structure of the `Syntax` of the command `cmd`.
-/
elab (name := inspectStx) "inspect_syntax " cpct:("compact ")? cmd:command : command => do
  let msg := if cpct.isSome then toMessageData cmd "| " else toMessageData cmd
  logInfo (m!"inspect syntax:\n---\n{cmd}\n---\n\n".compose msg)
  Command.elabCommand cmd

/--
`inspect_syntax tacs` displays the tree structure of the `Syntax` of the tactic sequence `tacs`.
-/
elab (name := inspectTac) "inspect_syntax " tacs:tacticSeq : tactic => do
  logInfo (m!"inspect syntax:\n---\n{tacs}\n---\n\n".compose (toMessageData tacs))
  Tactic.evalTactic tacs

end InspectSyntax

namespace Lean.Expr

open InspectGeneric

def recurse : Expr → Array Expr
  | ex@(.app ..)        => ex.getAppArgs
  | .lam _na t b _i     => #[t, b]
  | .forallE _na t b _i => #[t, b]
  | .letE _na t v b _i  => #[t, v, b]
  | .mdata _md e        => #[e]
  | .proj _na _id e     => #[e]
  | _ => #[]

def printNode (ctor? : Bool) (e : Expr) : MessageData :=
  let ctorN := if ctor? then m!" -- {e.ctorName}" else m!""
  (match e with
  | .bvar n                 => m!"'{n}'"
  | .fvar fv                => m!"'{fv.name}'"
  | .mvar mv                => m!"'{mv.name}'"
  | .sort u                 => m!"'{u}'"
  | .const na lv            => m!"'{na}' '{lv}'"
  | ex@(.app ..)            => m!"'{.ofConstName ex.getAppFn.constName}'"
  | .lam na _t _b i         => m!"{(bracks i).1}'{na}'{(bracks i).2}"
  | .forallE na _t _b i     => m!"{(bracks i).1}'{na}'{(bracks i).2}"
  | .letE na t v b i        => m!"'{na}' {t} {v} {b} {i}"
  | .lit (Literal.natVal n) => m!"'{n}'"
  | .lit (Literal.strVal n) => m!"'{n}'"
  | .mdata md e             => m!"'{md}' '{e}'"
  | .proj na id e           => m!"'{.ofConstName na}' {id} {e}") ++ ctorN

/-- `Lean.Expr.mle? p` take `e : Expr` as input.
If `e` represents `a ≤ b`, then it returns `some (t, a, b)`, where `t` is the Type of `a`,
otherwise, it returns `none`. -/
@[inline] def mle? (p : Expr) : Option (Expr × Expr × Expr) := do
  let (type, _, lhs, rhs) ← p.app4? ``LE.le
  pure (type, lhs, rhs)

/-- `Lean.Expr.mlt? p` take `e : Expr` as input.
If `e` represents `a < b`, then it returns `some (t, a, b)`, where `t` is the Type of `a`,
otherwise, it returns `none`. -/
@[inline] def mlt? (p : Expr) : Option (Expr × Expr × Expr) := do
  let (type, _, lhs, rhs) ← p.app4? ``LT.lt
  pure (type, lhs, rhs)

/-- `lhsrhs ex` returns the Type, lhs, rhs of `ex`, assuming that `ex` is of one of the forms
`a = b`, `a ≠ b`, `a ≤ b`, `a < b`. -/
def lhsrhs (ex : Expr) : Option (Expr × Expr × Expr) :=
  if let some x := ex.eq?  then x else
  if let some x := ex.ne?  then x else
  if let some x := ex.mle? then x else
  if let some x := ex.iff? then some (default, x) else
  if let some x := ex.and? then some (default, x) else
  if let .mdata _ e := ex  then lhsrhs e else
  ex.mlt?

end Lean.Expr

namespace InspectExpr
open Lean Elab Tactic Expr InspectGeneric
/-- `toMessageData ex` recursively formats the output of `treeM`. -/
partial
def Expr.toMessageData (ex : Expr)
    (ctor? : Bool := true) (sep : MessageData := "\n") (indent : MessageData := "|   ") :
    MessageData :=
  treeR (Expr.printNode ctor?) Expr.recurse ex (indent := indent) (sep := sep)

def inspectM {m : Type → Type} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (ex : Expr) (ctor? : Bool := true) (sep : MessageData := "\n") (indent : MessageData := "|   ") :
    m Unit :=
  logInfo <|
    m!"inspect: '{ex}'\n\n" ++ Expr.toMessageData ex ctor? (indent := indent) (sep := sep)

/-- `inspect id?` displays the tree structure of the `Expr`ession in the goal.
If the optional identifier `id?` is passed, then `inspect` shows the tree-structure for the
`Expr`ession at the given identifier.

The variants `inspect_lhs` and `inspect_rhs` do what you imagine, when the goal is
`a = b`, `a ≠ b`, `a ≤ b`, `a < b`.
-/
elab (name := tacticInspect) "inspect" bang:(colGt ppSpace ident)? : tactic => withMainContext do
  let expr := ← match bang with
    | none => getMainTarget
    | some id => do
      let loc := ← Term.elabTerm id none
      let some decl := (← getLCtx).findFVar? loc | throwError m!"not found"
      pure decl.type
  inspectM expr

@[inherit_doc tacticInspect]
elab "inspect_lhs" : tactic => withMainContext do focus do
  let some (_, x, _) := lhsrhs (← getMainTarget) | throwError "Try 'inspect'"
  inspectM x

@[inherit_doc tacticInspect]
elab "inspect_rhs" : tactic => withMainContext do focus do
  let some (_, _, x) := lhsrhs (← getMainTarget) | throwError "Try 'inspect'"
  inspectM x

end InspectExpr

section InspectIT

open InspectGeneric Lean Elab Tactic

def Array.display {α} [ToString α] (a : Array α) (sep : String := "\n  ") : String :=
  if a.isEmpty then "∅" else
  sep.intercalate (""::(a.map (s!"{·}")).toList)

namespace Lean.Elab

/-- Printing out a `CompletionInfo`. -/
def CompletionInfo.ctor : CompletionInfo → MessageData
  | .dot ti eType?      => m!"{.ofConstName ``dot} {.ofConstName ti.elaborator}, {ti.stx}, {eType?}"
  | .id name nm _ _ e?  => m!"{.ofConstName ``id} {name} '{nm.eraseMacroScopes}' {e?}"  -- `eraseMacroScopes` fixes tests
  | .dotId _ nm _ e?    => m!"{.ofConstName ``dotId} '{.ofConstName nm}' {e?}"
  | .fieldId _ nm? _ sn => m!"{.ofConstName ``fieldId} '{nm?.map MessageData.ofConstName}' '{sn}'"
  | .namespaceId stx    => m!"{.ofConstName ``namespaceId} {showStx stx}"
  | .option stx         => m!"{.ofConstName ``option} {showStx stx}"
  | .errorName sn pid   => m!"{.ofConstName ``errorName} stx: '{sn}' pid '{pid}'"
  | .endSection stx _id? _ sn => m!"{.ofConstName ``endSection} {sn} '{showStx stx}'"
  | .tactic stx         => m!"{.ofConstName ``tactic} {showStx stx}"

/-- Printing out a `PartialContextInfo`. -/
def ContextInfo.toMessageData : (pci : ContextInfo) → MessageData
    | ci =>
      m!"{.ofConstName ``ContextInfo} {ci.parentDecl?.map MessageData.ofConstName}"

/-- Printing out a `Info`. -/
def Info.toMessageData : Info → MessageData
  | .ofTacticInfo ti         =>
    m!"{.ofConstName ``ofTacticInfo}: {.ofConstName ti.elaborator}, {showStx ti.stx}"
  | .ofTermInfo ti           =>
    m!"{.ofConstName ``ofTermInfo}: {.ofConstName ti.elaborator}, {showStx ti.stx}, {ti.expr}"
  | .ofPartialTermInfo ti    =>
    m!"{.ofConstName ``ofPartialTermInfo}: {.ofConstName ti.elaborator}, {showStx ti.stx}, \
                                                                                {ti.expectedType?}"
  | .ofCommandInfo ci        =>
    m!"{.ofConstName ``ofCommandInfo}: {.ofConstName ci.elaborator}, {showStx ci.stx}"
  | .ofMacroExpansionInfo me =>
    m!"{.ofConstName ``ofMacroExpansionInfo}: {showStx me.stx} --> {me.output}"
  | .ofOptionInfo oi         =>
    m!"{.ofConstName ``ofOptionInfo}: {oi.optionName}, {oi.declName}"
  | .ofFieldInfo fi          =>
    m!"{.ofConstName ``ofFieldInfo}: {fi.projName}, {fi.fieldName}"
  | .ofCompletionInfo ci     =>
    m!"{.ofConstName ``ofCompletionInfo}.{ci.ctor}"
  | .ofUserWidgetInfo _      =>
    m!"{.ofConstName ``UserWidgetInfo}"
  | .ofCustomInfo ci         =>
    m!"{.ofConstName ``ofCustomInfo}: {showStx ci.stx}"
  | .ofFVarAliasInfo fv      =>
    m!"{.ofConstName ``ofFVarAliasInfo}: {fv.userName}, {fv.id.name}, {fv.baseId.name}"
  | .ofFieldRedeclInfo _     =>
    m!"{.ofConstName ``FieldRedeclInfo}"
  | .ofDelabTermInfo _       =>
    m!"{.ofConstName ``DelabTermInfo}"
  | .ofChoiceInfo ci         =>
    m!"{.ofConstName ``ofChoiceInfo}: {.ofConstName ci.elaborator}, {showStx ci.stx}"
  | .ofDocElabInfo i =>
    m!"{.ofConstName ``ofDocElabInfo}: {.ofConstName i.elaborator}, {showStx i.stx}"
  | .ofDocInfo i =>
    m!"{.ofConstName ``ofDocInfo}: {.ofConstName i.elaborator}, {showStx i.stx}"
  | .ofErrorNameInfo i =>
    m!"{.ofConstName ``ofErrorNameInfo}: {i.errorName} {showStx i.stx}"

def PartialContextInfo.toMessageData : PartialContextInfo → MessageData
  | commandCtx _ci => m!"{.ofConstName ``commandCtx}"
  | parentDeclCtx parentDecl => m!"parentDeclCtx {.ofConstName parentDecl}"
  | autoImplicitCtx .. => default

end Lean.Elab

namespace InspectInfoTree

/--
`treeM it` takes an `InfoTree` and returns a pair consisting of
* `MessageData` for the non-`InfoTree` arguments of `it`,
* an array of the `InfoTree` arguments to `it`.
-/
def treeM : InfoTree → (MessageData × Array InfoTree)
  | .context i t => (i.toMessageData, #[t])
  | .node i children => (i.toMessageData, children.toArray)
  | .hole mvarId => (m!"hole {mvarId.name}", #[])

def printNode : InfoTree → MessageData
  | .context i t => i.toMessageData
  | .node i children => i.toMessageData
  | .hole mvarId => m!"hole {mvarId.name}"

def treeM : InfoTree → (MessageData × Array InfoTree)
  | .context i t => (i.toMessageData, #[t])
  | .node i children => (i.toMessageData, children.toArray)
  | .hole mvarId => (m!"hole {mvarId.name}", #[])

/-- `treeR it` recursively formats the output of `treeM`. -/
partial
def treeR (it : InfoTree) (indent : MessageData := "\n") (sep : MessageData := "  ") :
    MetaM MessageData := do
  let (msg, es) := treeM it
  let mes ← es.mapM (treeR (indent := indent ++ sep) (sep := sep))
  return mes.foldl (fun x y => (x.compose indent).compose ((m!"|-").compose y)) msg

/--
`toMessageData it` is the default formatting of the output of `treeR it` that
uses `| ` to separate nodes.
-/
def toMessageData (it : InfoTree) : MetaM MessageData := treeR it (sep := "|   ")

/-- `inspectIT cmd` displays the tree structure of the `InfoTree` when elaborating `cmd`. -/
elab (name := inspectITStx) "inspectIT " cmd:command : command => do
  Command.elabCommand cmd
  let its ← getInfoTrees
  let itsMsgs : Array MessageData ← Command.liftTermElabM do Meta.liftMetaM do
    its.foldlM (init := ∅) fun a b => do
      let b' ← toMessageData b
      return (a.push b')
  logInfo (.joinSep (m!"inspectIT:\n---\n{showStx cmd false 0}\n---" :: itsMsgs.toList) "\n\n")

end InspectInfoTree

end InspectIT
