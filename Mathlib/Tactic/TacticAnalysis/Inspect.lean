import Lean.Elab.Command
open Lean

namespace AdomaniUtils

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

end AdomaniUtils

namespace InspectSyntax

open AdomaniUtils Lean Elab Tactic

/-- Print out a `SourceInfo`. -/
def si : SourceInfo → MessageData
  | .original leading _pos trailing _endPos =>
    m!"original: ⟨{rmLB leading.toString}⟩⟨{rmLB trailing.toString}⟩"
  | .synthetic _pos _endPos canonical => m!"synthetic {canonical}"
  | .none => "none"

/--
`treeM stx` takes a `Syntax` and returns a pair consisting of
* `MessageData` for the non-`Syntax` arguments of `stx`,
* an array of the `Syntax` children of `stx`.
-/
def treeM : Syntax → MessageData × Array Syntax
  | .missing                 => default
  | .node info kind args     => (m!"node {.ofConstName kind}, {si info}", args)
  | .atom info val           => (m!"atom {si info}-- '{val}'", #[])
  | .ident info rawVal val _ => (m!"ident {si info}-- ({val},{rawVal.toString})", #[])

/-- `treeR ex` recursively formats the output of `treeM`. -/
partial
def treeR (stx : Syntax) (indent : MessageData := "\n") (sep : MessageData := "  ") :
    MessageData :=
  let (msg, es) := treeM stx
  let mes := es.map (treeR (indent := indent ++ sep) (sep := sep))
  mes.foldl (fun x y => (x.compose indent).compose ((m!"|-").compose y)) msg

/--
`viewTreeWithBars stx` is the default formatting of the output of `treeR stx` that
uses `| ` to separate nodes.
-/
def toMessageData (stx : Syntax) : MessageData := treeR stx (sep := "|   ")

/--
`inspect cmd` displays the tree structure of the `Syntax` of the command `cmd`.
-/
elab (name := inspectStx) "inspect " cmd:command : command => do
  logInfo (m!"inspect:\n---\n{cmd}\n---\n\n".compose (toMessageData cmd))
  Command.elabCommand cmd

/--
`inspect tacs` displays the tree structure of the `Syntax` of the tactic sequence `tacs`.
-/
elab (name := inspectTac) "inspect " tacs:tacticSeq : tactic => do
  logInfo (m!"inspect:\n---\n{tacs}\n---\n\n".compose (toMessageData tacs))
  evalTactic tacs

end InspectSyntax

section InspectIT

open AdomaniUtils Lean Elab Tactic

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
def ContextInfo.toMessageData : (pci : ContextInfo) → MetaM MessageData
    | ci =>
      return m!"{.ofConstName ``ContextInfo} {ci.parentDecl?.map MessageData.ofConstName}"

/-- Printing out a `Info`. -/
def Info.toMessageData : Info → MetaM MessageData
  | .ofTacticInfo ti         =>
    return m!"{.ofConstName ``ofTacticInfo}: {.ofConstName ti.elaborator}, {showStx ti.stx}"
  | .ofTermInfo ti           => do
    return m!"{.ofConstName ``ofTermInfo}: {.ofConstName ti.elaborator}, {showStx ti.stx}, {ti.expr}"
  | .ofPartialTermInfo ti    =>
    return m!"{.ofConstName ``ofPartialTermInfo}: {.ofConstName ti.elaborator}, {showStx ti.stx}, \
                                                                                {ti.expectedType?}"
  | .ofCommandInfo ci        =>
    return m!"{.ofConstName ``ofCommandInfo}: {.ofConstName ci.elaborator}, {showStx ci.stx}"
  | .ofMacroExpansionInfo me =>
    return m!"{.ofConstName ``ofMacroExpansionInfo}: {showStx me.stx} --> {me.output}"
  | .ofOptionInfo oi         =>
    return m!"{.ofConstName ``ofOptionInfo}: {oi.optionName}, {oi.declName}"
  | .ofFieldInfo fi          =>
    return m!"{.ofConstName ``ofFieldInfo}: {fi.projName}, {fi.fieldName}"
  | .ofCompletionInfo ci     =>
    return m!"{.ofConstName ``ofCompletionInfo}.{ci.ctor}"
  | .ofUserWidgetInfo _      =>
    return m!"{.ofConstName ``UserWidgetInfo}"
  | .ofCustomInfo ci         =>
    return m!"{.ofConstName ``ofCustomInfo}: {showStx ci.stx}"
  | .ofFVarAliasInfo fv      =>
    return m!"{.ofConstName ``ofFVarAliasInfo}: {fv.userName}, {fv.id.name}, {fv.baseId.name}"
  | .ofFieldRedeclInfo _     =>
    return m!"{.ofConstName ``FieldRedeclInfo}"
  | .ofDelabTermInfo _       =>
    return m!"{.ofConstName ``DelabTermInfo}"
  | .ofChoiceInfo ci         =>
    return m!"{.ofConstName ``ofChoiceInfo}: {.ofConstName ci.elaborator}, {showStx ci.stx}"
  | .ofDocElabInfo i =>
    return m!"{.ofConstName ``ofDocElabInfo}: {.ofConstName i.elaborator}, {showStx i.stx}"
  | .ofDocInfo i =>
    return m!"{.ofConstName ``ofDocInfo}: {.ofConstName i.elaborator}, {showStx i.stx}"
  | .ofErrorNameInfo i =>
    return m!"{.ofConstName ``ofErrorNameInfo}: {i.errorName} {showStx i.stx}"

def PartialContextInfo.toMessageData : PartialContextInfo → MetaM MessageData
  | commandCtx _ci => return m!"{.ofConstName ``commandCtx}"
  | parentDeclCtx parentDecl => return m!"parentDeclCtx {.ofConstName parentDecl}"
  | autoImplicitCtx .. => default

end Lean.Elab

namespace InspectInfoTree

/--
`treeM it` takes an `InfoTree` and returns a pair consisting of
* `MessageData` for the non-`InfoTree` arguments of `it`,
* an array of the `InfoTree` arguments to `it`.
-/
def treeM : InfoTree → MetaM (MessageData × Array InfoTree)
  | .context i t => return (← i.toMessageData, #[t])
  | .node i children => return (← i.toMessageData, children.toArray)
  | .hole mvarId => return (m!"hole {mvarId.name}", #[])

/-- `treeR it` recursively formats the output of `treeM`. -/
partial
def treeR (it : InfoTree) (indent : MessageData := "\n") (sep : MessageData := "  ") :
    MetaM MessageData := do
  let (msg, es) ← treeM it
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
