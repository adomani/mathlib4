import Lean.Meta.Tactic.TryThis
import Mathlib.adomaniLeanUtils.inspect_syntax
import Mathlib.Tactic.Linter.CommandStart

open Lean Elab Command Mathlib Linter Style.CommandStart in
elab tk:"#reformat " cmd:command : command => do
  let tktxt := "#reformat"
  if let some cmdSubstring := cmd.raw.getSubstring? then
  if let .error .. :=
    captureException (← getEnv) Parser.topLevelCommandParserFn cmd.raw.getSubstring?.get!.toString
  then
    logWarningAt tk m!"{tktxt}: Parsing failed"
    return
  elabCommand cmd
  if (← get).messages.hasErrors then
    logWarningAt tk m!"{tktxt}: Command has errors"
    return
  match ← getExceptions (verbose? := false) cmd with
  | none => logWarningAt tk m!"{tktxt} internal error!"
  | some mex =>
    let (reported, _) := reportedAndUnreportedExceptions mex
    if reported.isEmpty then
      logInfoAt tk "All is good!"
      return
    let parts := mkStrings cmdSubstring (reported.map (·.rg.start))
    let reformatted := parts.foldl (· ++ ·.toString) ""
    liftTermElabM do Meta.liftMetaM do Lean.Meta.Tactic.TryThis.addSuggestion cmd reformatted

open Lean Elab Command in
elab "#getRange " st:str ppSpace cmd:command : command => do
  elabCommand cmd
  let str := st.getString
  match cmd.raw.find? fun x => 2 ≤ (x.getKind.toString.splitOn str).length with
  | none => logWarningAt st m!"{st} is not present"
  | some s =>
    let fm ← getFileMap
    let rg := s.getRange?.getD st.raw.getRange?.get!
    logInfoAt s m!"'{s}': {(fm.toPosition rg.start, fm.toPosition rg.stop)}"

open Lean Elab Command in
elab "#pp " cmd:command : command => do
  elabCommand cmd
  let noSpaces := cmd.raw.eraseLeadTrailSpaces
  let pretty ← Mathlib.Linter.pretty noSpaces
  logInfo m!"{pretty}"

#pp
#getRange "tacticSeqBracketed"
--#getRange "ident"
--#getRange "type"
#getRange "DeclSi"
--#getRange "declVal"
inspect
example : True := by  {trivial }
