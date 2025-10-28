--import Mathlib.Tactic--.Linter.CommandStart
--import Mathlib.Tactic.Linter.DeprecatedSyntaxLinter
--import Batteries
import Mathlib.Tactic.MinImports
import Aesop
import Mathlib.adomaniLeanUtils.inspect_syntax

open Lean Elab Command
elab "repl " cmd:command : command => do
  let stx ← cmd.raw.replaceM fun s => do
    if s.isOfKind `Lean.Parser.Tactic.grind then
      logInfoAt s "Found grind!"
      let aesop := mkNode `Aesop.Frontend.Parser.aesopTactic #[mkAtom "aesop", mkNullNode]
      pure aesop
    else
      pure none
  elabCommand stx
  logInfo m!"{stx}"

/-- The `<` partial order on modules: `importLT env mod₁ mod₂` means that `mod₂` imports `mod₁`. -/
def importLT (env : Environment) (f1 f2 : Name) : Bool :=
  (env.findRedundantImports #[f1, f2]).contains f1

open Lean Elab Command Mathlib.Command.MinImports in
def printThm (cinfo : ConstantInfo) (bySorry? : Bool) : Meta.MetaM MessageData := do
  let declName := cinfo.name
  --let some f := (← getEnv).find? declName | throwError "The constant {declName} should exist..."
  let isProp ← Meta.isProp cinfo.type
  let cmdTxt := if isProp then "theorem" else "def"
  if cinfo.value?.isNone then logInfo m!"{.ofConstName declName} has no value!"
  let proof := if isProp && bySorry? then m!"by sorry" else m!"{cinfo.value! (allowOpaque := true)}"
  return m!"{cmdTxt} {← addMessageContext <| .signature declName} := {proof}"
  --let some proof :=
  --  cmd.raw.find? (#[``Parser.Command.declValEqns, ``Parser.Command.declValSimple].contains ·.getKind) |
  --    throwError "Add another kind of proof!"

open Lean Elab Command Mathlib.Command.MinImports in
elab "cst " cmd:command : command => do
  elabCommand cmd
  let env ← getEnv
  let id ← getId cmd
  --let some declId :=
  --  cmd.raw.find? (·.isOfKind ``Parser.Command.declId) | throwError "No declaration id!"
  let declName ← resolveGlobalConstNoOverload id
  let csts ← getAllDependencies cmd id
  let cstsAndMods : NameMap (Array Name)  ← csts.foldlM (init := ∅) fun tot decl => do
    if decl.isInternalDetail then return tot
    if (env.find? decl).isNone then return tot
    let mod := (← findModuleOf? decl).getD (← getMainModule)
    return tot.alter mod (·.getD #[] |>.push decl)
    --_
  let sorted := cstsAndMods.toArray.qsort (importLT env ·.1 ·.1)
  let mut msg := #[]
  for (mod, cs) in sorted do
    msg := msg.push m!"** {mod}"
    for c in cs do
      if c.isInternalDetail then continue
      let some cinfo := env.find? c | continue
      let mod := (← findModuleOf? c).getD (← getMainModule)
      if mod.getRoot == `Mathlib then
      --if c == `X.F then dbg_trace "found in {mod}"
        msg := msg.push m!"In {mod}" |>.push (← liftTermElabM <| printThm cinfo (c != declName)) |>.push ""
      --logInfo <| ← liftTermElabM <| printThm declName true
  logInfo <| m!"\n".joinSep msg.toList
/-
  let some f := (← getEnv).find? declName | throwError "The constant {declName} should exist..."
  let cmdTxt := if ← liftTermElabM do Meta.isProp f.type then "theorem" else "def"
  --logInfo m!"Name: `{declName}`, id: `{declId}`"
  let some proof :=
    cmd.raw.find? (#[``Parser.Command.declValEqns, ``Parser.Command.declValSimple].contains ·.getKind) |
      throwError "Add another kind of proof!"
  logInfo m!"{cmdTxt} {← addMessageContext <| .signature declName}{proof}"
  --logInfo m!"{cmd}"
  logInfo <| m!"{id}" ++
              m!"{csts.toArray.qsort (·.toString < ·.toString )}"
-/

namespace X
inspect
theorem E : True := by
  trivial

inspect
def E' : Nat → Unit
  | _ => ()

cst
theorem F : True := by exact E

cst
def F' : Nat → Unit | _ => E' 0

def bl := true

cst
def cp {cmd id} :=
  if bl then Mathlib.Command.MinImports.getAllDependencies cmd id else default

#check Std.Internal.Parsec.ByteArray.skipUntil
#exit
