--import Mathlib.Tactic--.Linter.CommandStart
--import Mathlib.Tactic.Linter.DeprecatedSyntaxLinter
--import Batteries
import Mathlib.Tactic.MinImports
import Aesop
import Mathlib.adomaniLeanUtils.inspect_syntax
import Mathlib.Tactic

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
  let cmdTxt :=
    if ← Meta.isInstance declName then "instance" else
      if isProp then "theorem" else "def"
  --if cinfo.value?.isNone then
  --  if (cinfo.value? (allowOpaque := true)).isNone then
  --    logInfo m!"{.ofConstName declName} has not even an opaque value!"
  --  else
  --    logInfo m!"{.ofConstName declName} has no value!"
  let cmdTxt := (if isNoncomputable (← getEnv) declName then "noncomputable " else "") ++ cmdTxt
  let proof :=
    if isProp && bySorry?
    then
      m!"by sorry"
    else
      ((cinfo.value? (allowOpaque := true)).map (m!"{·}")).getD m!"by sorry"
  return m!"{cmdTxt} {← addMessageContext <| .signature declName} := {proof}"
  --let some proof :=
  --  cmd.raw.find? (#[``Parser.Command.declValEqns, ``Parser.Command.declValSimple].contains ·.getKind) |
  --    throwError "Add another kind of proof!"
#check Meta.isInstance
open Lean Elab Command Mathlib.Command.MinImports in
elab "cst " cmd:command : command => do
  elabCommand cmd
  let env ← getEnv
  let id ← getId cmd
  --let some declId :=
  --  cmd.raw.find? (·.isOfKind ``Parser.Command.declId) | throwError "No declaration id!"
  let declName ← resolveGlobalConstNoOverload id
  let csts ← getAllDependencies cmd id
  --dbg_trace csts.toArray
  let cstsAndMods : NameMap (Array ConstantInfo)  ← csts.foldlM (init := ∅) fun tot decl => do
    if decl.isInternalDetail then return tot
    let some cinfo := env.find? decl | return tot
    let mod := (← findModuleOf? decl).getD (← getMainModule)
    if mod.getRoot != `Mathlib then return tot
    return tot.alter mod (·.getD #[] |>.push cinfo)
    --_
  let sorted := cstsAndMods.toArray.qsort (importLT env ·.1 ·.1)
  let dRanges := declRangeExt.getModuleEntries env
  --dbg_trace (dRanges.find? `Mathlib.Command.MinImports.getDeclName).map (·.range.pos)
  --if false then
  liftTermElabM do
  let mut msg := #[]
  for (mod, cs) in sorted do
    let dict : NameMap _ :=
      if let some modIdx := env.moduleIdxForModule? mod
      then
        Std.TreeMap.ofArray (cmp := Name.quickCmp) <| dRanges modIdx
      else
        declRangeExt.getState env
    msg := msg.push m!"/- From {mod} -/"
    let cs := cs.qsort fun d1 d2 : ConstantInfo =>
      match dict.find? d1.name, dict.find? d2.name with
      | some r1, some r2 =>
        r1.range.pos.line < r2.range.pos.line
      | none, none => dbg_trace "false {(d1.name, d2.name)}"; false
      | _, _ => dbg_trace "false"; false
      --| some _, _ => dbg_trace "false {d2.name}"; false
      --| _, some _ => dbg_trace "false {d1.name}"; false
    for cinfo in cs do
      --if c.isInternalDetail then continue
      --let some cinfo := env.find? c | continue
      --let mod := (← findModuleOf? c).getD (← getMainModule)
      --if mod.getRoot == `Mathlib then
      --if c == `X.F then dbg_trace "found in {mod}"
      msg := msg.push (← printThm cinfo (cinfo.name != declName)) |>.push ""
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
#print Group

#print axioms funext
#print sig Ring
#print equations Nat.add
run_cmd
  let stx ← `(command| /-- -/ class Group where mul : Unit)
  --dbg_trace stx.raw[0]
  dbg_trace stx.raw[1]
  dbg_trace ""
  dbg_trace stx.raw[1][0]
  dbg_trace ""
  dbg_trace stx.raw[1][1]
  dbg_trace ""
  --elabPrintSig (mkNode `def #[mkIdent `hi, mkIdent `hi, mkIdent `Group])
  elabPrintEqns (mkNode `def #[mkIdent `hi, mkIdent `hi, mkIdent `Nat.add])
namespace F
class Group.{u} (G : Type u) extends
--number of parameters: 1
--parents:
  --Group.toDivInvMonoid :
  DivInvMonoid G where
--fields:
  --mul : G → G → G
  --mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c)
  --one : G
  --one_mul : ∀ (a : G), 1 * a = a
  --mul_one : ∀ (a : G), a * 1 = a
  npow :=
    npowRecAuto
  npow_zero := by
    intros; rfl
  npow_succ := by
    intros; rfl
  --inv : G → G
  div := DivInvMonoid.div'
  div_eq_mul_inv := by
    intros; rfl
  zpow :=
    zpowRec
  zpow_zero' := by
    intros; rfl
  zpow_succ' := by
    intros; rfl
  zpow_neg' := by
    intros; rfl
  inv_mul_cancel : ∀ (a : G), a⁻¹ * a = 1
--constructor:
--  Group.mk.{u} {G : Type u} [toDivInvMonoid : DivInvMonoid G] (inv_mul_cancel : ∀ (a : G), a⁻¹ * a = 1) : Group G
--

#check DivInvMonoid.toMonoid
#check _root_.Group
cst
theorem ga {G} [Group G] {g : G} : g * 1 = g := mul_one g

#check Polynomial.natDegree_add_eq_left_of_degree_lt

cst
theorem X.{u} {R : Type u} [Semiring R] {p q : Polynomial R}
    (h : q.degree < p.degree) : (p + q).natDegree = p.natDegree :=
  Polynomial.natDegree_add_eq_left_of_degree_lt h

#exit
cst
def mR := Group
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
