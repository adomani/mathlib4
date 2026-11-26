/-
Copyright (c) 2026 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public meta import Lean.Meta.Tactic.Rfl
public meta import Mathlib.Lean.Expr.Basic
public meta import Mathlib.Lean.Meta

/-!
# The `@[compute_degree]` attribute and the core of `compute_degree`

This file contains the part of `compute_degree` that does not know anything about polynomials:
an attribute `@[compute_degree]` that stores lemmas in a discrimination tree, and the function
`step?`, that finds and applies a stored lemma to a goal.

The notion of "degree" that `compute_degree` computes is not hard-coded: it is determined by the
lemmas tagged with `@[compute_degree]`.  There is a single attribute, and the role of each tagged
lemma is read off its statement.

* A **relaxation lemma** is a lemma with a hypothesis that coincides with its conclusion, except
  for some positions where both contain distinct variables.  These positions are the *outputs* of
  the degree computation.  For instance,
  ```lean
  theorem natDegree_le_of_le_of_le (h : natDegree f ≤ m) (hmn : m ≤ n) : natDegree f ≤ n
  theorem coeff_congr (h : coeff f m = r) (natDeg_eq_coeff : m = n) {s : R} (rs : r = s) :
      coeff f n = s
  ```
  declare that the output of `natDegree _ ≤ _` is its right-hand side and that the outputs of
  `coeff _ _ = _` are the index and the right-hand side.  Everything else (the polynomial, and
  any parameter that the two statements share) is an *input*.
  A relaxation lemma is applied to a goal whose outputs are not all metavariables: this turns the
  outputs of the main goal into metavariables, leaving side goals that relate them to the
  original outputs.
* Every **other lemma** is applied to a goal whose conclusion it matches.  This covers the lemmas
  that recurse into the structure of the polynomial (`natDegree_add_le_of_le`), the leaves
  (`natDegree_X_le`), lemmas that apply to any polynomial and therefore act as fallbacks
  (`natDegree f ≤ natDegree f`) and "entry" lemmas, whose conclusion has a shape different from
  their hypotheses (`natDegree f = d` from `natDegree f ≤ m` and `coeff f d ≠ 0`).

When several lemmas match a goal, the most specific ones are tried first, where specificity only
takes into account the positions of the goal that are not metavariables.  In particular, lemmas
about a specific head symbol of the polynomial are tried before fallback lemmas.

## Implementation notes

The `DiscrTree` lookup uses `getUnify`, so that metavariables in the outputs of a goal match
anything.  To avoid matching metavariables that are not outputs, a goal is only passed to the
non-relaxation lemmas if either
* a relaxation lemma matches it, all its outputs are metavariables and its inputs contain no
  metavariables, or
* the goal contains no metavariables at all.

The `DiscrTree` collapses numerals `OfNat.ofNat α n _` to the literal `n`, regardless of `α`.
To be able to register lemmas about numerals in a specific type, such as
`natDegree (OfNat.ofNat n : R[X]) ≤ 0`, both the keys of the lemmas and the queries are computed
after rewriting numerals so that their keys record `OfNat.ofNat`, the type and then the literal.

To keep the cost of a lookup independent of the size of the polynomial, the query is truncated
below the depth of the deepest stored key, and the specificity of a matching lemma is computed by
inspecting only the subterms of the goal where the lemma has a key that is not a wildcard.
-/

public meta section

namespace Mathlib.Tactic.ComputeDegree

open Lean Meta

/-- A lemma tagged with `@[compute_degree]`. -/
structure DegreeLemma where
  /-- The name of the lemma. -/
  declName : Name
  /-- The `DiscrTree` keys of the conclusion of the lemma. -/
  keys : Array DiscrTree.Key
  /-- For a relaxation lemma, the pairs `(i, j)` of positions in the telescope of the lemma
  such that the `i`-th variable appears in the main hypothesis exactly where the `j`-th variable
  appears in the conclusion.  The array is empty if and only if the lemma is not a relaxation
  lemma. -/
  outputs : Array (Nat × Nat)
  deriving Inhabited, BEq

/-- The lemmas tagged with `@[compute_degree]`. -/
structure DegreeLemmas where
  /-- The discrimination tree of the `@[compute_degree]` lemmas, keyed by their conclusions. -/
  tree : DiscrTree DegreeLemma := {}
  /-- The maximum depth of the keys of the lemmas in `tree`: the `DiscrTree` never inspects the
  subterms of a goal that are deeper than this. -/
  maxDepth : Nat := 0
  deriving Inhabited

/-- The depth of the tree described by the `DiscrTree` keys `ks`, where a single key has depth
`0`. -/
partial def keysDepth (ks : List DiscrTree.Key) : Nat :=
  (go ks).1
where
  /-- Return the depth of the subtree described by the first keys of `ks` and the remaining
  keys. -/
  go : List DiscrTree.Key → Nat × List DiscrTree.Key
    | [] => (0, [])
    | k :: ks => Id.run do
      let mut rest := ks
      let mut depth := 0
      for _ in [0:k.arity] do
        let (d, r) := go rest
        depth := max depth (d + 1)
        rest := r
      return (depth, rest)

/-- Environment extension for the `@[compute_degree]` lemmas. -/
initialize computeDegreeExt : SimpleScopedEnvExtension DegreeLemma DegreeLemmas ←
  registerSimpleScopedEnvExtension {
    addEntry := fun d l =>
      { tree := d.tree.insertKeyValue l.keys l
        maxDepth := max d.maxDepth (keysDepth l.keys.toList) }
    initial := {}
  }

/-- `truncate w d e` replaces by `w` the applications in `e` that are at depth more than `d`,
where the depth increases along the arguments of applications.

`compute_degree` only computes the `DiscrTree` keys of the truncation of a goal, so that the cost
of finding the relevant lemmas does not depend on the size of the polynomial. -/
partial def truncate (w : Expr) : Nat → Expr → Expr
  | d, .mdata m e => .mdata m (truncate w d e)
  | 0, .app .. => w
  | d + 1, e@(.app ..) => e.withApp fun f args => mkAppN f (args.map (truncate w d))
  | _, e => e

/-- `canonNumerals e` rewrites the numerals `OfNat.ofNat α n _` in `e` so that their
`DiscrTree` keys are `OfNat.ofNat`, followed by the keys of `α` and of `n`.  Without this, the
`DiscrTree` would collapse them to the literal `n`, forgetting the type `α`.

It also removes the `no_index` annotations around `OfNat.ofNat`, so that a lemma stated with
`ofNat(n)` does not end up with a key that matches every term. -/
def canonNumerals (e : Expr) : Expr :=
  e.replace fun e =>
    let e' := e.consumeMData
    if !e'.isAppOfArity ``OfNat.ofNat 3 then none
    else match e'.numeral? with
      -- The `mdata` prevents `DiscrTree.mkPath` from treating the whole term as a literal.
      | some n => some <| mkApp3 e'.getAppFn (e'.getArg! 0) (mkMData {} (mkRawNatLit n))
          (e'.getArg! 2)
      | none => some e'

/-- The `DiscrTree` keys of `e`, after normalising its numerals with `canonNumerals`. -/
def mkKeys (e : Expr) : MetaM (Array DiscrTree.Key) :=
  DiscrTree.mkPath (canonNumerals e)

/-- `diffMVars a b` compares the expressions `a` and `b`, assumed to have their metavariables
instantiated.  If they agree except at some positions where both contain metavariables, it
returns the pairs of metavariables at these positions.  Otherwise, it returns `none`. -/
partial def diffMVars (a b : Expr) : Option (Array (Expr × Expr)) :=
  if a == b then some #[]
  else if a.isMVar && b.isMVar then some #[(a, b)]
  else if a.isApp && b.isApp && a.getAppNumArgs == b.getAppNumArgs &&
      a.getAppFn == b.getAppFn then
    (a.getAppArgs.zip b.getAppArgs).foldlM (init := #[]) fun acc (x, y) =>
      (acc ++ ·) <$> diffMVars x y
  else none

/-- `relaxOutputs xs concl` determines whether the lemma whose telescope consists of `xs`
and whose conclusion is `concl` is a relaxation lemma.  If it is, it returns the outputs of the
lemma, as described in `DegreeLemma.outputs`.  Otherwise, it returns the empty array. -/
def relaxOutputs (xs : Array Expr) (concl : Expr) : MetaM (Array (Nat × Nat)) := do
  let concl ← instantiateMVars concl
  for x in xs do
    let hyp ← instantiateMVars (← inferType x)
    unless ← isProp hyp do continue
    let some pairs := diffMVars hyp concl | continue
    if pairs.isEmpty then continue
    let some outputs := pairs.mapM fun (h, c) => do
        let i ← xs.idxOf? h
        let j ← xs.idxOf? c
        guard (i != j)
        return (i, j)
      | continue
    return outputs
  return #[]

/-- Register `declName` as a `@[compute_degree]` lemma. -/
def addDegreeLemma (declName : Name) (kind : AttributeKind) : MetaM Unit := do
  let info ← getConstInfo declName
  let (xs, _, concl) ← forallMetaTelescope info.type
  let keys ← mkKeys concl
  let outputs ← relaxOutputs xs concl
  trace[Tactic.compute_degree] "'{declName}' is {if outputs.isEmpty then "an" else "a relaxation"} \
    '@[compute_degree]' lemma, with keys {keys}"
  computeDegreeExt.add { declName, keys, outputs } kind
  unless kind == .local do recordExtraRevUseOfCurrentModule

/--
`@[compute_degree]` registers a lemma for use by the `compute_degree` tactic.

There is a single attribute: how `compute_degree` uses a lemma is determined by its statement.
* A lemma with a hypothesis that coincides with the conclusion, except for some positions where
  both contain distinct variables, is a *relaxation lemma*.  It declares that these positions are
  the outputs of the degree computation.  For instance,
  `natDegree f ≤ m → m ≤ n → natDegree f ≤ n` declares that the output of `natDegree _ ≤ _` is
  its right-hand side.
* Every other lemma is applied to the goals that match its conclusion, the most specific ones
  first.
-/
syntax (name := computeDegreeAttr) "compute_degree" : attr

initialize registerTraceClass `Tactic.compute_degree

@[inherit_doc computeDegreeAttr]
initialize registerBuiltinAttribute {
  name := `computeDegreeAttr
  descr := "a lemma used by the `compute_degree` tactic"
  add := fun declName _ kind => MetaM.run' <| addDegreeLemma declName kind
}

/-- `keyArgs e root` is the `DiscrTree` key of `e`, together with the arguments of `e` that
correspond to the children of the key, as computed by `mkKeys`.

Unlike `DiscrTree.mkPath`, it does not determine which arguments of `e` are not indexed: this
does not matter for `matchScore`, since the keys of these arguments are `.star` in the lemmas. -/
def keyArgs (e : Expr) (root : Bool) : MetaM (DiscrTree.Key × List Expr) := do
  let e ← DiscrTree.reduceDT e root
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := e.numeral? then
      return (.const ``OfNat.ofNat 3, [e.getArg! 0, mkRawNatLit n, e.getArg! 2])
  match e.getAppFn with
  | .lit v => return (.lit v, [])
  | .const c _ => return (.const c e.getAppNumArgs, e.getAppArgs.toList)
  | .fvar f => return (.fvar f e.getAppNumArgs, e.getAppArgs.toList)
  | .mvar _ => return (.star, [])
  -- As in `DiscrTree.mkPath`, the arguments of a projection come before the structure.
  | .proj s i a => return (.proj s i e.getAppNumArgs, e.getAppArgs.toList ++ [a])
  | .forallE _ d _ _ => return (.arrow, [d])
  | _ => return (.other, [])

/-- `matchScore keys tgt` is the number of positions where the `DiscrTree` keys `keys` of a
lemma and the keys of the goal `tgt` coincide and neither is a wildcard.

This measures how specific a lemma is for a goal, ignoring the positions where the goal has a
metavariable.  Only the subterms of `tgt` where `keys` is not a wildcard are inspected. -/
partial def matchScore (keys : List DiscrTree.Key) (tgt : Expr) : MetaM Nat :=
  withReducible <| go keys [tgt] true 0
where
  /-- Drop `n` complete subterms from the list of keys `ks`. -/
  skip : Nat → List DiscrTree.Key → List DiscrTree.Key
    | 0, ks => ks
    | _, [] => []
    | n + 1, k :: ks => skip (n + k.arity) ks
  /-- The main loop of `matchScore`. -/
  go : List DiscrTree.Key → List Expr → Bool → Nat → MetaM Nat
    | [], _, _, n | _, [], _, n => return n
    | .star :: ks, _ :: es, _, n => go ks es false n
    | k :: ks, e :: es, root, n => do
      let (k', args) ← keyArgs e root
      if k' == .star then go (skip k.arity ks) es false n
      else if k' == k then go ks (args ++ es) false (n + 1)
      else return n

/-- `matchRelax? lems tgt` looks for a relaxation lemma in `lems` whose conclusion unifies with
`tgt` without assigning metavariables of `tgt` and such that the inputs of `tgt` contain no
metavariables.  If it finds one, it returns the lemma, together with the array recording which
outputs of `tgt` are metavariables. -/
def matchRelax? (lems : Array DegreeLemma) (tgt : Expr) :
    MetaM (Option (DegreeLemma × Array Bool)) := do
  for lem in lems do
    let res? ← withNewMCtxDepth do
      let (xs, _, concl) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels
        lem.declName))
      unless ← isDefEq concl tgt do return none
      let outputs := lem.outputs.map (·.2)
      for h : i in [:xs.size] do
        if outputs.contains i then continue
        let x := xs[i]
        if (← x.mvarId!.isAssigned) && (← instantiateMVars x).hasExprMVar then return none
      return some (← outputs.mapM fun j => return (← instantiateMVars xs[j]!).isMVar)
    if let some isMVar := res? then return some (lem, isMVar)
  return none

/-- What `compute_degree` does with a goal: either apply a relaxation lemma, or try the given
lemmas in order. -/
inductive Action where
  /-- Apply the relaxation lemma. -/
  | relax (lem : DegreeLemma)
  /-- Apply the first lemma that succeeds. -/
  | apply (lems : List DegreeLemma)

/-- `getAction? g` determines what `compute_degree` should do with the goal `g`, if anything.
It also returns the target of `g` for which it made this decision. -/
def getAction? (g : MVarId) : MetaM (Option (Expr × Action)) := g.withContext do
  if ← g.isAssigned then return none
  let tgt ← g.getType''
  let lems := computeDegreeExt.getState (← getEnv)
  -- Replacing subterms by a metavariable can only add lemmas to the ones returned by `getUnify`,
  -- and the replaced subterms are deeper than all the keys in `lems.tree`.
  let cands ← withoutModifyingState do
    let tgt' := truncate (← mkFreshExprMVar none) (lems.maxDepth + 1) tgt
    lems.tree.getUnify (canonNumerals tgt')
  let (relax, others) := cands.partition (!·.outputs.isEmpty)
  let isDegreeGoal ← match ← matchRelax? relax tgt with
    | some (lem, isMVar) => if isMVar.all id then pure true else return some (tgt, .relax lem)
    | none => pure false
  unless isDegreeGoal || !tgt.hasExprMVar do return none
  if others.isEmpty then return none
  let scored ← others.toList.mapM fun l => return (← matchScore l.keys.toList tgt, l)
  return some (tgt, .apply <| (scored.mergeSort (·.1 ≥ ·.1)).map (·.2))

/-- After applying a relaxation lemma, the outputs that were already metavariables give rise to
side goals `?a ~ ?b`, where `?a` is one of the new goals `gs`.  `closeMVarRels gs` assigns `?a`
to `?b` and closes these side goals by reflexivity.  It returns the goals in `gs` that are still
unassigned. -/
def closeMVarRels (gs : List MVarId) : MetaM (List MVarId) := do
  for g in gs do
    if ← g.isAssigned then continue
    let tgt ← g.getType''
    let .app (.app _ a) b := tgt | continue
    unless a.isMVar && b.isMVar && a != b do continue
    let (a, b) := if gs.contains a.mvarId! then (a, b) else (b, a)
    unless gs.contains a.mvarId! do continue
    a.mvarId!.assign b
    try g.applyRfl catch _ => pure ()
  gs.filterM fun g => return !(← g.isAssigned)

/-- `step? g` applies to `g` the `@[compute_degree]` lemma determined by `getAction?`.
It returns the resulting goals, or `none` if no lemma matches `g`.
It fails if some lemmas match `g`, but none of them can be applied.

If `cached` is the result of an earlier call to `getAction? g` and the target of `g` has not changed
since then, `step?` uses it instead of calling `getAction?` again. -/
def step? (g : MVarId) (cached : Option (Expr × Action) := none) :
    MetaM (Option (List MVarId)) := do
  let cached ← match cached with
    | some (tgt, a) => if (← g.getType'') == tgt then pure (some (tgt, a)) else getAction? g
    | none => getAction? g
  let some (_, action) := cached | return none
  match action with
  | .relax lem =>
    trace[Tactic.compute_degree] "relaxing the outputs of{indentD (← g.getType'')}\n\
      using '{lem.declName}'"
    return some (← closeMVarRels (← g.applyConst lem.declName))
  | .apply lems =>
    for lem in lems do
      if let some gs ← observing? (g.applyConst lem.declName) then
        trace[Tactic.compute_degree] "applied '{lem.declName}' to{indentD (← g.getType'')}"
        return some gs
    throwError "'compute_degree': none of the lemmas {lems.map (·.declName)} can be applied to\
      {indentD (← g.getType'')}"

end Mathlib.Tactic.ComputeDegree
