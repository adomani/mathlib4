/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Tactic.ComputeDegree.Core

/-!
# `compute_degree` and `monicity`: tactics for explicit polynomials

This file defines two related tactics: `compute_degree` and `monicity`.

Using `compute_degree` when the goal is of one of the seven forms
* `natDegree f ≤ d` (or `<`),
* `degree f ≤ d` (or `<`),
* `natDegree f = d`,
* `degree f = d`,
* `coeff f d = r`, if `d` is the degree of `f`,

tries to solve the goal.
It may leave side-goals, in case it is not entirely successful.

Using `monicity` when the goal is of the form `Monic f` tries to solve the goal.
It may leave side-goals, in case it is not entirely successful.

Both tactics admit a `!` modifier (`compute_degree!` and `monicity!`) instructing
Lean to try harder to close the goal.

See the doc-strings for more details.

## TODO

* Currently, `compute_degree` does not deal correctly with some edge cases.  For instance,
  ```lean
  example [Semiring R] : natDegree (C 0 : R[X]) = 0 := by
    compute_degree
  --  ⊢ 0 ≠ 0
  ```
  Still, it may not be worth to provide special support for `natDegree f = 0`.
* Make sure that numerals in coefficients are treated correctly.
* Make sure that `compute_degree` works with goals of the form `degree f ≤ ↑d`, with an
  explicit coercion from `ℕ` on the RHS.
* Add support for proving goals of the from `natDegree f ≠ 0` and `degree f ≠ 0`.
* Make sure that `degree`, `natDegree` and `coeff` are equally supported.

## Implementation notes

Assume that `f : R[X]` is a polynomial with coefficients in a semiring `R` and
`d` is either in `ℕ` or in `WithBot ℕ`.

If the goal has the form `natDegree f < d`, then we convert it to two separate goals:
* `natDegree f ≤ ?_`, on which we apply the following steps;
* `?_ < d`;

where `?_` is a metavariable that `compute_degree` computes in its process.
We proceed similarly for `degree f < d`.

If the goal has the form `natDegree f = d`, then we convert it to three separate goals:
* `natDegree f ≤ d`;
* `coeff f d = r`;
* `r ≠ 0`.

Similarly, an initial goal of the form `degree f = d` gives rise to goals of the form
* `degree f ≤ d`;
* `coeff f d = r`;
* `r ≠ 0`.

Next, we apply successively lemmas whose side-goals all have the shape
* `natDegree f ≤ d`;
* `degree f ≤ d`;
* `coeff f d = r`;

plus possibly "numerical" identities and choices of elements in `ℕ`, `WithBot ℕ`, and `R`.

Recursing into `f`, we break apart additions, multiplications, powers, subtractions,...
The leaves of the process are
* numerals, `C a`, `X` and `monomial a n`, to which we assign degree `0`, `1` and `a` respectively;
* `fvar`s `f`, to which we tautologically assign degree `natDegree f`.

The lemmas that `compute_degree` applies are the ones tagged with `@[compute_degree]`: there is
no hard-coded dictionary from head symbols to lemmas.  The attribute and the code that selects
and applies the lemmas are in `Mathlib/Tactic/ComputeDegree/Core.lean`, whose module docstring
explains how the statement of a lemma determines how `compute_degree` uses it.
This file contains the lemmas for `natDegree`, `degree` and `coeff`, and the tactic itself.
-/

public meta section

open AddMonoidAlgebra Polynomial

namespace Mathlib.Tactic.ComputeDegree

section recursion_lemmas
/-!
### Simple lemmas about `natDegree`

The lemmas in this section all have the form `natDegree <some form of cast> ≤ 0`.
Their proofs are weakenings of the stronger lemmas `natDegree <same> = 0`.
These are the lemmas called by `compute_degree` on (almost) all the leaves of its recursion.
-/

variable {R : Type*}

section semiring
variable [Semiring R]

@[compute_degree]
theorem natDegree_C_le (a : R) : natDegree (C a) ≤ 0 := (natDegree_C a).le

@[compute_degree]
theorem natDegree_natCast_le (n : ℕ) : natDegree (n : R[X]) ≤ 0 := (natDegree_natCast _).le
@[compute_degree]
theorem natDegree_zero_le : natDegree (0 : R[X]) ≤ 0 := natDegree_zero.le
@[compute_degree]
theorem natDegree_one_le : natDegree (1 : R[X]) ≤ 0 := natDegree_one.le

@[compute_degree]
theorem natDegree_ofNat_le (n : ℕ) [n.AtLeastTwo] : natDegree (OfNat.ofNat n : R[X]) ≤ 0 :=
  (natDegree_ofNat n).le

@[compute_degree]
theorem degree_ofNat_le (n : ℕ) [n.AtLeastTwo] : degree (OfNat.ofNat n : R[X]) ≤ 0 :=
  degree_natCast_le n

@[compute_degree]
theorem coeff_ofNat_ite {m n : ℕ} [m.AtLeastTwo] :
    (OfNat.ofNat m : R[X]).coeff n = ((if n = 0 then OfNat.ofNat m else 0 : ℕ) : R) :=
  coeff_natCast_ite

@[compute_degree]
theorem coeff_add_of_eq {n : ℕ} {a b : R} {f g : R[X]}
    (h_add_left : f.coeff n = a) (h_add_right : g.coeff n = b) :
    (f + g).coeff n = a + b := by subst ‹_› ‹_›; apply Polynomial.coeff_add

@[compute_degree]
theorem coeff_mul_add_of_le_natDegree_of_eq_ite {d df dg : ℕ} {a b : R} {f g : R[X]}
    (h_mul_left : natDegree f ≤ df) (h_mul_right : natDegree g ≤ dg)
    (h_mul_left : f.coeff df = a) (h_mul_right : g.coeff dg = b) (ddf : df + dg ≤ d) :
    (f * g).coeff d = if d = df + dg then a * b else 0 := by
  split_ifs with h
  · subst h_mul_left h_mul_right h
    exact coeff_mul_add_eq_of_natDegree_le ‹_› ‹_›
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ddf ?_)
    · exact natDegree_mul_le_of_le ‹_› ‹_›
    · exact ne_comm.mp h

@[compute_degree]
theorem coeff_pow_of_natDegree_le_of_eq_ite' {m n o : ℕ} {a : R} {p : R[X]}
    (h_pow : natDegree p ≤ n) (h_exp : m * n ≤ o) (h_pow_bas : coeff p n = a) :
    coeff (p ^ m) o = if o = m * n then a ^ m else 0 := by
  split_ifs with h
  · subst h h_pow_bas
    exact coeff_pow_of_natDegree_le ‹_›
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ‹_› ?_)
    · exact natDegree_pow_le_of_le m ‹_›
    · exact Iff.mp ne_comm h

section SMul

variable {S : Type*} [SMulZeroClass S R] {n : ℕ} {a : S} {f : R[X]}

@[compute_degree]
theorem natDegree_smul_le_of_le (hf : natDegree f ≤ n) :
    natDegree (a • f) ≤ n :=
  (natDegree_smul_le a f).trans hf

@[compute_degree]
theorem degree_smul_le_of_le (hf : degree f ≤ n) :
    degree (a • f) ≤ n :=
  (degree_smul_le a f).trans hf

@[compute_degree]
theorem coeff_smul : (a • f).coeff n = a • f.coeff n := rfl

end SMul

section congr_lemmas

/-- The following two lemmas should be viewed as a hand-made "congr"-lemmas.
They achieve the following goals.
* They introduce *two* fresh metavariables replacing the given one `deg`,
  one for the `natDegree ≤` computation and one for the `coeff =` computation.
  This helps `compute_degree`, since it does not "pre-estimate" the degree,
  but it "picks it up along the way".
* They split checking the inequality `coeff p n ≠ 0` into the task of
  finding a value `c` for the `coeff` and then
  proving that this value is non-zero by `coeff_ne_zero`.
-/
@[compute_degree]
theorem natDegree_eq_of_le_of_coeff_ne_zero' {deg m o : ℕ} {c : R} {p : R[X]}
    (h_natDeg_le : natDegree p ≤ m) (coeff_eq : coeff p o = c)
    (coeff_ne_zero : c ≠ 0) (deg_eq_deg : m = deg) (coeff_eq_deg : o = deg) :
    natDegree p = deg := by
  subst coeff_eq deg_eq_deg coeff_eq_deg
  exact natDegree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›

@[compute_degree]
theorem degree_eq_of_le_of_coeff_ne_zero' {deg m o : WithBot ℕ} {c : R} {p : R[X]}
    (h_deg_le : degree p ≤ m) (coeff_eq : coeff p (WithBot.unbotD 0 deg) = c)
    (coeff_ne_zero : c ≠ 0) (deg_eq_deg : m = deg) (coeff_eq_deg : o = deg) :
    degree p = deg := by
  subst coeff_eq coeff_eq_deg deg_eq_deg
  rcases eq_or_ne m ⊥ with rfl | hh
  · exact bot_unique h_deg_le
  · obtain ⟨m, rfl⟩ := WithBot.ne_bot_iff_exists.mp hh
    exact degree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›

variable {m n : ℕ} {f : R[X]} {r : R}

theorem coeff_congr_lhs (h : coeff f m = r) (natDeg_eq_coeff : m = n) : coeff f n = r :=
  natDeg_eq_coeff ▸ h

/-- The relaxation lemma for `natDegree _ ≤ _`: its right-hand side is the output. -/
@[compute_degree]
theorem natDegree_le_of_le_of_le {m n : ℕ} (h : natDegree f ≤ m) (hmn : m ≤ n) :
    natDegree f ≤ n :=
  h.trans hmn

/-- The relaxation lemma for `degree _ ≤ _`: its right-hand side is the output. -/
@[compute_degree]
theorem degree_le_of_le_of_le {m n : WithBot ℕ} (h : degree f ≤ m) (hmn : m ≤ n) :
    degree f ≤ n :=
  h.trans hmn

/-- The entry lemma for `natDegree _ < _`: it reduces it to `natDegree _ ≤ _`. -/
@[compute_degree]
theorem natDegree_lt_of_le_of_lt {m n : ℕ} (h : natDegree f ≤ m) (hmn : m < n) :
    natDegree f < n :=
  h.trans_lt hmn

/-- The entry lemma for `degree _ < _`: it reduces it to `degree _ ≤ _`. -/
@[compute_degree]
theorem degree_lt_of_le_of_lt {m n : WithBot ℕ} (h : degree f ≤ m) (hmn : m < n) :
    degree f < n :=
  h.trans_lt hmn

/-- The fallback for `natDegree _ ≤ _`, used when no other lemma applies. -/
@[compute_degree]
theorem natDegree_le_natDegree_self (f : R[X]) : natDegree f ≤ natDegree f := le_rfl

/-- The fallback for `degree _ ≤ _`, used when no other lemma applies. -/
@[compute_degree]
theorem degree_le_degree_self (f : R[X]) : degree f ≤ degree f := le_rfl

/-- The fallback for `coeff _ _ = _`, used when no other lemma applies. -/
@[compute_degree]
theorem coeff_eq_coeff_self (f : R[X]) (n : ℕ) : f.coeff n = f.coeff n := rfl

/-- The relaxation lemma for `coeff _ _ = _`: the index and the right-hand side are the outputs. -/
@[compute_degree]
theorem coeff_congr (h : coeff f m = r) (natDeg_eq_coeff : m = n) {s : R} (rs : r = s) :
    coeff f n = s :=
  natDeg_eq_coeff ▸ rs ▸ h

end congr_lemmas

end semiring

section ring
variable [Ring R]

@[compute_degree]
theorem natDegree_intCast_le (n : ℤ) : natDegree (n : R[X]) ≤ 0 := (natDegree_intCast _).le

@[compute_degree]
theorem coeff_sub_of_eq {n : ℕ} {a b : R} {f g : R[X]} (hf : f.coeff n = a) (hg : g.coeff n = b) :
    (f - g).coeff n = a - b := by subst hf hg; apply Polynomial.coeff_sub

@[compute_degree]
theorem coeff_neg_of_eq {n : ℕ} {a : R} {f : R[X]} (hf : f.coeff n = a) :
    (-f).coeff n = -a := by subst hf; apply Polynomial.coeff_neg

@[compute_degree]
theorem coeff_intCast_ite {n : ℕ} {a : ℤ} : (Int.cast a : R[X]).coeff n = ite (n = 0) a 0 := by
  simp only [← C_eq_intCast, coeff_C, Int.cast_ite, Int.cast_zero]

end ring

end recursion_lemmas

/-!
### `@[compute_degree]` lemmas from other files

The lemmas in this file are tagged with `@[compute_degree]` where they are declared.  The lemmas
below are declared in files that do not import `Mathlib.Tactic.ComputeDegree.Core`.
The module docstring of `Mathlib/Tactic/ComputeDegree/Core.lean` explains how `compute_degree`
uses them.
-/

-- `natDegree _ ≤ _`
attribute [compute_degree] natDegree_X_le natDegree_monomial_le natDegree_add_le_of_le
  natDegree_sub_le_of_le natDegree_mul_le_of_le natDegree_pow_le_of_le natDegree_neg_le_of_le

-- `degree _ ≤ _`
attribute [compute_degree] degree_zero_le degree_one_le degree_natCast_le degree_intCast_le
  degree_C_le degree_X_le degree_monomial_le degree_add_le_of_le degree_sub_le_of_le
  degree_mul_le_of_le degree_pow_le_of_le degree_neg_le_of_le

-- `coeff _ _ = _`
attribute [compute_degree] Polynomial.coeff_zero coeff_one coeff_natCast_ite coeff_C coeff_X
  coeff_monomial_apply

section Tactic

open Lean Elab Tactic Meta Expr

/-- `tryRfl mvs` takes as input a list of `MVarId`s, scans them partitioning them into two
lists: the goals containing some metavariables and the goals not containing any metavariable.

If a goal containing a metavariable has the form `?_ = x`, `x = ?_`, where `?_` is a metavariable
and `x` is an expression that does not involve metavariables, then it closes this goal using `rfl`,
effectively assigning the metavariable to `x`.

If a goal does not contain metavariables, it tries `rfl` on it.

It returns the list of `MVarId`s, beginning with the ones that initially involved (`Expr`)
metavariables followed by the rest.
-/
def tryRfl (mvs : List MVarId) : MetaM (List MVarId) := do
  let (yesMV, noMV) ← mvs.partitionM fun mv =>
                          return hasExprMVar (← instantiateMVars (← mv.getDecl).type)
  let tried_rfl ← noMV.mapM fun g => g.applyConst ``rfl <|> return [g]
  let assignable ← yesMV.mapM fun g => do
    let tgt ← instantiateMVars (← g.getDecl).type
    match tgt.eq? with
      | some (_, lhs, rhs) =>
        if (isMVar rhs && (! hasExprMVar lhs)) ||
           (isMVar lhs && (! hasExprMVar rhs)) then
           g.applyConst ``rfl
        else pure [g]
      | none =>
        return [g]
  return (assignable.flatten ++ tried_rfl.flatten)

@[deprecated (since := "2026-05-27")] alias try_rfl := tryRfl

/--
`splitApply mvs static` takes two lists of `MVarId`s.  The first list, `mvs`,
corresponds to goals that are potentially within the scope of `compute_degree`:
namely, goals of the form
`natDegree f ≤ d`, `degree f ≤ d`, `natDegree f = d`, `degree f = d`, `coeff f d = r`.

`splitApply` determines which of these goals are actually within the scope, it applies the relevant
`@[compute_degree]` lemma and returns two lists: the left-over goals of all the applications,
followed by the concatenation of the previous `static` list, followed by the newly discovered goals
outside of the scope of `compute_degree`. -/
def splitApply (mvs static : List MVarId) : MetaM ((List MVarId) × (List MVarId)) := do
  let actions ← mvs.mapM fun mv => return (mv, ← getAction? mv)
  let (can_progress, curr_static) := actions.partition (·.2.isSome)
  -- The goals processed earlier may have assigned metavariables in `mv`: `step?` only reuses the
  -- result of `getAction?` if the target of `mv` has not changed.
  let progress ← can_progress.mapM fun (mv, a) => return (← step? mv a).getD [mv]
  return (progress.flatten, static ++ curr_static.map (·.1))

/-- `miscomputedDegree? deg false_goals` takes as input
* an `Expr`ession `deg`, representing the degree of a polynomial
  (i.e. an `Expr`ession of inferred type either `ℕ` or `WithBot ℕ`);
* a list of `MVarId`s `false_goals`.

Although inconsequential for this function, the list of goals `false_goals` reduces to `False`
if `norm_num`med.
`miscomputedDegree?` extracts error information from goals of the form
* `a ≠ b`, assuming it comes from `⊢ coeff_of_given_degree ≠ 0` —
  reducing to `False` means that the coefficient that was supposed to vanish, does not;
* `a ≤ b`, assuming it comes from `⊢ degree_of_subterm ≤ degree_of_polynomial` —
  reducing to `False` means that there is a term of degree that is apparently too large;
* `a = b`, assuming it comes from `⊢ computed_degree ≤ given_degree` —
  reducing to `False` means that there is a term of degree that is apparently too large.

The cases `a ≠ b` and `a = b` are not a perfect match with the top coefficient:
reducing to `False` is not exactly correlated with a coefficient being non-zero.
It does mean that `compute_degree` reduced the initial goal to an unprovable state
(unless there was already a contradiction in the initial hypotheses!), but it is indicative that
there may be some problem.
-/
def miscomputedDegree? (deg : Expr) : List Expr → List MessageData
  | tgt::tgts =>
    let rest := miscomputedDegree? deg tgts
    if tgt.ne?.isSome then
      m!"* the coefficient of degree {deg} may be zero" :: rest
    else if let some ((Expr.const ``Nat []), lhs, _) := tgt.le? then
      m!"* there is at least one term of naïve degree {lhs}" :: rest
    else if let some (_, lhs, _) := tgt.eq? then
      m!"* there may be a term of naïve degree {lhs}" :: rest
    else rest
  | [] => []

/--
`compute_degree` is a tactic to solve goals of the form
*  `natDegree f = d`,
*  `degree f = d`,
*  `natDegree f ≤ d` (or `<`),
*  `degree f ≤ d` (or `<`),
*  `coeff f d = r`, if `d` is the degree of `f`.

The tactic may leave goals of the form `d' = d`, `d' ≤ d`, `d' < d`, or `r ≠ 0`, where `d'` in `ℕ`
or `WithBot ℕ` is the tactic's guess of the degree, and `r` is the coefficient's guess of the
leading coefficient of `f`.

`compute_degree` applies `norm_num` to the left-hand side of all side goals, trying to close them.

The variant `compute_degree!` first applies `compute_degree`.
Then it uses `norm_num` on all the remaining goals and tries `assumption`.

`compute_degree` can be extended by tagging lemmas with `@[compute_degree]`.
-/
syntax (name := computeDegree) "compute_degree" "!"? : tactic

@[tactic_alt computeDegree]
macro "compute_degree!" : tactic => `(tactic| compute_degree !)

elab_rules : tactic | `(tactic| compute_degree $[!%$bang]?) => focus <| withMainContext do
  let goal ← getMainGoal
  let gt ← goal.getType''
  let deg? := match gt.eq? with
    | some (_, _, rhs) => some rhs
    | _ => none
  let some gls ← step? goal | throwError m!"'compute_degree' inapplicable. \
      No '@[compute_degree]' lemma applies to the goal{indentD gt}"
  let mut (gls, static) := (gls, [])
  while gls != [] do (gls, static) ← splitApply gls static
  let rfled ← tryRfl static
  setGoals rfled
  --  simplify the left-hand sides, since this is where the degree computations leave
  --  expressions such as `max (0 * 1) (max (1 + 0 + 3 * 4) (7 * 0))`
  evalTactic
    (← `(tactic| try any_goals conv_lhs =>
                   (simp +decide only [Nat.cast_withBot]; norm_num)))
  if bang.isSome then
    let mut false_goals : Array MVarId := #[]
    let mut new_goals : Array MVarId := #[]
    for g in ← getGoals do
      let gs' ← run g do evalTactic (←
        `(tactic| try (any_goals norm_num <;> norm_cast <;> try assumption)))
      new_goals := new_goals ++ gs'.toArray
      if ← gs'.anyM fun g' => g'.withContext do return (← g'.getType'').isConstOf ``False then
        false_goals := false_goals.push g
    setGoals new_goals.toList
    if let some deg := deg? then
      let errors := miscomputedDegree? deg (← false_goals.mapM (MVarId.getType'' ·)).toList
      unless errors.isEmpty do
        throwError Lean.MessageData.joinSep
          (m!"The given degree is '{deg}'.  However,\n" :: errors) "\n"

/-- `monicity` tries to solve a goal of the form `Monic f`.
It converts the goal into a goal of the form `natDegree f ≤ n` and one of the form `f.coeff n = 1`
and calls `compute_degree` on those two goals.

The variant `monicity!` starts like `monicity`, but calls `compute_degree!` on the two side-goals.
-/
macro (name := monicityMacro) "monicity" : tactic =>
  `(tactic| (apply monic_of_natDegree_le_of_coeff_eq_one <;> compute_degree))

@[tactic_alt monicityMacro]
macro "monicity!" : tactic =>
  `(tactic| (apply monic_of_natDegree_le_of_coeff_eq_one <;> compute_degree!))

end Tactic

end Mathlib.Tactic.ComputeDegree

/-!
We register `compute_degree` with the `hint` tactic.
-/
register_hint 1000 compute_degree
register_try?_tactic (priority := 1000) compute_degree
