import Mathlib.Tactic.TacticAnalysis
import Mathlib.Tactic.TacticAnalysis.Declarations
import Mathlib.adomaniLeanUtils.inspect_syntax
import Mathlib.adomaniLeanUtils.inspect_infotree

/-
# General outline

* `Config` takes `ContextInfo`s and `TacticInfo` and performs some
  `CommandElabM` computation.

  structure Config where
    run : Array (ContextInfo × TacticInfo) → CommandElabM Unit

* `Pass` extends `Config` and also links it to an (optional) option.

* `Entry` contains the name of a `Config` and of an option.
* `Entry.import` converts an `Entry` into a `Pass`.

`Entry` is lexicographically ordered by names.

Basically, we want to pass around `Pass`es, but we can only store `Entry`s.

The attribute is accessed as `@[tacticAnalysis optionName]`
and it adds the `Config` to which the attribute was added with the input option.

* Write a function that reports the ranges of `findTacticSeqs`, maybe?
  Note that the input `Syntax` is only used for the global
  "is there a range associated to this or not" check.

* `runPasses` simply executes the code in each input `Pass` on the given `InfoTree`s.

* Finally, the `tacticAnalysis` linter executes `runPasses` on every command.

# Helper for creating `Config`s

* `TriggerCondition` is used to select sublists of tactics on which to run the tests.
  It has three modes:
  * `skip` means discard all tactics in the list so far and move on to the next one;
  * `continue` means to accumulate the current tactic, but do not test yet and check if the current sublist should grow more;
  * `accept` means stop accumulating and execute the tests.

  The `continue` and `accept` modes also contain a `context` to potentially propagate information about the accumulation of tactics.

* `ComplexConfig` has 3 main components: `trigger`, `test` and `tell`.
  These are the phases of the framework:
  * `trigger` selects the tactics to analyze;
  * `test` runs some `MetaM` code on the selected tactics;
  * `tell` reports a `CommandElabM` conclusion of `test`.

  Among the information that the various pieces pass around, the analysis also records the number of `heartbeats`.

* `testTacticSeq` assumes that the input `tacticSeq` has been selected by the `trigger` and
  * runs the `test` on it;
  * reports the corresponding `tell`.

* `runPass` puts it all together:
  * select the sublists of tactics using `trigger`;
  * run `testTacticSeq` on the selected tactics.

* `Config.ofComplex` simply uses the code in a `ComplexConfig` as a `Config`.

# Some `Config`s (in the `Declarations` file)

* `TerminalReplacementOutcome` is a custom type for recording the outcome of a `test` in the
  `terminalReplacement` setting.
  It always contains a `tactic` and
  * if the outcome is `success`, then nothing else;
  * if the outcome is `remainingGoals`, then a list of goals as `MessageData`;
  * if the outcome is `error`, then a single `MessageData`.

* `terminalReplacement` produces a `Config` using the `ofComplex` setting in the case of replacing
  a terminal tactic with another.
  The inputs are

  * `oldTacticName` and `newTacticName` -- human-readable names for either
    individual tactics (such as `linarith`), or
    families of tactics (such as `ring`, including `ring_nf`, `ring1`, and so on).
    These are helpful for reporting, but have no bearing to what the tactics really are.

  * `newTactic stx goal` produces the new tactic as a (`MetaM`-)function of
    the old tactic `stx` to be replaced, and
    the current `goal` (passed as an `MVarId`).

  * `oldTacticKind`, the `SyntaxNodeKind` that triggers the replacement
    (e.g. `Mathlib.Tactic.linarith` for `linarith).

  * `reportFailure`, `reportSuccess` and `reportSlowdown` -- `Bool`ean flags for whether or not to
    report in the case of failure, success and slowdown.

  * `maxSlowdown` -- a threshold for what to consider an acceptable slowdown.
    This is a ratio, rather than an absolute value, and it defaults to `1`, which means that
    no slowdown is allowed.

  Here is a summary of what the code does.

  * The output type is `TerminalReplacementOutcome` and
    the context that is passed around is a `Syntax`.

  * The `trigger` only `accept`s tactics with `SyntaxNodeKind` the input `oldTacticKind` and
    `skip`s everything else.

  * The `test` runs the tactic `tac` specified by `newTactic stx goal` and reports
    * a `success tac` if the goal is closed;
    * a `.remainingGoals tac [list of MessageData-expressions for the left-over goals]`;
    * a `.error tac msg`, where `msg` is a MessageData containing a standalone Lean file of the form
      ```lean4
      import xxx
      ...
      import zzz

      theorem extracted ... := by
        fail_if_success tac
        stx
      ```
  The rest of the reporting is pretty straightforward.

After this, the file starts defining various `Config`s using the tools developped so far.
Several involve replacing a terminal tactic with another, e.g.
* `linarithToGrind`,
* `ringToGrind`,
* `omegaToCutsat`.

These can be seen as either
* "regressions", if reporting a failure to replace say `linarith` by `grind`; or
* "golfs", if reporting a success to replace `omega` by `cutsat`.

Hence, this can be used to verify that a tactic is "increasing" its scope (mostly `grind`),
or seeing if one can be phased out, since one or more other tactics might take its place
(for instance, replacing `omega` by `cutsat`).

-/
variable (nnn : Nat)


inspect #check Nat.succ
inspect #check nnn.succ
open Lean.Elab
inspectIT #check Nat.succ
inspectIT #check nnn.succ
