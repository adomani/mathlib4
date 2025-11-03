import Mathlib.Tactic.AdaptationNote
import Mathlib.Tactic.TacticAnalysis
import Mathlib.Tactic.TacticAnalysis.Declarations
import Mathlib.adomaniLeanUtils.inspect_syntax
import Mathlib.adomaniLeanUtils.inspect_infotree

open Lean.Elab

set_option linter.unusedTactic false
set_option linter.style.multiGoal false

set_option linter.tacticAnalysis.mergeWithGrind true in
example : 0 = 0 := by
  have : 0 = 0 := by
    intros
    intros
    intros
    intros
    intros
    grind
  intros
  intros
  intros
  intros
  intros
  grind

set_option linter.tacticAnalysis.terminalToGrind true in
example : 0 = 0 := by
  intros
  intros
  intros
  intros
  intros
  rfl

open Lean Elab Command
def spell (ns : Parser.SyntaxNodeKindSet) : Syntax → CommandElabM Unit
  | s@(.node i k args) => do
    if ns.contains k then logInfoAt s k
    let _ ← args.mapM (spell ns)
  | _ => return default

elab "ss " cmd:command : command => do
  elabCommand cmd
--  let parserCats ← Parser.builtinParserCategoriesRef.get
--  logInfo m!"{parserCats.toArray.map (·.1)}"
--  logInfo m!"{parserCats.toArray.map fun cat => (cat.1, ((parserCats.find? cat.1)).toArray.map (·.kinds.toArray.map (m!"{.ofConstName ·.1}")))}"
--  let tactics := parserCats.find? `tactic
  let cats := (Parser.parserExtension.getState (← getEnv)).categories
  let some tactics := Parser.ParserCategory.kinds <$> cats.find? `tactic
    | return
  -- Do not forget about `conv`
  logInfo m!"{tactics.toArray.map (m!"{.ofConstName ·.1}")}"
  spell tactics cmd
  --logInfo m!"{tactics.map (·.kinds.toArray)}"

inspect
example : 0 = 0 := by
  intros
  skip
  have := 0
  rfl
#check Batteries.Tactic.unreachable
ss
example : 0 = 0 := by
  intros
  have := by
    skip
    intros
    exact 1
  skip
  have := 0
  rfl

#check Lean.Parser.Tactic.open
#check Lean.Parser.Tactic.match
#check Lean.Parser.Tactic.unknown

namespace Talk
/-!
# What happens when you type a command in Lean?

This is a rough and not entirely correct outline.

## Parsing
First, Lean is going to produce a `Syntax` object from what you typed.
-/
#print Syntax

inductive Syntax where
  | missing
  | node   (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax)
  | atom   (info : SourceInfo) (val : String)
  | ident  (info : SourceInfo) (rawVal : Substring) (val : Name)
    (preresolved : List Syntax.Preresolved)

-- `inspect` is a command that is only defined for this presentation!
--inspect #check Nat
--inspect section

run_cmd
  let h := mkIdent `hello
  let stx ← `(#check $h .succ)
  let stx ← `(dite cond (fun h => t) (fun h => t))
  let stx ← `(infixl:25 " ≃* " => MulEquiv)
  logInfo (InspectSyntax.toMessageData stx)

/-!
## Elaboration
Once Lean produced a valid `Syntax` term, it next `elaborates` it.

During elaboration, all sorts of results can happen:
* a whole bunch of declarations are added to the `Environment` (e.g. you are `import`ing a module);
* a new declaration could be added to the `Environment` (e.g. you are proving a `theorem`);
* a `namespace` could be opened;
* an `attribute` may be added to a previously defined declaration;
* an option may be set (e.g. `set_option autoImplicit false`);
* a new `notation` may be introduced (e.g. `infixl:25 " ≃* " => MulEquiv`);
* a new command may be defined (e.g. you are using `elab`);
and so on.

Most of these effects, modify the `Environment`.
At the same time, what the `Environment` is when a command is issued, determines how the command
is elaborated!
-/
#print Environment
/-!
The `Environment` is not the only data structure that affects elaboration of commands.
Modifying the `Scope` also affects elaboration -- the `Scope` is not part of the `Environment`.
-/

#print Scope
/-!
The `Scope` is a `structure` that carries additional information useful for elaborating commands.
It is part of the state of the `CommandElabM` monad.
-/
variable (nnn : Nat)

#where

/-!
## Quiz

What is the difference in the `Syntax` trees for the following command?
-/

#check Nat.succ
#check nnn.succ

/-!
## Answer
Let's `inspect` them!
-/

--inspect #check Nat.succ
--inspect #check nnn.succ

/-!
What changes?

`#check` discards the effects of its computations from the `Environment`, so there is no persistent
data left after a `#check`.

However, elaboration is a complicated process and there is a data-structure that contains basically
*all* the information about each command: the `InfoTree`s.
-/

#print InfoTree
/-!
The construction of an `InfoTree` for a command is intertwined with the elaboration of the command
itself.
While the command gets elaborated, the `InfoTree` gets constructed, storing important information,
that is then also used during elaboration.

Once Lean finishes elaborating a command, it also creates the `InfoTree`s.
And we can inspect them!
-/

inspectIT #check Nat.succ
inspectIT #check nnn.succ
/-!
## The takeaway

When inspecting commands,
* we get superficial information by analysing the `Syntax`;
* we get in-depth (and virtually complete) information, by analysing the `InfoTree`s.

## What should I expect to find in an `InfoTree`

As you move the cursor through a command, the `InfoView` displays changing information.
More or less, every time that the display changes, corresponds to a new node in an `InfoTree`.
Some of the information stored in the `Info` input to that node is then displayed in the
`InfoView`.

Depending on the `Info` at each node, different kinds of "context" are accessible.

### `TacticInfo` nodes in an `InfoTree`
For instance at a `TacticInfo` node, we can find information about
* which `Syntax` node is responsible for this `Info`;
* which elaborator handled the corresponding `Syntax`;
* the metavariable contexts before and after the tactic is evaluated;
* the list of goals before and after the tactic is evaluated.

In turn, the metavariable contexts contain information about the types of each goals,
their universe levels, which relationships there are between all the metavariables that have been
created so far, local contexts and so on.

### `ContextInfo` and `InfoTree`s
A `ContextInfo` is not actually stored anywhere in an `InfoTree`
(although the related `PartialContextInfo` is).
Even so, a `ContextInfo` is similar to information that could be included in an `InfoTree`.
The main difference is that the data contained in `InfoTree`s tends to be "local": it is a snapshot
of what is available at a particular moment.
A `ContextInfo` is more "global": it links the information that was available *before* the command
was elaborated to the specific modifications that happened in the course of elaboration.

For instance, the `Environment` and the whole content of the file is contained in a `ContextInfo`.
Also, which `option`s are set, what is the current `namespace` and what namespaces are `open`
is all stored in a `ContextInfo`.

Note that this information can be modified within a single command, since there can be nested
`set_option ... in ...`, `variable ... in ...` and similar modifying any given command.

In summary, a `ContextInfo` really does provide a "context" for the data stored in the `Info` nodes:
the `ContextInfo` is essential to "read" correctly the information of the `Info` nodes.

# The `tacticAnalysis` framework

Finally, we made it here!

## General outline

* `Config` takes `ContextInfo`s and `TacticInfo` and performs some
  `CommandElabM` computation.
  ```
  structure Config where
    run : Array (ContextInfo × TacticInfo) → CommandElabM Unit
  ```

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

## Helper for creating `Config`s

* `TriggerCondition` is used to select sublists of tactics on which to run the tests.
  It has three modes:
  * `skip` means discard all tactics in the list so far and move on to the next one;
  * `continue` means to accumulate the current tactic, but do not test yet and check if the current
    sublist should grow more;
  * `accept` means stop accumulating and execute the tests.

  The `continue` and `accept` modes also contain a `context` to potentially propagate information
  about the accumulation of tactics.

* `ComplexConfig` has 3 main components: `trigger`, `test` and `tell`.
  These are the phases of the framework:
  * `trigger` selects the tactics to analyze;
  * `test` runs some `MetaM` code on the selected tactics;
  * `tell` reports a `CommandElabM` conclusion of `test`.

  Among the information that the various pieces pass around, the analysis also records the number
  of `heartbeats`.

* `testTacticSeq` assumes that the input `tacticSeq` has been selected by the `trigger` and
  * runs the `test` on it;
  * reports the corresponding `tell`.

* `runPass` puts it all together:
  * select the sublists of tactics using `trigger`;
  * run `testTacticSeq` on the selected tactics.

* `Config.ofComplex` simply uses the code in a `ComplexConfig` as a `Config`.

## Some `Config`s (in the `Declarations` file)

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

There are a few more `Config`s that are easy to interpret.

* `rwMerge` isolates (maximal) chains length at least 2 of consecutive `rw`s and tries to merge
  them into a single `rw` that closes the goal.

* `mergeWithGrind` tries to merge a (maximal) pair `tac; grind` with `grind` alone,
  assuming that it still closes the goal.

  I wonder whether the merging only maximal chains of length 2 is intended.

* `terminalToGrind` is similar, except that it tries to replace "tails" of tactics by `grind`,
  regardless of whether the tail already ended with `grind` or not.

* `tryAtEachStep` is another "`Config`-template": it simply tries to insert a tactic at all
  places and checks whether it closes the goal.
  `grind`, `simp_all`, `aesop` and `grind +premises` are all individually defined using
  `tryAtEachStep`.

* `introMerge` does what is expected: merge consecutive uses of `intro`.

# Future work and todos

* `findTacticSeqs` does not actually do what it says.
  I consider this to be a bug and it should be fixed!

* It would be interesting to allow functions such as `rwMerge` to try to merge *subsets* of
  consecutive `rw`s, instead of "all or nothing".

* Right now, the `tacticAnalysis` framework does not have "global" awareness:
  it can evaluate a tactic "locally", but it cannot figure out whether the result of that evaluation
  will produce a globally valid command.

* Besides inspecting tactics, it would also be useful to inspect all commands in general.

* Ideally, this should all be linked to automated modifications of the source code, so that running
  the framework also has the option of self-correcting/self-improving the source.
-/

end Talk
