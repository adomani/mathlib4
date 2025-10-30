import Mathlib.Tactic.TacticAnalysis

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

# Some `Config`s (in the `Declarations` file)
-/
