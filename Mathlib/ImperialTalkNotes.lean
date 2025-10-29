import Mathlib.Tactic.TacticAnalysis

/-
Notes

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
-/
