/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public meta import Mathlib.Tactic.Linter.Header
import Lean.Parser.Syntax
import Init.Data.String.TakeDrop

/-!
# The `commandStart` linter

The `commandStart` linter emits a warning if
* either a command does not start at the beginning of a line;
* or the "hypotheses segment" of a declaration does not coincide with its pretty-printed version.
-/

meta section

open Lean Elab Command Linter

private def String.norm (s : String) : String :=
  s.replace "\n" "⏎"

namespace Mathlib.Linter1

/--
The `commandStart` linter emits a warning if
* either a command does not start at the beginning of a line;
* or the "hypotheses segment" of a declaration does not coincide with its pretty-printed version.

In practice, this makes sure that the spacing in a typical declaration looks like
```lean
example (a : Nat) {R : Type} [Add R] : <not linted part>
```
as opposed to
```lean
example (a: Nat) {R:Type}  [Add  R] : <not linted part>
```
-/
public register_option linter.style.commandStart1 : Bool := {
  defValue := false
  descr := "enable the commandStart linter"
}

/-- If the `linter.style.commandStart.verbose` option is `true`, the `commandStart` linter
reports some helpful diagnostic information. -/
public register_option linter.style.commandStart.verbose1 : Bool := {
  defValue := false
  descr := "enable the commandStart linter"
}

/-- If the command starts with one of the `SyntaxNodeKind`s in `skipped`, then the
`commandStart` linter ignores the command. -/
def skipped : Std.HashSet SyntaxNodeKind := Std.HashSet.emptyWithCapacity
  |>.insert ``Parser.Command.moduleDoc
  |>.insert ``Parser.Command.elab_rules
  |>.insert ``Lean.Parser.Command.syntax
  |>.insert `Aesop.Frontend.Parser.declareRuleSets

/--
`CommandStart.endPos stx` returns the position up until the `commandStart` linter checks the
formatting.
This is every declaration until the type-specification, if there is one, or the value,
as well as all `variable` commands.
-/
def CommandStart.endPos (stx : Syntax) : Option String.Pos.Raw :=
  --dbg_trace stx.getKind
  if skipped.contains stx.getKind then none else
  if let some cmd := stx.find? (#[``Parser.Command.declaration, `lemma].contains ·.getKind) then
    if let some ind := cmd.find? (·.isOfKind ``Parser.Command.inductive) then
      match ind.find? (·.isOfKind ``Parser.Command.optDeclSig) with
      | none => dbg_trace "unreachable?"; none
      | some _sig => stx.getTailPos? --sig.getTailPos?
    else
    match cmd.find? (·.isOfKind ``Parser.Term.typeSpec) with
      | some _s => stx.getTailPos? --s[0].getTailPos? -- `s[0]` is the `:` separating hypotheses and the type
      | none => match cmd.find? (·.isOfKind ``Parser.Command.declValSimple) with
        | some _s => stx.getTailPos? --s.getPos?
        | none => stx.getTailPos? --none
  else if stx.isOfKind ``Parser.Command.variable || stx.isOfKind ``Parser.Command.omit then
    stx.getTailPos?
  else stx.getTailPos?

/--
A `FormatError` is the main structure tracking how some surface syntax differs from its
pretty-printed version.

In case of deviations, it contains the deviation's location within an ambient string.
-/
-- Some of the information contained in `FormatError` is redundant, however, it is useful to convert
-- between the `String.pos` and `String` length conveniently.
public structure FormatError where
  /-- The distance to the end of the source string, as number of characters -/
  srcNat : Nat
  /-- The distance to the end of the source string, as number of string positions -/
  srcEndPos : String.Pos.Raw
  /-- The distance to the end of the formatted string, as number of characters -/
  fmtPos : Nat
  /-- The kind of formatting error. For example: `extra space`, `remove line break` or
  `missing space`.

  Strings starting with `Oh no` indicate an internal error.
  -/
  msg : String
  /-- The length of the mismatch, as number of characters. -/
  length : Nat
  /-- The starting position of the mismatch, as a `String.pos`. -/
  srcStartPos : String.Pos.Raw
  deriving Inhabited

instance : ToString FormatError where
  toString f :=
    s!"srcNat: {f.srcNat}, srcPos: {f.srcEndPos}, fmtPos: {f.fmtPos}, \
      msg: {f.msg}, length: {f.length}\n"

/--
Produces a `FormatError` from the input data.  It expects
* `ls` to be a "user-typed" string;
* `ms` to be a "pretty-printed" string;
* `msg` to be a custom error message, such as `extra space` or `remove line break`;
* `length` (optional with default `1`), how many characters the error spans.

In particular, it extracts the position information within the string, both as number of characters
and as `String.Pos`.
-/
public
def mkFormatError (ls ms : String) (msg : String) (length : Nat := 1) : FormatError where
  srcNat := ls.length
  srcEndPos := ls.rawEndPos
  fmtPos := ms.length
  msg := msg
  length := length
  srcStartPos := ls.rawEndPos

/--
Add a new `FormatError` `f` to the array `fs`, trying, as much as possible, to merge the new
`FormatError` with the last entry of `fs`.
-/
public
def pushFormatError (fs : Array FormatError) (f : FormatError) : Array FormatError :=
  -- If there are no errors already, we simply add the new one.
  if fs.isEmpty then fs.push f else
  let back := fs.back!
  -- If the latest error is of a different kind than the new one, we simply add the new one.
  if back.msg != f.msg || back.srcNat - back.length != f.srcNat then fs.push f else
  -- Otherwise, we are adding a further error of the same kind and we therefore merge the two.
  fs.pop.push {back with length := back.length + f.length, srcStartPos := f.srcEndPos}

/--
Compares the two substrings `s1` and `s2`, with the expectation that `s2` starts with `s1`,
and that the characters where this is not true satisfy `f`.

If the expectation is correct, then it returns `some (s2 \ s1)`, otherwise, it returns `none`.

The typical application uses `f = invisible`.
-/
partial
def consumeIgnoring (s1 s2 : Substring.Raw) (f : String → Bool) : Option Substring.Raw :=
  -- The expected end of the process: `s1` is fully consumed, we return `s2`.
  if s1.isEmpty || s2.isEmpty then s2 else
  -- Otherwise, we compare the first available character of each string.
  let a1 := s1.take 1
  let a2 := s2.take 1
  -- If they agree, we move one step over and continue.
  if a1 == a2 then
    consumeIgnoring (s1.drop 1) (s2.drop 1) f
  else
    -- Also if every character of `a1` or `a2` satisfies `f`, then we drop that and continue.
    if f a1.toString then consumeIgnoring (s1.drop 1) s2 f else
    if f a2.toString then consumeIgnoring s1 (s2.drop 1) f
    -- If all else failed, then we return `none`.
    else some s2

--def invisible (c : Char) : Bool :=
--  c.isWhitespace || #['«', '»'].contains c

def invisible (s : String) : Bool :=
  s.all fun c => c.isWhitespace || #['«', '»'].contains c

/-- Extract the `leading` and the `trailing` substring of a `SourceInfo`. -/
public def _root_.Lean.SourceInfo.getLeadTrail : SourceInfo → String × String
  | .original lead _ trail _ => (lead.toString, trail.toString)
  | _ => default

def compareLeaf (tot : Array Nat) (leadTrail : String × String) (orig s : String) : Array Nat := Id.run do
    let (l, t) := leadTrail
    let mut newTot := tot
    if !l.isEmpty then
      newTot := newTot.push s.length
    if !s.startsWith orig then newTot := newTot.push s.length
    let rest := s.drop orig.length
    if t.trimAscii.isEmpty then if t == " " || t == "\n" then return newTot
    if (t.dropWhile (· == ' ')).take 2 == "--" || (t.dropWhile (· == ' ')).take 1 == "\n" then return newTot
    return newTot.push rest.positions.count

/--
Analogous to `Lean.PrettyPrinter.ppCategory`, but does not run the parenthesizer,
so that the output should only differ from the source syntax in whitespace.
-/
def ppCategory' (cat : Name) (stx : Syntax) : CoreM Format := do
  let opts ← getOptions
  let stx := (sanitizeSyntax stx).run' { options := opts }
  -- the next line starts with `parenthesizeCategory cat stx` in `Lean.PrettyPrinter.ppCategory`
  stx >>= PrettyPrinter.formatCategory cat

/-- Replaces each consecutive run of whitespace in the input `s` with a single space. -/
def reduceWhitespace (s : String) : String :=
  " ".intercalate <| (s.splitToList (·.isWhitespace)).filter (!·.isEmpty)

/-- Converts the input syntax into a string using the pretty-printer and then collapsing
consecuting whitespace into a single space. -/
public def pretty (stx : Syntax) : CommandElabM (Option String) := do
  let fmt : Option Format := ←
      try
        liftCoreM <| ppCategory' `command stx
      catch _ =>
        Linter.logLintIf linter.style.commandStart.verbose1 (stx.getHead?.getD stx)
          m!"The `commandStart` linter had some parsing issues: \
            feel free to silence it and report this error!"
        return none
  if let some fmt := fmt then
    let st := fmt.pretty (width := 100000)
    return reduceWhitespace st
  else
    return none

/--
`getChoiceNode kind args n` is a convenience function for handling `choice` nodes in syntax trees.

* If `kind` is not `choice`, then it returns `args`.
* If `kind` is `choice`, then it returns the array containing only the `n`-th entry of `args`,
  or `#[]` if `args` has fewer than `n` entries.

The argument `n` is optional and equals `0` by default.

The reason for this function is that we traverse the syntax tree to regenerate the expected
string.
If we traversed all of `choice`s children, we would regenerate duplicate parts of the syntax.
For this reason, we make a default choice of which single child to follow.
-/
public
def getChoiceNode (kind : SyntaxNodeKind) (args : Array Syntax) (n : Nat := 0) : Array Syntax :=
  if kind == `choice then #[args[n]?].reduceOption else args

/--
Splays the input syntax into a string.

There is a slight subtlety about `choice` nodes, that are traversed only once.
-/
partial
def _root_.Lean.Syntax.regString : Syntax → String
  | .node _ kind args => (getChoiceNode kind args).foldl (init := "") (· ++ ·.regString)
  | .ident i raw _ _ => let (l, t) := i.getLeadTrail; l ++ raw.toString ++ t
  | .atom i s => let (l, t) := i.getLeadTrail; l ++ s ++ t
  | .missing => ""

/-- Replaces the leading and trailing substrings in a `SourceInfo` with `"".toSubstring`. -/
def _root_.Lean.SourceInfo.removeSpaces : SourceInfo → SourceInfo
  | .original _ p _ q => .original "".toRawSubstring p "".toRawSubstring q
  | s => s
  --| .synthetic p q c => .synthetic p q c
  --| .none => .none

/-- For every node of the input syntax, replace the leading and trailing substrings in every
`SourceInfo` with `"".toSubstring`. -/
public partial
def _root_.Lean.Syntax.eraseLeadTrailSpaces : Syntax → Syntax
  | .node i k args => .node i.removeSpaces k (args.map (·.eraseLeadTrailSpaces))
  | .ident i raw v p => .ident i.removeSpaces raw v p
  | .atom i s => .atom i.removeSpaces s
  | .missing => .missing

def withVerbose {α} (v : Bool) (s : String) (a : α) : α :=
  if v then
    dbg_trace s
    a
  else
    a

/-- Answers whether a `Substring` starts with a space (` `), contains possibly more spaces,
until there is either `/ -` (without the space between `/` and `-`) or `--`. -/
public def onlineComment (s : Substring.Raw) : Bool :=
  (s.take 1).toString == " " &&
    #[ "/-", "--"].contains ((s.dropWhile (· == ' ')).take 2).toString

/--
Assumes that `pp` is either empty or a single space, as this is satisfied by the intended
application.

Checks whether `orig` is an "acceptable version" of `pp`:
1. if `pp` is a space, check that `orig` starts either
   * with a line break, or
   * with a single space and then a non-space character,
   * with at least one space and then a `onlineComment`;
2. if `pp` is empty, check that `orig` is empty as well or starts either
   * with a non-whitespace character,
   * with at least one space and then a `onlineComment`.

TODO: should item 2. actually check that there is no space and that's it?
-/
def validateSpaceAfter (orig pp : Substring.Raw) : Bool :=
  -- An empty `pp`ed tail sould correspond to
  -- an empty `orig`,
  -- something starting with a line break,
  -- something starting with some spaces and then a comment
  let orig1 := (orig.take 1).toString
  let orig2 := (orig.take 2).toString
  dbg_trace
    "pp.isEmpty {pp.isEmpty}\n\
    if {pp.isEmpty}:\n  \
      orig.takeWhile (·.isWhitespace): {orig.takeWhile (·.isWhitespace)}\n  \
      or\n  \
      onlineComment orig: {onlineComment orig}\n\
    if {!pp.isEmpty}:\n  \
      (orig1 == \"⏎\"): {(orig1 == "\n")}\n  \
      or\n  \
      onlineComment orig: {onlineComment orig}\n  \
      or\n  \
      orig1 == \" \" && !orig2.trim.isEmpty: {orig1 == " " && !orig2.trimAscii.isEmpty}"
  (pp.isEmpty && ((orig.takeWhile (·.isWhitespace)).isEmpty || onlineComment orig)) ||
    (
      (!pp.isEmpty) && ((orig1 == "\n") || onlineComment orig || (orig1 == " " && !orig2.trimAscii.isEmpty))
    )
/-
#eval show TermElabM _ from do
  let space : Substring := " ".toSubstring
  let spaceChar : Substring := " f".toSubstring
  let doublespaceChar : Substring := "  f".toSubstring
  let doublespace : Substring := "  ".toSubstring
  let noSpace : Substring := "".toSubstring
  let linebreak : Substring := "\n".toSubstring
  let commentInline : Substring := "  --".toSubstring
  let commentMultiline : Substring := "  /-".toSubstring -- -/ to preserve sanity
  -- `true`
  guard <| onlineComment commentInline
  guard <| onlineComment commentMultiline
  guard <| validateSpaceAfter spaceChar space
  guard <| validateSpaceAfter linebreak space
  guard <| validateSpaceAfter commentInline space
  guard <| validateSpaceAfter commentMultiline space
  guard <| validateSpaceAfter noSpace noSpace
  guard <| validateSpaceAfter "a".toSubstring noSpace
  -- `false`
  guard <| !onlineComment space
  guard <| !onlineComment doublespace
  guard <| !onlineComment noSpace
  guard <| !onlineComment linebreak
  -- A space not followed by a character is not accepted.
  guard <| !validateSpaceAfter space space
  guard <| !validateSpaceAfter doublespaceChar space
  guard <| !validateSpaceAfter space noSpace
  guard <| !validateSpaceAfter spaceChar noSpace
  guard <| !validateSpaceAfter doublespaceChar noSpace
-/

/-- Assume both substrings come from actual trails. -/
def validateSpaceAfter' (orig pp : Substring.Raw) : Bool :=
  -- An empty `pp`ed tail sould correspond to
  -- an empty `orig`,
  -- something starting with a line break,
  -- something starting with some spaces and then a comment
  let orig1 := (orig.take 1).toString
  let orig2 := (orig.take 2).toString
  let answer := (orig1 == "\n") ||
    (pp.isEmpty && ((orig.takeWhile (·.isWhitespace)).isEmpty || onlineComment orig)) ||
      (
        (!pp.isEmpty) && (onlineComment orig || (orig1 == " " && orig2 != "  "))
      )
  withVerbose (!answer)
    s!"\
    orig1 == \"⏎\": {orig1 == "\n"}\n\
    or\n  \
    pp.isEmpty {pp.isEmpty}\n\
    if {pp.isEmpty}:\n  \
      orig.takeWhile (·.isWhitespace): {orig.takeWhile (·.isWhitespace)}\n  \
      or\n  \
      onlineComment orig: {onlineComment orig}\n\
    if {!pp.isEmpty}:\n  \
      onlineComment orig: {onlineComment orig}\n  \
      or\n  \
      orig1 == \" \" && orig1 == orig2: {orig1 == " " && orig1 == orig2}"
      answer

/-
#eval show TermElabM _ from do
  let space : Substring := " ".toSubstring
  let spaceChar : Substring := " f".toSubstring
  let doublespaceChar : Substring := "  f".toSubstring
  let doublespace : Substring := "  ".toSubstring
  let noSpace : Substring := "".toSubstring
  let linebreak : Substring := "\n".toSubstring
  let commentInline : Substring := "  --".toSubstring
  let commentMultiline : Substring := "  /-".toSubstring -- -/ to preserve sanity
  -- `true`
  guard <| validateSpaceAfter' spaceChar space
  guard <| validateSpaceAfter' linebreak space
  guard <| validateSpaceAfter' commentInline space
  guard <| validateSpaceAfter' commentMultiline space
  guard <| validateSpaceAfter' noSpace noSpace
  guard <| validateSpaceAfter' "a".toSubstring noSpace
  -- A space not followed by a character *is accepted*.
  guard <| validateSpaceAfter' space space
  guard <| !validateSpaceAfter' doublespaceChar space
  -- `false`
  guard <| !validateSpaceAfter' space noSpace
  guard <| !validateSpaceAfter' spaceChar noSpace
  guard <| !validateSpaceAfter' doublespaceChar noSpace

#eval
  let origStr := "intro      --hi"
  let str := "intro hi"
  let orig : Substring := {origStr.toSubstring with startPos := ⟨"intro".length⟩}
  let pp : Substring := {str.toSubstring with startPos := ⟨"intro".length⟩}
  let pp : Substring := "".toSubstring
  dbg_trace "pp.isEmpty: {pp.isEmpty}, validate {validateSpaceAfter orig pp}"
  validateSpaceAfter orig pp

#eval validateSpaceAfter' " ".toSubstring " ".toSubstring
-/

structure Exceptions where
  orig : String
  pp : String
  pos : String.Pos.Raw
  kind : SyntaxNodeKind
  reason : String

instance : ToString Exceptions where
  toString
  | {orig := o, pp := pp, pos := p, kind := k, reason := r} =>
    s!"Exception\npos:  {p}\nkind: '{k}'\norig: '{o.norm}'\npret: '{pp.norm}'\nreason: {r}\n---"

def addException (e : Array Exceptions) (orig pp : String) (p : String.Pos.Raw) (k : SyntaxNodeKind) (reason : String) :
    Array Exceptions :=
  e.push <| Exceptions.mk orig pp p k reason


def validateAtomOrId (tot : Array Exceptions) (kind : SyntaxNodeKind) (i1 _i2 : SourceInfo) (s1 s2 : String) (str : Substring.Raw) :
    Substring.Raw × Array Exceptions :=
  let (_l1, t1) := i1.getLeadTrail
  --let (l2, t2) := i2.getLeadTrail
  --dbg_trace "removing '{s2}'"
  let stripString := consumeIgnoring s2.toRawSubstring str invisible|>.getD default --str.drop s2.length
  let trail := stripString.takeWhile (·.isWhitespace)
  --withVerbose (trail.isEmpty != t1.isEmpty) s!"Discrepancy at {s1}, orig: '{t1}' pped: '{trail}'"
  let isValid := validateSpaceAfter' t1.toRawSubstring trail
  --dbg_trace "{isValid} -- {(s1, s2)}: '{t1}', '{trail}'\n"
  let tot1 := if isValid then
                tot
              else
                dbg_trace "invalid with '{s1}' '{s2}' '{t1}' '{trail.toString}' '{stripString.startPos}' '{kind}'"
                addException tot t1 trail.toString stripString.startPos kind "invalid"
--consumeIgnoring s2.toSubstring str invisible
  --if ((!str.toString.startsWith s1) || (!str.toString.startsWith s2)) then
  if (((consumeIgnoring s1.toRawSubstring str invisible).isNone) ||
      ((consumeIgnoring s2.toRawSubstring str invisible).isNone)) then
    dbg_trace s!"something went wrong\n\
      --- All pretty {kind} ---\n{str.toString}\ndoes not start with either of the following\n\
      --- Orig ---\n'{s1.norm}'\n--- Pretty---\n'{s2.norm}'\n---\n{tot1}"
    match consumeIgnoring s2.toRawSubstring str invisible with
    | some leftOver =>
      (leftOver, addException tot1 t1 trail.toString stripString.startPos kind
        s!"wrong:\n'{s1}' or\n'{s2}' is not the start of\n'{str.toString}'")
    | none =>
      (stripString |>.dropWhile (·.isWhitespace), addException tot1 t1 trail.toString stripString.startPos kind s!"wrong: '{s1}' or '{s2}' is not the start of '{str.toString}'")
  else
    ( --withVerbose (!isValid) s!"Discrepancy at {s1}, orig: '{t1}' pped: '{trail}'"
      stripString |>.dropWhile (·.isWhitespace), tot1)

#guard validateSpaceAfter' " ".toRawSubstring " ".toRawSubstring

def exclusions : NameSet := NameSet.empty
  |>.insert ``Parser.Command.docComment

def scanWatching (verbose? : Bool) :
    Array Exceptions → SyntaxNodeKind → Syntax → Syntax → Substring.Raw → Substring.Raw × Array Exceptions
  | tot, k, .ident i1 s1 n1 p1, .ident i2 s2 n2 p2, str =>
    withVerbose verbose? "idents" <|
      validateAtomOrId tot k i1 i2 s1.toString s2.toString str
  | tot, k, .atom i1 s1, .atom i2 s2, str =>
    withVerbose verbose? "atoms" <|
      validateAtomOrId tot k i1 i2 s1 s2 str
  | tot, k, .node i1 s1 as1, ppstx@(.node i2 s2 as2), str =>
    let s1 := if s1 == `null then k else s1
    --if exclusions.contains s1 then
    --  dbg_trace "skipping {s1}"
    --  let endPos := ppstx.getTrailingTailPos?.get!
    --  let endPos := as2.back!.getTrailingTailPos?.get!
    --  let endPos := as2.back!.getRange?.get!.stop
    --  let endPos := ppstx.getRange?.get!.stop
    --  ({str with startPos := endPos}, tot)
    --else
    withVerbose (as1.size != as2.size) "** Error! **" <|
    withVerbose verbose? "nodes" <| Id.run do
      let mut pos := str.startPos
      let mut tots := tot
      for h : i in [:as1.size] do
        let a1 := as1[i]
        let a2 := as2[i]?.getD default
        let ({startPos := sp,..}, news) := scanWatching verbose? tots s1 a1 a2 {str with startPos := pos}
        pos := sp
        tots := news
      ({str with startPos := pos}, tots)
  | tot, k, s1, s2, str =>
    withVerbose verbose? "rest" <|
      (str, tot)

def modifyTail (si : SourceInfo) (newTrail : Substring.Raw) : SourceInfo :=
  match si with
  | .original lead pos _ endPos => .original lead pos newTrail endPos
  | _ => si

/--
Compares the two substrings `s` and `t`, with the expectation that `t` starts with `s`,
up to whitespace and guillemets (`«` and `»`).

It returns the substring of `t` that starts from the first position where it differs from `s`,
after it erased potential whitespace, taking care of preserving the last whitespace, if present.

The typical application is when `s` is the value of an atom/identifier leaf in `Syntax` and
`t` is the pretty-printed version of the whole syntax tree.
The main goal is to figure out what is the trailing whitespace substring
(usually either empty `""` or a single space `" "`).
-/
partial
def readWhile (s t : Substring.Raw) : Substring.Raw :=
  if s.isEmpty || t.isEmpty then t else
  let s1 := s.take 1
  let t1 := t.take 1
  if s1 == t1 then
    readWhile (s.drop 1) (t.drop 1)
  else
    if t1.trim.isEmpty then
      readWhile s t.trimLeft
    else
    if s1.trim.isEmpty then
      readWhile s.trimLeft t
    else
    if #["«", "»"].contains t1.toString then
      readWhile s (t.drop 1)
    else
    if #["«", "»"].contains s1.toString then
      readWhile (s.drop 1) t
    else
      t

#eval show Lean.Elab.Term.TermElabM _ from do
  let s := "/- alsdkj la l    asklj  ew ljr  wer-/".toRawSubstring
  let t := "/- alsdkj la l asklj ew ljr    wer-/ theorem".toRawSubstring
  guard <| (readWhile s t).toString == " theorem"
  let t := "/- alsdkj la l asklj ew ljr    wer-/theorem".toRawSubstring
  guard <| (readWhile s t).toString == "theorem"

#eval show Lean.Elab.Term.TermElabM _ from do
  let s := "example".toRawSubstring
  let t := "example := 0".toRawSubstring
  guard <| (readWhile s t).toString == " := 0"
  let t := ":= 0".toRawSubstring
  guard <| (readWhile (" :=".toRawSubstring) t).toString == " 0"
  guard <| (readWhile (" := ".toRawSubstring) t).toString == "0"

public def _root_.Substring.Raw.toRange (s : Substring.Raw) : Lean.Syntax.Range where
  start := s.startPos
  stop := s.stopPos

public structure mex where
  rg : Lean.Syntax.Range
  error : String
  kinds : Array SyntaxNodeKind

def mex.toString {m} [Monad m] [MonadFileMap m] (ex : mex) : m String := do
  let fm ← getFileMap
  return s!"{ex.error} {(fm.toPosition ex.rg.start, fm.toPosition ex.rg.stop)} ({ex.kinds})"

/--
A structure combining the various exceptions to the `commandStart` linter.
* `kinds` is the array of `SyntaxNodeKind`s that are ignored by the `commandStart` linter.
* `depth` represents how many `SyntaxNodeKind`s the `commandStart` linter climbs, in search of an
  exception.

  A depth of `none`, means that the linter ignores nodes starting with the given `SyntaxNodeKind`
  and any sub-node.

  A depth of `some n` means that the linter will only ignore the first `n` `SyntaxNodeKind`s
  starting from the given `SyntaxNodeKind` and resumes checking for all deeper nodes.
-/
public
structure ExcludedSyntaxNodeKind where
  /-- `kinds` is the array of `SyntaxNodeKind`s that are ignored by the `commandStart` linter. -/
  kinds : Array SyntaxNodeKind
  /--
  `depth` represents how many `SyntaxNodeKind`s the `commandStart` linter climbs, in search of an
  exception.

  A depth of `none`, means that the linter ignores nodes starting with the given `SyntaxNodeKind`
  and any sub-node.

  A depth of `some n` means that the linter will only ignore the first `n` `SyntaxNodeKind`s
  starting from the given `SyntaxNodeKind` and resumes checking for all deeper nodes.
  -/
  depth : Option Nat

/--
`unparseable` are the `SyntaxNodeKind`s that block the `commandStart` linter: their appearance
anywhere in the syntax tree makes the linter ignore the whole command.

This is the reason their `depth` is `none`.
-/
public
def unparseable : ExcludedSyntaxNodeKind where
  kinds := #[
    ``Parser.Command.macro_rules,
    ``runCmd,
  ]
  depth := none

/--
These are the `SyntaxNodeKind`s for which we want to ignore the pretty-printer.

Deeper nodes are *not* inspected.
-/
public
def totalExclusions : ExcludedSyntaxNodeKind where
  kinds := #[
    -- Each entry prevents the formatting of...
    ``Parser.Command.docComment, -- of doc-strings.
    ``Parser.Command.moduleDoc, -- of module docs.
    ``«term{_:_//_}», -- of `{a // ...}`.
    ``«term{_}», -- of a singleton `{a}`.
    ``«term{}»,  -- of the empty set, the pretty-printer prefers `{ }`
    `Mathlib.Meta.setBuilder, -- of `{a | ...}`.
    ``Parser.Tactic.tacticSeqBracketed, -- of `{ tactics }`.
    ``Parser.Command.macro, -- of `macro`.
    ``Parser.Command.elab, -- of `elab`.
    ``Parser.Command.elab_rules, -- of `elab_rules`.
    `Mathlib.Meta.«term{_|_}», -- of `{ f x y | (x : X) (y : Y) }`.
    ``«term[_]», -- of lists.
    ``«term#[_,]», -- of arrays.
    ``Parser.Term.anonymousCtor, -- of `⟨...⟩`.
    ``Parser.Command.syntax, -- of `syntax ...`.
    `Aesop.Frontend.Parser.declareRuleSets, -- of `declare_aesop_rule_sets`.
    `Aesop.Frontend.Parser.featIdent, -- of `attribute [aesop safe (rule_sets := [CategoryTheory])] Subsingleton.elim`
    ``«term_::_», -- of lists.
    `Stream'.«term_::_», -- of `Stream'` notation, analogous to lists.
    `Batteries.Util.LibraryNote.commandLibrary_note___, -- of `library_note "Title"/-- Text -/`.
    `Mathlib.Notation3.notation3, -- of `notation3`.
    ``Parser.Term.structInstField, -- of the `where` fields: the LHS pps with virtually no spaces.
    ``Parser.Term.structInst, -- of the `where` fields: the LHS pps with virtually no spaces.
    `Lean.Parser.Command.grindPattern, -- `grind_pattern A => x, y` prints no space after `,`
  ]
  depth := none

def ignoreSpaceAfter : ExcludedSyntaxNodeKind where
  kinds := #[
    ``«term¬_»,
  ]
  depth := some 2

/--
These are the `SyntaxNodeKind`s for which the pretty-printer would likely not space out from the
following nodes, but we overrule it and place a space anyway.
-/
def forceSpaceAfter : ExcludedSyntaxNodeKind where
  kinds := #[
    `token.«·», -- the focusing dot `·` in `conv` mode
    ``termThrowError__, -- `throwError "message"`
    -- Syntax nodes that do not pretty-print with a space, if followed by a parenthesis `()`
    ``Parser.Tactic.rcases, -- `rcases (a)`
    ``Parser.Tactic.replace, -- `replace (a)`
    ``Parser.Term.whereDecls, -- `where`
  ]
  depth := some 2

def forceSpaceAfter' : ExcludedSyntaxNodeKind where
  kinds := #[
    `atom.«have», -- `have (a)` in term mode.
    `atom.«let», -- `let (a)` in term mode.
  ]
  depth := some 1

/--
These are the `SyntaxNodeKind`s for which the pretty-printer would likely space out from the
following nodes, but we overrule it and do not place a space.
-/
def forceNoSpaceAfter : ExcludedSyntaxNodeKind where
  kinds := #[
    --``Parser.Term.doubleQuotedName,
    `atom.«`», -- useful for double-quoted names
  ]
  depth := some 2

/--
Checks whether the input array `ks` of `SyntaxNodeKind`s matches the conditions implied by
the `ExcludedSyntaxNodeKind` `exc`.

The function takes into account what the `SyntaxNodeKind`s in `ks` are, as well as their
depth, as required by `exc.depth`.
-/
public
def ExcludedSyntaxNodeKind.contains (exc : ExcludedSyntaxNodeKind) (ks : Array SyntaxNodeKind) :
    Bool :=
  let lastNodes := if let some n := exc.depth then ks.drop (ks.size - n) else ks
  !(lastNodes.filter exc.kinds.contains).isEmpty

public
def reportedAndUnreportedExceptions (as : Array mex) : Array mex × Array mex :=
  as.partition fun a =>
    (!totalExclusions.contains a.kinds) && (!ignoreSpaceAfter.contains a.kinds)

--def filterSortExceptions (as : Array mex) : Array mex :=
--  let filtered := as.filter fun a =>
--    (!totalExclusions.contains a.kinds) && (!ignoreSpaceAfter.contains a.kinds)
--  filtered.qsort (·.rg.start < ·.rg.start)

structure AfterAtom where
  /-- `next` is either `" ".toSubstring` or `"".toSubstring`, depending on whether the
  character following the current identifier/atom is required to be followed by a space or not. -/
  next : Substring.Raw
  /-- `read` is the pretty-printed substring, starting from after the current identifier/atom,
  dropping also eventual leading whitespace. -/
  strNew : Substring.Raw

structure PPinstruction where
  pos : String.Pos.Raw
  after : Bool := true
  space : Bool := true
  deriving Inhabited

public
structure PPref where
  pos : String.Pos.Raw
  ok : Bool
  bracket : Option String.Pos.Raw := none
  kinds : Array SyntaxNodeKind
  deriving Inhabited

/-- A mapping from each start/ending position of each atom in the string generating the original
syntax with the corresponding start/ending position in the pretty-printed string generated by
stripping all comments and whitespace. -/
public
abbrev Correspondence := Std.HashMap String.Pos.Raw PPref

def atomOrIdentEndPos {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (verbose? : Bool) (k : Array SyntaxNodeKind) (orig pp : Substring.Raw) :
    m String.Pos.Raw := do
  let ppDropOrig := readWhile orig pp
  if verbose? then
    if ppDropOrig == pp && (!ppDropOrig.isEmpty) then
      -- Temporary change, to reduce warning spam.
      if !(k.contains `hygieneInfo && !k.contains `choice) && False then
        logWarning m!"No change at{indentD m!"'{ppDropOrig}'"}\n{k.map MessageData.ofConstName}\n\n\
        Maybe because the `SyntaxNodeKind`s contain:\n\
        hygieneInfo: {k.contains `hygieneInfo}\n\
        choice: {k.contains `choice}"
  --dbg_trace "ppDropOrig[{ppDropOrig.startPos}]: '{ppDropOrig.toString.norm}'"
  pure ppDropOrig.startPos

public
partial
def generateCorrespondence {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (verbose? : Bool) :
    Correspondence → Array SyntaxNodeKind → Syntax → Substring.Raw → m (Substring.Raw × Correspondence)
  | corr, k, .ident info rawVal _val _pre, str => do
    --dbg_trace "kinds:\n{k}"
    --dbg_trace "rawVal: '{rawVal}'"
    let ppEndPos ← atomOrIdentEndPos verbose? (k.push (.str `ident rawVal.toString)) rawVal str
    let (_, tail) := info.getLeadTrail
    --dbg_trace "(tail: '{tail.norm}', (tail[0], str[{ppEndPos}]) ('{(tail.take 1).norm}' '{(str.get ppEndPos)}'))\n({str.startPos}, {str.stopPos})\n"
    let cond := tail.take 1 == (str.take 1).toString
    pure (
      {str with startPos := ppEndPos},
      -- Is `getD default` a good idea?  It resolves some panics, but there may be a better default
      corr.alter ((info.getTrailing?.getD default).startPos) fun a => if (a.getD default).bracket.isSome then a else PPref.mk ppEndPos cond none (k.push (.str `ident rawVal.toString)))
  | corr, k, .atom info val, str => do
    --dbg_trace "kinds:\n{k}"
    --dbg_trace "val: '{val}'"
    let ppEndPos ← atomOrIdentEndPos verbose? (k.push (.str `atom val)) val.toRawSubstring str
    let (_, tail) := info.getLeadTrail
    --dbg_trace "(tail: '{tail.norm}', (tail[0], str[{ppEndPos}]) ('{(tail.take 1).norm}' '{(str.get ppEndPos)}'))\n"
    let cond := tail.take 1 == "".push (str.get ppEndPos)
    pure (
      {str with startPos := ppEndPos},
      -- Is `getD default` a good idea?  It resolves some panics, but there may be a better default
      corr.alter ((info.getTrailing?.getD default).startPos) fun a => if (a.getD default).bracket.isSome then a else PPref.mk ppEndPos cond none (k.push (.str `atom val)))
  | corr, k, _stx@(.node _info kind args), str => do
    --let corr :=
    --  if (k.back?.getD .anonymous) == ``Parser.Term.structInst then
    --    --dbg_trace "inserting {stx} {(stx.getRange?.map fun | {start := a, stop := b} => (a, b))}\n"
    --    corr
    --    --corr.insert stx.getTailPos?.get! <| PPref.mk stx.getPos?.get! true (some stx.getPos?.get!)
    --  else
    --    --dbg_trace "not inserting\n"
    --    corr
    (getChoiceNode kind args).foldlM (init := (str, corr)) fun (str, corr) arg => do
      generateCorrespondence verbose? corr (k.push kind) arg str
  | corr, _, _stx, str => do
    pure (str, corr)

partial
def _root_.String.Slice.mkGroups (s : String.Slice) (n : Nat) : List String.Slice :=
  if n == 0 || s.positions.count ≤ n then [s] else
  s.take n :: (s.drop n).mkGroups n

-- TODO: fix this and re-enable it!
-- def byTens (s : String) (n : Nat := 9) : String.Slice :=
--   "\n".intercalate <| ("".intercalate <| (List.range n).map (fun n => s!"{(n + 1) % 10}")) :: (s.toSlice.mkGroups n)

public
def mkRangeError (ks : Array SyntaxNodeKind) (orig pp : Substring.Raw) :
    Option (Lean.Syntax.Range × MessageData × String) := Id.run do
  let origWs := orig.takeWhile (·.isWhitespace)
  --dbg_trace "here for '{(orig.take 10).toString}'\n{ks}\n"
  --dbg_trace ks
  if forceSpaceAfter.contains ks || forceSpaceAfter'.contains ks  then
    --dbg_trace "forceSpaceAfter"
    let space := if (pp.take 1).trim.isEmpty then "" else " "
    if origWs.isEmpty then
      return some (⟨origWs.startPos, origWs.next origWs.startPos⟩, "add space in the source", space)
    else
    if origWs.toString.length == 1 || (orig.take 1).toString == "\n" then
      return none
    else
      let origWsNext := origWs.drop 1
      return some (⟨origWsNext.startPos, origWsNext.stopPos⟩, "remove space in the source", space)
  else if forceNoSpaceAfter.contains ks then
    --dbg_trace "forceNoSpaceAfter"
    if !origWs.isEmpty then
      return some (⟨origWs.startPos, origWs.stopPos⟩, "remove space in the source", "")
    else
      return none
  else
  let ppNext := pp.take 1
  -- The next pp-character is a space
  if ppNext.trim.isEmpty then
    --dbg_trace "next is whitespace"
    if onlineComment orig then
      return none
    if origWs.isEmpty then
      return some (⟨orig.startPos, orig.next orig.startPos⟩, "add space in the source", "")
    let origWsNext := origWs.drop 1
    let pastSpaces := origWs.dropWhile (· == ' ')
    if (origWs.take 1).toString == " " && (pastSpaces.take 1).toString == "\n" then
      return some (⟨origWs.startPos, pastSpaces.stopPos⟩, "Please remove spaces before line breaks", "")
    else
      if (origWs.take 1).toString != "\n" && (!origWsNext.isEmpty) then
        return some (⟨origWsNext.startPos, origWsNext.stopPos⟩, "remove space in the source", "")
  -- The next pp-character is not a space
  if !ppNext.trim.isEmpty then
    --dbg_trace "next is not whitespace"
    if !origWs.isEmpty then
      let wsName := if (origWs.take 1).toString == " " then "space" else "line break"
      let s := if origWs.toString.length == 1 || (origWs.take 1).toString == "\n" then "" else "s"
      return some (⟨origWs.startPos, origWs.stopPos⟩, m!"remove {wsName}{s} in the source", "")
  return none

/-- Assumes that the `startPos` of the string is where the "center" of the window will be. -/
public
def mkWdw (s : Substring.Raw) (mid : String := "") : String :=
  let p := s.startPos
  let fromStart := {s with startPos := 0, stopPos := p}
  let toEnd := {s with startPos := p, stopPos := s.str.rawEndPos}
  let leftWhitespaceAndWord := fromStart.trimRight.dropRightWhile (!·.isWhitespace)
  let rightWhitespaceAndWord := toEnd.trimLeft.dropWhile (!·.isWhitespace)
  s!"\
    {{s with startPos := leftWhitespaceAndWord.stopPos, stopPos := p}}\
    {mid}\
    {{s with startPos := p, stopPos := rightWhitespaceAndWord.startPos}}".trimAscii.toString.norm

/-
This part of the code\n  '{origWindow.trim}'\n\
should be written as\n  '{expectedWindow}'\n"
-/

open Lean Elab Command in
elab "#show_corr " cmd:command : command => do
  elabCommand cmd
  let orig := cmd.raw.getSubstring?.getD default
  let stxNoSpaces := cmd.raw.eraseLeadTrailSpaces
  if let some pretty := ← Mathlib.Linter1.pretty stxNoSpaces then
    let pp := pretty.toRawSubstring
    let (_, corr) ← generateCorrespondence true Std.HashMap.emptyWithCapacity #[] cmd pretty.toRawSubstring
    for (origPos, ppR) in corr do
      let ppPos := ppR.pos
      let origAtPos := {orig with startPos := origPos}
      let ppAtPos := {pp with startPos := ppPos}
      if let some (rg, msg) := mkRangeError ppR.kinds origAtPos ppAtPos then
        -- TODO: temporary change, hopefully reduces false positives!
        if mkWdw origAtPos != mkWdw ppAtPos && !(mkWdw origAtPos).contains '¬' then
          logWarningAt (.ofRange rg)
            m!"{msg}\n\
            This part of the code\n  '{mkWdw origAtPos}'\n\
            should be written as\n  '{indentD <| mkWdw ppAtPos}'\n"
    let fm ← getFileMap
    let sorted := corr.toArray.qsort (·.1 < ·.1)
    let mut msgs := #[]
    for (a, b) in sorted do
      msgs := msgs.push (
        {fm.toPosition a with column := (fm.toPosition a).column + 1},
          b.pos,
          "'".push (pretty.toRawSubstring.get (pretty.toRawSubstring.prev b.pos))
            |>.push (pretty.toRawSubstring.get b.pos)
            |>.push (pretty.toRawSubstring.get (pretty.toRawSubstring.next b.pos))
            |>.push '\'',
          b.ok,
          b.bracket,
        )
    -- TODO: fix `byTens` and re-enable this logging output
    --logInfo <| .joinSep (msgs.toList.map (m!"{·}") ++ [m!"{byTens pretty (min pretty.length 100)}"]) "\n"
  else logWarning "Error"

-- #show_corr
-- --inspect
-- #check (  { default := (/-  -/) }:    Inhabited   Unit
-- )

def processAtomOrIdent {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (verbose? : Bool) (k : Array SyntaxNodeKind) (val str : Substring.Raw) :
    m (AfterAtom × PPinstruction) := do
  --dbg_trace "forceSpaceAfter.contains {k}: {forceSpaceAfter.contains k}\nStarting with '{val}'\n"
  let read := readWhile val str
  if verbose? then
    if read == str && (!read.isEmpty) then
      logWarning m!"No change at{indentD m!"'{read}'"}\n{k.map MessageData.ofConstName}\n\n\
      Maybe because the `SyntaxNodeKind`s contain:\n\
      hygieneInfo: {k.contains `hygieneInfo}\n\
      choice: {k.contains `choice}"
  let (next, strNew, ppInstr) :=
    -- Case `read = " "`
    if (read.take 1).toString == " "
    then
      -- Case `read = " "` but we do not want a space after
      if forceNoSpaceAfter.contains k then
        ("".toRawSubstring, read.drop 1, {pos := (read.drop 1).startPos, space := false})
      else
        (" ".toRawSubstring, read.drop 1, {pos := (read.drop 1).startPos})
    else
    -- Case `read = ""` but we want a space after anyway
    if forceSpaceAfter.contains k || forceSpaceAfter'.contains k then
      --dbg_trace "adding a space at '{read}'\n"
      (" ".toRawSubstring, read, {pos := read.startPos})
    -- Case `read = ""` and we follow the pretty-printer recommendation
    else
      ("".toRawSubstring, read, {pos := read.startPos, space := false})
  pure (AfterAtom.mk next strNew, ppInstr)

/--
`insertSpacesAux verbose? noSpaceStx prettyString`
scans the syntax tree `noSpaceStx` and, whenever it finds an `atom` or `ident` node,
it compares it with the substring `prettyString`, consuming the value of the `atom`/`ident` and
appending the following whitespace as trailing substring in the `SourceInfo`, if such a space is
present.

This essentially converts `noSpaceStx` into a `Syntax` tree whose traversal reconstructs exactly
`prettyString`.
-/
public
partial
def insertSpacesAux {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (verbose? : Bool) :
    Array SyntaxNodeKind → Syntax → Substring.Raw → m (Syntax × Substring.Raw)
  | k, .ident info rawVal val pre, str => do
    let (⟨next, strNew⟩, _) ← processAtomOrIdent verbose? (k.push (.str `ident rawVal.toString)) rawVal str
    if false then
      dbg_trace
        s!"* ident '{rawVal}'\nStr: '{str}'\nNxt: '{next}'\nNew: '{strNew}'\n"
    pure (.ident (modifyTail info next) rawVal val pre, strNew)
  | k, .atom info val, str => do
    let (⟨next, strNew⟩, _) ← processAtomOrIdent verbose? (k.push (.str `atom val)) val.toRawSubstring str
    if false then
      dbg_trace
        s!"* atom '{val}'\nStr: '{str}'\nNxt: '{next}'\nNew: '{strNew}'\n"
    pure (.atom (modifyTail info next) val, strNew)
  | k, .node info kind args, str => do
    --let kind := if kind == `null then k else kind
    let mut str' := str
    let mut stxs := #[]
    for arg in getChoiceNode kind args do
      let (newStx, strNew) ← insertSpacesAux verbose? (k.push kind) arg str'
      if false then
        logInfo m!"'{strNew}' intermediate string at {k.push kind}"
      str' := strNew.trimLeft
      stxs := stxs.push newStx
    pure (.node info kind stxs, str')
  | _, stx, str => do
    pure (stx, str)
