/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

import Lean.Parser.Syntax
public meta import Mathlib.CommandStartAux

/-!
# The `commandStart` linter

The `commandStart` linter emits a warning if
* either a command does not start at the beginning of a line;
* or the "hypotheses segment" of a declaration does not coincide with its pretty-printed version.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter1

open Lean in
/--
`insertSpaces verbose? stx` first replaces in `stx` every `trailing` substring in every `SourceInfo`
with either `"".toSubstring` or `" ".toSubstring`, according to what the pretty-printer would
place there.

In particular, it erases all comments embedded in `SourceInfo`s.
-/
def insertSpaces (verbose? : Bool) (stx : Syntax) : CommandElabM (Option Syntax) := do
  let stxNoSpaces := stx.eraseLeadTrailSpaces
  if let some pretty := ← Mathlib.Linter1.pretty stxNoSpaces then
    let withSpaces ← insertSpacesAux verbose? #[stx.getKind] stx pretty.toRawSubstring
    return withSpaces.1
  else return none

def allowedTrail (ks : Array SyntaxNodeKind) (orig pp : Substring.Raw) : Option mex :=
  let orig1 := (orig.take 1).toString
  if orig.toString == pp.toString then none else
  -- Case `pp = ""`
  if pp.isEmpty then
    match orig1 with
    | " " => some ⟨orig.toRange, "remove space", ks⟩
    | "\n" => some ⟨orig.toRange, "remove line break", ks⟩
    | _ => some ⟨orig.toRange, "please, report this issue!", ks⟩ -- is this an unreachable case?
  -- Case `pp = " "`
  else
    if orig.isEmpty then
      let misformat : Substring.Raw := {orig with stopPos := orig.stopPos.increaseBy 1}
      some ⟨misformat.toRange, "add space", ks⟩
    else
    -- Allow line breaks
    if (orig.take 1).toString == "\n" then
      none
    else
    -- Allow comments
    if onlineComment orig then
      none
    else
    if (2 ≤ orig.toString.length) then
      some ⟨(orig.drop 1).toRange, if (orig.take 1).toString == "\n" then "remove line break" else "remove space", ks⟩
    else
      default

def _root_.Lean.SourceInfo.compareSpaces (ks : Array SyntaxNodeKind) :
    SourceInfo → SourceInfo → Option mex
  | .original _ _ origTrail .., .original _ _ ppTrail .. =>
    allowedTrail ks origTrail ppTrail
  | _, _ => none

partial
def _root_.Lean.Syntax.compareSpaces : Array SyntaxNodeKind → Array mex → Syntax → Syntax → Array mex
  | kinds, tot, .node _ kind a1, .node _ _ a2 =>
    let (a1, a2) := (getChoiceNode kind a1, getChoiceNode kind a2)
    a1.zipWith (fun a b => a.compareSpaces (kinds.push kind) tot b) a2 |>.flatten
  | kinds, tot, .ident origInfo rawVal .., .ident ppInfo .. =>
    if let some e := origInfo.compareSpaces (kinds.push (.str `ident rawVal.toString)) ppInfo
    then
      tot.push e else tot
  | kinds, tot, .atom origInfo val .., .atom ppInfo .. =>
    if let some e := origInfo.compareSpaces (kinds.push (.str `atom val)) ppInfo
    then
      tot.push e else tot
  | _, tot, _, _ => tot
--  | tot, .missing .., .missing .. => tot
--  | tot, .node _ k _, _ => tot
--  | tot, _, .node _ k _ => tot
--  | tot, .atom .., _ => tot
--  | tot, _, .atom .. => tot
--  | tot, .ident .., _ => tot
--  | tot, _, .ident .. => tot

open Parser in
/-- `captureException env s input` uses the given `Environment` `env` to parse the `String` `input`
using the `ParserFn` `s`.

This is a variation of `Lean.Parser.runParserCategory`.
-/
def captureException (env : Environment) (s : ParserFn) (input : String) : Except String Syntax :=
  let ictx := mkInputContext input "<input>"
  let s := s.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if !s.allErrors.isEmpty then
    .error (s.toErrorMsg ictx)
  else if String.Pos.Raw.atEnd ictx.input s.pos then
    .ok s.stxStack.back
  else
    .error ((s.mkError "end of input").toErrorMsg ictx)

/-- Returning `none` denotes a processing error. -/
def getExceptions (stx : Syntax) (verbose? : Bool := false) :
    CommandElabM (Option (Array mex)) := do
  let stxNoTrail := stx.unsetTrailing
  let s ← get
  let insertSpace ← insertSpaces verbose? stx
  set s
  if let some stxNoSpaces := insertSpace then
    if verbose? then
      logInfo m!"Pretty-printed syntax:\n{stxNoSpaces}"
    return stxNoTrail.compareSpaces #[] #[] stxNoSpaces
  else
    return none

/--
Scan the two input strings `L` and `M`, assuming `M` is the pretty-printed version of `L`.
This almost means that `L` and `M` only differ in whitespace.

While scanning the two strings, accumulate any discrepancies --- with some heuristics to avoid
flagging some line-breaking changes.
(The pretty-printer does not always produce desirably formatted code.)

The `rebuilt` input gets updated, matching the input `L`, whenever `L` is preferred over `M`.
When `M` is preferred, `rebuilt` gets appended the string
* `addSpace`, if `L` should have an extra space;
* `removeSpace`, if `L` should not have this space;
* `removeLine`, if this line break should not be present.

With the exception of `addSpace`, in the case in which `removeSpace` and `removeLine` consist
of a single character, then number of characters added to `rebuilt` is the same as the number of
characters removed from `L`.
-/
partial
def parallelScanAux (as : Array FormatError) (rebuilt L M addSpace removeSpace removeLine : String) :
    String × Array FormatError :=
  if M.trimAscii.isEmpty then (rebuilt ++ L.toSlice, as) else
  -- We try as hard as possible to scan the strings one character at a time.
  -- However, single line comments introduced with `--` pretty-print differently than `/--`.
  -- So, we first look ahead for `/--`: the linter will later ignore doc-strings, so it does not
  -- matter too much what we do here and we simply drop `/--` from the original string and the
  -- pretty-printed one, before continuing. -- -/
  -- Next, if we already dealt with `/--`, finding a `--` means that this is a single line comment
  -- (or possibly a comment embedded in a doc-string, which is ok, since we eventually discard
  -- doc-strings).  In this case, we drop everything until the following line break in the
  -- original syntax, and for the same amount of characters in the pretty-printed one, since the
  -- pretty-printer *erases* the line break at the end of a single line comment.
  --dbg_trace (L.take 3, M.take 3)
  if (L.take 3) == "/--".toSlice && (M.take 3) == "/--".toSlice then
    parallelScanAux as (rebuilt ++ "/--") (L.drop 3).copy (M.drop 3).copy addSpace removeSpace removeLine else
  if (L.take 2) == "--".toSlice
  then
    let newL := L.dropWhile (· != '\n')
    let diff := L.length - newL.copy.length
    -- Assumption: if `L` contains an embedded inline comment, so does `M`
    -- (modulo additional whitespace).
    -- This holds because we call this function with `M` being a pretty-printed version of `L`.
    -- If the pretty-printer changes in the future, this code may need to be adjusted.
    let newM := M.dropWhile (· != '-') |>.drop diff
    parallelScanAux as (rebuilt ++ (L.takeWhile (· != '\n')).toString ++ (newL.takeWhile (·.isWhitespace)).toString) newL.trimAsciiStart.copy newM.trimAsciiStart.copy addSpace removeSpace removeLine
  else
  if (L.take 2) == "-/".toSlice
  then
    let newL := L.drop 2 |>.trimAsciiStart
    let newM := M.drop 2 |>.trimAsciiStart
    parallelScanAux as (rebuilt ++ "-/" ++ ((L.drop 2).takeWhile (·.isWhitespace)).toString) newL.copy newM.copy addSpace removeSpace removeLine
  else
  let ls := L.drop 1
  let ms := M.drop 1
  let lf := L.front
  let m := M.front
  --match L.front with
  --| ' ' =>
  if lf == ' ' then
    let newAs := if m.isWhitespace then as else pushFormatError as (mkFormatError L M "extra space")
    let rebs := if m.isWhitespace then rebuilt.push ' ' else rebuilt ++ removeSpace
    let newLs := if m.isWhitespace then ls.trimAsciiStart.toString else ls.toString
    let newMs := if m.isWhitespace then ms.trimAsciiStart.toString else M
    parallelScanAux newAs rebs newLs newMs addSpace removeSpace removeLine
  else if lf == '\n' then
  --| '\n' =>
    if m.isWhitespace then
      parallelScanAux as (rebuilt ++ (L.takeWhile (·.isWhitespace)).toString) ls.toString.trimAsciiStart.toString ms.toString.trimAsciiStart.toString addSpace removeSpace removeLine
    else
      parallelScanAux (pushFormatError as (mkFormatError L M "remove line break")) (rebuilt ++ removeLine ++ (ls.takeWhile (·.isWhitespace)).toString) ls.toString.trimAsciiStart.toString M addSpace removeSpace removeLine
  else
    let l := lf
  --| l => -- `l` is not whitespace
    if l == m then
      parallelScanAux as (rebuilt.push l) ls.toString ms.toString addSpace removeSpace removeLine
    else
      if m.isWhitespace then
        parallelScanAux (pushFormatError as (mkFormatError L M "missing space")) ((rebuilt ++ addSpace).push ' ') L ms.trimAsciiStart.copy addSpace removeSpace removeLine
    else
      -- If this code is reached, then `L` and `M` differ by something other than whitespace.
      -- This should not happen in practice.
      (rebuilt, pushFormatError as (mkFormatError ls.copy ms.copy "Oh no! (Unreachable?)"))
--#exit
@[inherit_doc parallelScanAux]
def parallelScan (src fmt : String) : Array FormatError :=
  let (_expected, formatErrors) := parallelScanAux ∅ "" src fmt "🐩" "🦤" "😹"
  --dbg_trace "src:\n{src}\n---\nfmt:\n{fmt}\n---\nexpected:\n{expected}\n---"
  formatErrors

partial
def _root_.Lean.Syntax.compareToString : Array FormatError → Syntax → String → Array FormatError
  | tot, .node _ kind args, s =>
    (getChoiceNode kind args).foldl (init := tot) (· ++ ·.compareToString tot s)
  | tot, .ident i raw _ _, s =>
    let (l, t) := i.getLeadTrail
    let (_r, f) := parallelScanAux tot "" (l ++ raw.toString ++ t) s "🐩" "🦤" "😹"
    --dbg_trace "'{r}'"
    f
  | tot, .atom i s', s => --compareLeaf tot i.getLeadTrail s' s
    let (l, t) := i.getLeadTrail
    let (_r, f) := parallelScanAux tot "" (l ++ s' ++ t) s "🐩" "🦤" "😹"
    --dbg__trace "'{r}'"
    f
  | tot, .missing, _s => tot

partial
def _root_.Lean.Syntax.compare : Syntax → Syntax → Array SyntaxNodeKind
  | .node _ _ a1, .node _ _ a2 => a1.zipWith (fun a b => a.compare b) a2 |>.flatten
  | .ident .., .ident .. => #[]
  | .atom .., .atom .. => #[]
  | .missing .., .missing .. => #[]
  | .node _ k _, _ => #[k ++ `left]
  | _, .node _ k _ => #[k ++ `right]
  | .atom .., _ => #[`atomLeft]
  | _, .atom .. => #[`atomRight]
  | .ident .., _ => #[`identLeft]
  | _, .ident .. => #[`identRight]

/-
open Lean Elab Command in
elab "#comp " cmd:command : command => do
  elabCommand cmd
  let cmdString := cmd.raw.regString
  let pp ← pretty cmd
  dbg_trace "---\n{cmdString}\n---\n{pp}\n---"
  let comps := cmd.raw.compareToString #[] pp
  dbg_trace comps
--  dbg_trace "From start: {comps.map (cmdString.length - ·) |>.reverse}"
  --logInfo m!"{cmd}"
-/

namespace Style.CommandStart

/--
`unlintedNodes` contains the `SyntaxNodeKind`s for which there is no clear formatting preference:
if they appear in surface syntax, the linter will ignore formatting.

Currently, the unlined nodes are mostly related to `Subtype`, `Set` and `Finset` notation and
list notation.
-/
abbrev unlintedNodes := #[
  -- # set-like notations, have extra spaces around the braces `{` `}`

  -- subtype, the pretty-printer prefers `{ a // b }`
  ``«term{_:_//_}»,
  -- set notation, the pretty-printer prefers `{ a | b }`
  `«term{_}»,
  -- empty set, the pretty-printer prefers `{ }`
  ``«term{}»,
  -- various set builder notations, the pretty-printer prefers `{ a : X | p a }`
  `Mathlib.Meta.setBuilder,
  `Mathlib.Meta.«term{_|_}»,

  -- The pretty-printer lacks a few spaces.
  ``Parser.Command.syntax,

  -- # misc exceptions

  -- We ignore literal strings.
  `str,

  -- list notation, the pretty-printer prefers `a :: b`
  ``«term_::_»,

  -- negation, the pretty-printer prefers `¬a`
  ``«term¬_»,

  -- declaration name, avoids dealing with guillemets pairs `«»`
  ``Parser.Command.declId,

  `Mathlib.Tactic.superscriptTerm, `Mathlib.Tactic.subscript,

  -- notation for `Bundle.TotalSpace.proj`, the total space of a bundle
  -- the pretty-printer prefers `π FE` over `π F E` (which we want)
  `Bundle.termπ__,

  -- notation for `MeasureTheory.condExp`, the spaces around `|` may or may not be present
  `MeasureTheory.«term__[_|_]»,

  -- notation for `Finset.slice`, the pretty-printer prefers `𝒜 #r` over `𝒜 # r` (mathlib style)
  `Finset.«term_#_»,

  -- The docString linter already takes care of formatting doc-strings.
  ``Parser.Command.docComment,

  -- The pretty-printer adds a space between the backticks and the actual name.
  ``Parser.Term.doubleQuotedName,

  -- the `f!"..."` for interpolating a string
  ``Std.termF!_,

  -- `{structure}`
  ``Parser.Term.structInst,

  -- `let (a) := 0` pretty-prints as `let(a) := 0`, similarly for `rcases`.
  ``Parser.Term.let,
  ``Parser.Tactic.rcases,

  -- sometimes, where there are multiple fields, it is convenient to end a line with `⟨` and then
  -- align the indented fields on the successive lines, before adding the closing `⟩`.
  ``Parser.Term.anonymousCtor,
  -- similarly, we ignore lists and arrays
  ``«term[_]», ``«term#[_,]»,

  -- the `{ tacticSeq }` syntax pretty prints without a space on the left and with a space on the
  -- right.
  ``Parser.Tactic.tacticSeqBracketed,

  -- in `conv` mode, the focusing dot (`·`) is *not* followed by a space
  ``Parser.Tactic.Conv.«conv·._»,

  -- The pretty printer does not place spaces around the braces`{}`.
  ``Parser.Term.structInstField,

  -- `throwError "Sorry"` does not pretty-print the space before the opening `"`.
  ``termThrowError__,

  -- Ignore term-mode `have`, since it does not print a space between `have` and the identifier,
  -- if there is a parenthesis in-between.
  ``Parser.Term.have,
  -- For a similar reason, we also ignore tactic `replace`.
  ``Parser.Tactic.replace,

  -- If two `induction ... with` arms are "merged", then the pretty-printer
  -- does not put a space before the `|`s
  ``Parser.Tactic.inductionAlt,
  ]

/--
Given an array `a` of `SyntaxNodeKind`s, we accumulate the ranges of the syntax nodes of the
input syntax whose kind is in `a`.

The linter uses this information to avoid emitting a warning for nodes with kind contained in
`unlintedNodes`.
-/
def getUnlintedRanges (a : Array SyntaxNodeKind) :
    Std.HashSet Lean.Syntax.Range → Syntax → Std.HashSet Lean.Syntax.Range
  | curr, s@(.node _ kind args) =>
    let new := args.foldl (init := curr) (·.union <| getUnlintedRanges a curr ·)
    if a.contains kind then
      --dbg_trace "adding {s} at {s.getRange?.getD default}"
      new.insert (s.getRange?.getD default)
    else
      new
  -- We special case `where` statements, since they may be followed by an indented doc-string.
  | curr, .atom info "where" =>
    if let some trail := info.getRangeWithTrailing? then
      curr.insert trail
    else
      curr
  | curr, _ => curr

/-- Given a `HashSet` of `Lean.Syntax.Range`s `rgs` and a further `Lean.Syntax.Range` `rg`,
`isOutside rgs rg` returns `false` if and only if `rgs` contains a range that completely contains
`rg`.

The linter uses this to figure out which nodes should be ignored.
-/
def isOutside (rgs : Std.HashSet Lean.Syntax.Range) (rg : Lean.Syntax.Range) : Bool :=
  rgs.all fun {start := a, stop := b} ↦ !(a ≤ rg.start && rg.stop ≤ b)

def mkWindowSubstring (orig : Substring.Raw) (start : String.Pos.Raw) (ctx : Nat) : String :=
  let head : Substring.Raw := {orig with stopPos := start} -- `orig`, up to the beginning of the discrepancy
  let middle : Substring.Raw := {orig with startPos := start}
  let headCtx := head.takeRightWhile (!·.isWhitespace)
  let tail := middle.drop ctx |>.takeWhile (!·.isWhitespace)
  s!"{headCtx}{middle.take ctx}{tail}"

/--
We think of `orig` as `orig = ...<wordLeft><whitespaceLeft>|<whitespaceRight><wordRight>...`
where
* `<wordLeft>`  and `<wordLeft>` are maximal consecutive sequences of non-whitespace characters,
* `<whitespaceLeft>` and `<whitespaceRight>` are maximal consecutive sequences of whitespace
  characters,
* the `|` denotes the input position `start`.

We carve out the substring `<wordLeft><whitespaceLeft><whitespaceRight><wordRight>`.
-/
def mkWindowSubstring' (orig : Substring.Raw) (start : String.Pos.Raw) : String :=
  -- Starting from the first discrepancy, we move to the right, consuming all subsequent
  -- contiguous whitespace and then all subsequent contiguous non-whitespace.
  let fromError : Substring.Raw := {orig with startPos := start}
  let extRight := fromError.dropWhile (·.isWhitespace) |>.dropWhile (!·.isWhitespace)
  -- Ending at the first discrepancy, we move to the left, consuming all previous
  -- contiguous whitespace and then all previous contiguous non-whitespace.
  let toError : Substring.Raw := {orig with stopPos := start}
  let extLeft := toError.dropRightWhile (·.isWhitespace) |>.dropRightWhile (!·.isWhitespace)
  -- Carve the substring using the starting and ending positions determined above.
  {orig with startPos := extLeft.stopPos, stopPos := extRight.startPos}.toString

def mkExpectedWindow (orig : Substring.Raw) (start : String.Pos.Raw) : String :=
  -- Ending at the first discrepancy, we move to the left, consuming all previous
  -- contiguous whitespace and then all previous contiguous non-whitespace.
  let toError : Substring.Raw := {orig with stopPos := start}
  let extLeft := toError.dropRightWhile (·.isWhitespace) |>.dropRightWhile (!·.isWhitespace)

  -- Starting from the first discrepancy, we move to the right, consuming all subsequent
  -- contiguous whitespace and then all subsequent contiguous non-whitespace.
  let fromError : Substring.Raw := {orig with startPos := start}
  let first := fromError.take 1
  let afterWhitespace := fromError.dropWhile (·.isWhitespace) |>.takeWhile (!·.isWhitespace)
  --dbg_trace "first: '{first}'"
  --dbg_trace "afterWhitespace: '{afterWhitespace}'"
  if first.trim.isEmpty then
    -- Case 1: `first` consists of whitespace, so we discard all consecutive whitespace and
    -- keep the following non-whitespace block.
    {orig with startPos := extLeft.stopPos, stopPos := start}.toString ++ afterWhitespace.toString
  else
    -- Case 2: `first` is not whitespace, so we simply add a space and then the
    -- following non-whitespace block.
    {orig with startPos := extLeft.stopPos, stopPos := start}.toString ++ " " ++
      {afterWhitespace with startPos := start}.toString

#guard mkExpectedWindow "0123 abcdef    \n ghi".toRawSubstring ⟨8⟩ == "abc def"

#guard mkExpectedWindow "0123 abc    \n def ghi".toRawSubstring ⟨9⟩ == "abc def"

def _root_.Mathlib.Linter.mex.mkWindow (orig : Substring.Raw) (m : mex) (ctx : Nat := 4) : String :=
  let lth := ({orig with startPos := m.rg.start, stopPos := m.rg.stop}).toString.length
  mkWindowSubstring orig m.rg.start (ctx + lth)

/-- `mkWindow orig start ctx` extracts from `orig` a string that starts at the first
non-whitespace character before `start`, then expands to cover `ctx` more characters
and continues still until the first non-whitespace character.

In essence, it extracts the substring of `orig` that begins at `start`, continues for `ctx`
characters plus expands left and right until it encounters the first whitespace character,
to avoid cutting into "words".

*Note*. `start` is the number of characters *from the right* where our focus is!
-/
public def mkWindow (orig : String) (start ctx : Nat) : String :=
  let head := orig.dropEnd (start + 1) -- `orig`, up to one character before the discrepancy
  let middle := orig.takeEnd (start + 1)
  let headCtx := head.takeEndWhile (!·.isWhitespace)
  let tail := middle.drop ctx |>.takeWhile (!·.isWhitespace)
  s!"{headCtx}{middle.take ctx}{tail}"

def _root_.Mathlib.Linter1.mex.toLinterWarning (m : mex) (orig : Substring.Raw) : MessageData :=
  let origWindow := mkWindowSubstring' orig m.rg.start
  let expectedWindow := mkExpectedWindow orig m.rg.start
  m!"{m.error} in the source\n\n\
  This part of the code\n  '{origWindow.trimAscii}'\n\
  should be written as\n  '{expectedWindow}'\n"

/-- If `s` is a `Substring` and `p` is a `String.Pos`, then `s.break p` is the pair consisting of
the `Substring` `s` ending at `p` and of the `Substring` `s` starting from `p`. -/
def _root_.Substring.Raw.break (s : Substring.Raw) (p : String.Pos.Raw) : Substring.Raw × Substring.Raw :=
  ({s with stopPos := p}, {s with startPos := p})

/--
Assume that `ms` is a sorted array of `String.Pos` that are within the `startPos` and the `stopPos`
of `orig`.
Successively `break` `orig` at all the positions in `ms`.
For each piece thus created, except for the very first one, check if it starts with whitespace.
Only if it does, wedge a `" ".toSubstring` between this piece and the previous one.
In all cases, drop all leading whitespace from the pieces.

Return the concatenation of the possibly-trimmed-pieces with the appropriate `" ".toSubstring`
separators.

The intuition is that the positions listed in `ms` correspond to places where there is a
discrepancy between an expected boundary between words and the actual string.
The expectation is that up to the current position, everything is well-formatted and, if a space
was available, then it has been used. The convention is that no more than one consecutive space
is used to separate words at the positions in `ms`.

Thus, if a position in `ms` falls where the following character is not a space, then a space should
be added before that word.  Hence, the script adds a `" ".toSubstring`.

If, instead, there is a space after a position in `ms`, then it, and all the following streak of
whitespace, is redundant and gets trimmed.
-/
def mkStrings (orig : Substring.Raw) (ms : Array String.Pos.Raw) : Array Substring.Raw :=
  let (tot, orig) := ms.foldl (init := (#[], orig)) fun (tot, orig) pos =>
    let (start, follow) := orig.break pos
    let newTot := tot.push start ++ if (follow.take 1).trim.isEmpty then #[] else #[" ".toRawSubstring]
    (newTot, follow.trimLeft)
  tot.push orig

section Tests
local instance : Coe String Substring.Raw := ⟨String.toRawSubstring⟩

#guard -- empty positions, store `s` in a singleton array
  let s := "abcdef    ghi jkl"
  let ms : Array String.Pos.Raw := #[]
  #[s.toRawSubstring] == mkStrings s.toRawSubstring ms

#guard
  let s := "12345    ghi jkl"
  let ms : Array String.Pos.Raw := #[⟨5⟩]
  #["12345".toRawSubstring, "ghi jkl".toRawSubstring] == mkStrings s.toRawSubstring ms

#guard
  let s := "12345    ghi    jkl"
  let ms : Array String.Pos.Raw := #[⟨2⟩, ⟨5⟩, ⟨10⟩, ⟨12⟩]
  #["12".toRawSubstring, " ", "345", "g", " ", "hi", "jkl"] == mkStrings s.toRawSubstring ms

#guard
  let s := "12345    ghi    jklmno pqr"
  let ms : Array String.Pos.Raw := #[⟨6⟩, ⟨13⟩, ⟨19⟩]
  #["12345 ".toRawSubstring, "ghi ", "jkl", " ", "mno pqr"] == mkStrings s.toRawSubstring ms

end Tests

@[inherit_doc Mathlib.Linter1.linter.style.commandStart1]
def commandStartLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.style.commandStart1 (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- If the file is mostly a "meta" file, then do not lint.  The heuristic for this is to look
  -- at the name of the module.
  let comps : ExcludedSyntaxNodeKind := .mk (← getMainModule).components.toArray none
  if comps.contains #[`Tactic, `Util, `Lean, `Meta] then
    return
  -- Skip `eoi` and `#exit`.
  if Parser.isTerminalCommand stx then return
  -- Some `SyntaxNodeKind`s are prone to produce incorrect pretty-printed text, so we skip
  -- commands that contain them.
  if stx.find? (unparseable.contains #[·.getKind]) |>.isSome then
    return
  -- If a command does not start on the first column, emit a warning.
  --dbg_trace "lint1"
  let orig := stx.getSubstring?.getD default

  let stxNoSpaces := stx.eraseLeadTrailSpaces
  if let some pretty := ← Mathlib.Linter1.pretty stxNoSpaces then
    let pp := pretty.toRawSubstring
    let (_, corr) ← generateCorrespondence true Std.HashMap.emptyWithCapacity #[] stx pretty.toRawSubstring
    let (reported, excluded) := corr.partition fun _ {kinds := ks,..} => !totalExclusions.contains ks
    let fm ← getFileMap
    --dbg_trace "reported: {reported.toArray.map (fm.toPosition ·.1)}"
    --dbg_trace "excluded: {excluded.toArray.map (fm.toPosition ·.1)}"
    for (origPos, ppR) in reported do
      let ppPos := ppR.pos
      let origAtPos := {orig with startPos := origPos}
      let ppAtPos := {pp with startPos := ppPos}
      if let some (rg, msg, mid) := mkRangeError ppR.kinds origAtPos ppAtPos then
        -- TODO: temporary change, hopefully reduces no-op warning spew
        if mkWdw origAtPos != mkWdw ppAtPos mid then
          -- TODO: temporary change, hopefully reduces no-op warning spew
          if !((mkWdw origAtPos).contains '¬' || (mkWdw origAtPos).contains '-' || (mkWdw origAtPos).startsWith "suffices" || (mkWdw origAtPos).contains '⊢' || (mkWdw origAtPos).contains "π ") then
            Linter.logLint linter.style.commandStart1 (.ofRange rg)
              m!"{msg}\n\n\
              This part of the code\n  '{mkWdw origAtPos}'\n\
              should be written as\n  '{mkWdw ppAtPos mid}'\n"

    for (origPos, ppR) in excluded.filter (fun _ _ => false) do
      let ppPos := ppR.pos
      let origAtPos := {orig with startPos := origPos}
      let ppAtPos := {pp with startPos := ppPos}
      if let some (rg, msg, mid) := mkRangeError ppR.kinds origAtPos ppAtPos then
        if mkWdw origAtPos != mkWdw ppAtPos mid then
          -- TODO: temporary change, hopefully reduces no-op warning spew
          if !((mkWdw origAtPos).contains '¬' || (mkWdw origAtPos).contains '-' || (mkWdw origAtPos).startsWith "suffices" || (mkWdw origAtPos).contains '⊢' || (mkWdw origAtPos).contains "π ") then
            logInfoAt (.ofRange rg)
              m!"{msg}\n\n\
              This part of the code\n  '{mkWdw origAtPos}'\n\
              should be written as\n  '{mkWdw ppAtPos mid}'\n\n{ppR.kinds}\n"

/-
  if let some mexs ← getExceptions stx then
  let (reported, _) := reportedAndUnreportedExceptions mexs
  --let parts := mkStrings orig (reported.map (·.rg.start))
  --dbg_trace "Reformatted:\n{parts.foldl (· ++ ·.toString) ""}\n---"
  let fname ← getFileName
  let fm ← getFileMap
  let mut visitedLines : Std.HashSet Nat := ∅
  for m in reported.qsort (·.rg.start < ·.rg.start) do
    --logInfoAt (.ofRange m.rg) m!"{m.error} ({m.kinds})"
    --dbg_trace "{m.mkWindow orig}"
    Linter.logLint linter.style.commandStart (.ofRange m.rg) <| m.toLinterWarning orig
    -- Try to `sed` away. -- remove the trailing `, _` to get the following to ever be executed.
    if let #[a, _, _] := m.kinds.drop (m.kinds.size - 2) then
      let lineNumber := (fm.toPosition m.rg.start).line
      if visitedLines.contains lineNumber then
        continue
      visitedLines := visitedLines.insert lineNumber
      let lineStart := fm.lineStart lineNumber
      let lineEnd := fm.lineStart (lineNumber + 1)
      let line : Substring := {fm.source.toSubstring with startPos := lineStart, stopPos := lineEnd}.trimRight
      let origWindow := mkWindowSubstring' orig m.rg.start
      let expectedWindow := mkExpectedWindow orig m.rg.start
      let newLine := line.toString.replace origWindow expectedWindow
      if newLine != line.toString then
        logInfoAt (.ofRange m.rg) m!"# {a}\n\
          sed -i '{lineNumber}\{s={line.toString.replace "=" "\\="}={newLine.replace "=" "\\="}=}' {fname}"
-/

/-
  if let some pos := stx.getPos? then
    let colStart := ((← getFileMap).toPosition pos).column
    if colStart ≠ 0 then
      Linter.logLint linter.style.commandStart stx
        m!"'{stx}' starts on column {colStart}, \
          but all commands should start at the beginning of the line."
  -- We skip `macro_rules`, since they cause parsing issues.
  if (stx.find? fun s =>
    #[``Parser.Command.macro_rules, ``Parser.Command.macro, ``Parser.Command.elab].contains
      s.getKind ) |>.isSome then
    return
  let some upTo := CommandStart.endPos stx | return

  let fmt : Option Format := ←
      try
        liftCoreM <| ppCategory' `command stx --PrettyPrinter.ppCategory `command stx
      catch _ =>
        Linter.logLintIf linter.style.commandStart.verbose (stx.getHead?.getD stx)
          m!"The `commandStart` linter had some parsing issues: \
            feel free to silence it and report this error!"
        return none
  if let some fmt := fmt then
    let st := fmt.pretty
    let parts := st.split (·.isWhitespace) |>.filter (!·.isEmpty)
    --for p in parts do dbg_trace "'{p}'"
    let st := " ".intercalate parts
    let origSubstring := stx.getSubstring?.getD default
    let orig := origSubstring.toString
    if (! Parser.isTerminalCommand stx) && st.trim.isEmpty then logInfo m!"Empty on {stx}"
    else
    --dbg_trace "here"
    let slimStx := captureException (← getEnv) Parser.topLevelCommandParserFn st <|>
      .ok (.node default ``Parser.Command.eoi #[])
    --dbg_trace "there"
    if let .ok slimStx := slimStx then
      let diffs := stx.compare slimStx
      if !diffs.isEmpty then
        logInfo m!"{diffs}"
        dbg_trace stx
        dbg_trace slimStx
    else
      logWarning m!"Parsing error!\n{stx.getKind}|||\n---"
      dbg_trace stx
    --let parts := orig.split (·.isWhitespace) |>.filter (!·.isEmpty)
    --if ! ("".intercalate parts).startsWith (st.replace " " "" |>.replace "«" "" |>.replace "»" "") then
    --  logWarning m!"A\n{st.replace " " "" |>.replace "«" "" |>.replace "»" ""}\n---\n{"".intercalate parts}"

    let scan := parallelScan orig st
    let (o, n) := (scan.size, (← finalScan stx false).size)
    if o != n then
      dbg_trace "(old, new): ({o}, {n})"
      dbg_trace scan
      for e in (← finalScan stx false) do
        dbg_trace e
      let ustx := stx.eraseLeadTrailSpaces
      let simplySpaced ← pretty ustx <|> return default
      dbg_trace simplySpaced
    let docStringEnd := stx.find? (·.isOfKind ``Parser.Command.docComment) |>.getD default
    let docStringEnd := docStringEnd.getTailPos? |>.getD default
    let forbidden := getUnlintedRanges unlintedNodes ∅ stx
    --dbg_trace forbidden.fold (init := #[]) fun tot ⟨a, b⟩ => tot.push (a, b)
    for s in scan do
      --logInfo m!"Scanning '{s}'"
      let center := origSubstring.stopPos.unoffsetBy s.srcEndPos
      let rg : Lean.Syntax.Range :=
        ⟨center, center |>.offsetBy s.srcEndPos |>.unoffsetBy s.srcStartPos |>.increaseBy 1⟩
      if s.msg.startsWith "Oh no" then
        Linter.logLintIf linter.style.commandStart.verbose (.ofRange rg)
          m!"This should not have happened: please report this issue!"
        Linter.logLintIf linter.style.commandStart.verbose (.ofRange rg)
          m!"Formatted string:\n{fmt}\nOriginal string:\n{origSubstring}"
        continue
      --logInfo m!"Outside '{s}'? {isOutside forbidden rg}"
      unless isOutside forbidden rg do
        continue
      unless rg.stop ≤ upTo do return
      unless docStringEnd ≤ rg.start do return

      let ctx := 4 -- the number of characters after the mismatch that linter prints
      let srcWindow := mkWindow orig s.srcNat (ctx + s.length)
      let expectedWindow := mkWindow st s.fmtPos (ctx + (1))
      Linter.logLint linter.style.commandStart (.ofRange rg)
        m!"{s.msg} in the source\n\n\
          This part of the code\n  '{srcWindow}'\n\
          should be written as\n  '{expectedWindow}'\n"
      Linter.logLintIf linter.style.commandStart.verbose (.ofRange rg)
        m!"Formatted string:\n{fmt}\nOriginal string:\n{origSubstring}"
-/

initialize addLinter commandStartLinter

open Lean Elab Command Linter in
elab tk:"#mex " cmd:(command)? : command => do
  let opts ← elabSetOption (mkIdent `linter.style.commandStart) (mkAtom "false")
  withScope ({ · with opts }) do
    let tktxt := "#mex"
    if let some cmd := cmd then if let some cmdSubstring := cmd.raw.getSubstring? then
    if let .error .. :=
      captureException (← getEnv) Parser.topLevelCommandParserFn cmd.raw.getSubstring?.get!.toString
    then
      logWarningAt tk m!"{tktxt}: Parsing failed"
      return
    elabCommand cmd
    --dbg_trace "here: {cmd}"
    if (← get).messages.hasErrors then
      logWarningAt tk m!"{tktxt}: Command has errors"
      return
    match ← getExceptions (verbose? := true) cmd with
    | none => logWarning m!"{tktxt}: Processing error"
    | some mexs =>
      if mexs.isEmpty then
        logInfo "No whitespace issues found!"
        return
      let (reported, unreported) := reportedAndUnreportedExceptions mexs
      logInfo m!"{mexs.size} whitespace issue{if mexs.size == 1 then "" else "s"} found: \
          {reported.size} reported and {unreported.size} unreported."
      -- If the linter is active, then we do not need to emit the messages again.
      if !Linter.getLinterValue linter.style.commandStart1 (← getLinterOptions) then
        for m in reported do
          logWarningAt (.ofRange m.rg) <|
            m!"reported: {m.toLinterWarning cmdSubstring}\n\n\
              {m.kinds.map MessageData.ofConstName}"
      for m in unreported do
        logInfoAt (.ofRange m.rg)
          m!"unreported: {m.toLinterWarning cmdSubstring}\n\n\
            {m.kinds.map MessageData.ofConstName}"

end Style.CommandStart

end Mathlib.Linter1
