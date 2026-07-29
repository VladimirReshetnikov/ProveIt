# Does Lean disagree with itself about string identity?

A recurring source of subtle bugs is that "string equality" means different
things in different components: byte-wise in one encoding, up to Unicode
normalisation, culture-sensitive, case-insensitive, or with ad-hoc rules
(ignoring `Cf` characters, C-string truncation at NUL). Wherever two components
of one system disagree about when two strings are the same, something can be
smuggled past the one that is doing the checking.

`Name` is the identity of every constant in Lean, and `Name`s are built from
`String`s, so this class of bug would be soundness-relevant here. This directory
records the investigation.

**Result: no soundness loophole, and no checker break.** Lean is byte-exact and
*uniform* internally, and every decision path in `leanprover/comparator` carries
names as structural `Lean.Name` — no normalisation, case folding, collation or
dot-splitting anywhere. Every disagreement found fails **closed**.

One finding is nevertheless a genuine machine-level defect rather than a hazard
for human readers: **`Name.toString` is not injective, and it is reachable from
ordinary Lean source.** See [`NameToString.md`](NameToString.md).

The headline lexical result is a *negative* one, and it is the reassuring answer
to the question that motivated this study: **no character that Lean accepts in a
bare identifier is one that collation-, NFKC- or `Cf`-stripping comparison would
treat as equal to its absence** — 0 of the 43 invisible/ignorable characters
tested. Every such character requires French quotes `«…»`, which are
conspicuous in source.

## Confirmed disagreements (Lean vs. its environment)

### 1. Lean identifiers vs. Unicode canonical equivalence

`NormalizationForms.lean`. Lean's `isIdRest` (`Init/Meta/Defs.lean:133`) admits
Latin-1 Supplement and Latin Extended-A, so precomposed `é` (U+00E9) is a legal
identifier character — but U+0301 COMBINING ACUTE ACCENT is in no admitted
range. Consequently, for the two canonically-equivalent spellings of `café`:

| spelling | result |
| --- | --- |
| `def café` (NFC, U+00E9) | accepted |
| `def café` (NFD, `e`+U+0301) | **`error: expected token`** |
| `def «café»` (NFD, French-quoted) | **accepted — a second, distinct constant** |
| `def «café»` (NFC, French-quoted) | `error: 'café' has already been declared` |

So `café` and `«café»` are two distinct Lean constants whose names Unicode
declares to be *the same string*. Lean itself never confuses them
(`NameIdentity.lean` confirms the environment keeps both and finds each under
its own name, and `Name.toString` escapes the NFD form as `«café»`). Any
component in the pipeline that normalises — a filesystem, an editor, a diff or
review tool, a search index, a normalising text pipeline — would.

### 2. Collation-ignorable characters: ARABIC TATWEEL

`TatweelIdentifiers.lean`. U+0640 ARABIC TATWEEL (category `Lm`) is the standard
example of a character that culture-sensitive comparison gives **zero weight**:
under .NET's default `StringComparison.CurrentCulture`, and under the DUCET
default collation, `"foo"` and `"fooـ"` compare **equal**. The same holds
for `Cf` characters such as U+00AD SOFT HYPHEN and the zero-width joiners --
and C# goes further and strips `Cf` characters from identifiers outright.

U+0640 is in none of `isLetterLike`'s ranges, so:

| spelling | result |
| --- | --- |
| `def fooـ` (bare suffix) | **`error: expected token`** |
| `def ـfoo` (bare prefix) | **`error: expected token`** |
| `def «fooـ»` | **accepted -- distinct from `foo`** |
| `def «ـfoo»` | **accepted -- distinct from `foo`** |

Lean's own comparisons are all ordinal and agree that these are distinct:
`"foo" == "fooـ"` is `false`, `compare` gives `.lt`, the `Name`s differ,
the hashes differ, and `Name.toString` escapes them to `«fooـ»` /
`«ـfoo»`, which round-trip. So Lean is immune; anything downstream that
compares identifiers by collation rather than ordinally is not.

The useful fact is the *bare* rejection: an invisible or zero-weight character
cannot be smuggled into an ordinary-looking identifier. Getting one in requires
French quotes, which are conspicuous in source.

### 3. `Name.toString` is documented as not round-tripping

`NameRoundTrip.lean`. Over 18 adversarial components, three fail
`toName ∘ toString = id`:

```
component "a»b"  printed as "a»b"  parsed back as Lean.Name.anonymous
component "»"    printed as "»"    parsed back as Lean.Name.anonymous
component "«x»"  printed as "«x»"  parsed back as `x
```

The last is the sharp one: `Name.mkSimple "«x»"` and `Name.mkSimple "x"` are
distinct constants, but the printed form of the first *parses to the second*.
So `toName ∘ toString` is not injective, while ordinal comparison of the printed
forms keeps them apart -- two different notions of name identity.

This is **documented**, not a new bug. `Init/Meta/Defs.lean:235`:

> Names with number components, anonymous names, and names containing `»` might
> not round trip.

(Number components actually do round-trip -- `foo.5` vs `foo.«5»` -- so the
doc is pessimistic there.)

It matters because names really do cross a text boundary: comparator's
`Main.lean:safeExport` serialises the constants to export with `.toString` and
passes them as **argv** to `lean4export`, which parses them back. Those names
are verifier-controlled (theorem names, permitted axioms, the primitive list),
so a solver cannot reach it -- but a challenge whose theorem name contained `»`
would silently cause the wrong constant to be exported.

### 4. Module names vs. the filesystem

`ModuleNameVsFilesystem.md`. Lean's module identity is byte-exact; NTFS and
APFS/HFS+ are case-insensitive, and HFS+ normalises to NFD. On Windows,
`import FOO` silently loads `Foo`. Lean *does* catch the collision when both
spellings appear in one file, but a lone mis-cased import resolves to a module
other than the one written.

## Systematic lexer sweep

79 candidate characters x 4 probes each, one probe per file (316 `lean`
invocations, since Lean's error recovery mis-attributes columns when probes are
batched). Behaviour is entirely **position-independent**, and there were **zero**
"has already been declared" collisions across all 158 baseline/variant pairs:

| | bare (first/middle/last) | inside `«…»` | collides with plain spelling |
| --- | --- | --- | --- |
| 43 characters | `error: expected token` | accepted | never |
| 36 characters | accepted | accepted | never |

**Rejected bare (43).** All 23 `Cf` tested (SOFT HYPHEN, ZWSP, ZWNJ, ZWJ, WORD
JOINER, BOM, ARABIC LETTER MARK, LRM/RLM, all bidi overrides and isolates,
INVISIBLE TIMES/SEPARATOR/PLUS), 7 `Mn` (CGJ, variation selectors, combining
acute/dot/ring), 3 Hangul fillers, 4 `Zs` (NBSP, FIGURE SPACE, MMSP, IDEOGRAPHIC
SPACE), U+2065, the DŽ digraphs, MIDDLE DOT, HYPHENATION POINT, and **U+0640
ARABIC TATWEEL**.

**Accepted bare (36).** Exactly `isIdFirst`/`isIdRest` and nothing else:
Letterlike U+2100-214F (including U+212A KELVIN, U+2126 OHM, U+212B ANGSTROM,
and the `So` symbols No and TM), Math Alphanumerics, Latin-1 Supplement, Latin
Extended-A, Greek. `Lean.Parser.Basic:563 whitespace` skips only
`' ' | '	' | '' | '
'`; there is no normalising or stripping pre-pass.

Re-run under Lean 4.33.0-rc1 (comparator's pinned toolchain) for 15
representative characters: identical results.

### The "equal to another character" half does bite — for auditors only

Exhaustive scan over all **981 bare-legal codepoints**: exactly 7 have
`NFC(c) != c` with a bare-legal NFC image — U+212A/`K`, U+2126/`Ω`, U+212B/`Å`,
U+1F79/`ό`, U+1F7B/`ύ`, U+1F7D/`ώ`, U+1FBE/`ι`. Both spellings are legal bare,
both declare fine, and the pretty-printer emits the raw character unescaped, so
the two `#check` lines are byte-identical on screen. Beyond that, **82 NFKC
classes** (404 codepoints) and **254 case-folding classes** (520 codepoints)
contain more than one bare-legal member: `Foo𝔄`/`Foo𝒜`/`Foo𝔸`/`FooA` are four
distinct constants that UAX-31 NFKC identifier folding collapses into one, and
`h₁` vs `h1` likewise.

Measured on .NET 10.0.9 / ICU:

| pair | Ordinal | OrdinalIgnoreCase | InvariantCollate | +IgnoreCase |
| --- | --- | --- | --- | --- |
| `ς` vs `σ` | False | **True** | False | True |
| U+212A vs `K`, U+2126 vs `Ω`, U+212B vs `Å` | False | False | **True** | True |
| U+1FBE vs `ι` | False | **True** | **True** | True |
| Math alphanumerics, `ℕ`/`N`, `No`, `TM`, `₁`/`1` | False | False | False | **True** |
| `ſ`/`s`, `ß`/`ss`, `ı`/`I` | False | False | False | False |

Note the first row: `OrdinalIgnoreCase` — the comparison people reach for
*because* they believe it is the culture-free safe one — conflates `ς` and `σ`,
both of which are legal bare Lean identifier characters.

## Negative results

* **Embedded NUL does not split the kernel from the compiler.**
  `EmbeddedNulDiff.lean` — `'\0'` is a valid Unicode scalar, so Lean strings may
  contain it, while the runtime stores strings NUL-terminated
  (`lean_string_cstr`). 32 differential checks (`String.decEq`, `==`, ordering,
  `length`, `utf8ByteSize`, `toList`, `isPrefixOf`, `posOf`, `get`, `take`,
  `drop`, `append`, `push`, `hash`) comparing `Lean.Kernel.whnf` against the
  compiler via `Meta.evalExpr`: **0 mismatches**. Lean's runtime is length-based
  throughout, not C-string-based.
* **Invalid UTF-8 is not constructible.** In Lean 4.32 `String` is
  `structure String where ofByteArray :: (toByteArray : ByteArray)
  (isValidUTF8 : ByteArray.IsValidUTF8 toByteArray)`. The proof field closes off
  overlong encodings and lone surrogates in any *proof*, even though the runtime
  constructor is `lean_string_from_utf8_unchecked`.
* **`Name` hashing is consistent across construction routes.**
  `NameIdentity.lean` — `Name.str p s`, `Name.mkStr p s`, `String.toName` and
  `Name.mkSimple` all yield the same cached hash and `Name.quickCmp = .eq`. A
  desynchronised cached hash would have let two constants share a name in the
  environment's hash-indexed map; it does not happen.
* **Numeric name components round-trip faithfully.** `Name.mkNum foo 5` prints
  as `foo.5` while `Name.mkStr foo "5"` prints as `foo.«5»`; both survive
  `toString ∘ toName`, and they stay distinct. (This is the hazard comparator's
  `numeric_namespace` regression test covers.)
* **The export payload is clean** — and this is why nothing escalates to
  soundness. It is the one boundary a solution author controls, and it carries
  names structurally as `{"str":{"pre":idx,"str":s}}`. A fuzz over all 1,112,064
  code points found 0 JSON round-trip mismatches and 0 distinct characters
  rendering to identical JSON text.
* **The `«…»` wrapper itself is robust.** `Name.mkStr .anonymous ("q"++c++"z")`
  for all 1,112,064 code points, checking `n.toString.toName == n`: **2
  failures**, U+00BB `»` and U+271D `✝`. NUL, newline, tab, quotes, backticks,
  all CJK and all astral planes round trip exactly. Every other round-trip
  failure lives in the code paths that *suppress* the wrapper.
* **The filesystem does not conflate homoglyphs.** 13 pairs (U+212A/K, U+2126/Ω,
  U+212B/Å, `ſ`/`S`, `ſ`/`s`, `ς`/`σ`, `ı`/`I`, `İ`/`I`, Math-A/`A`, `ℕ`/`N`,
  `ß`/`ss`, NFC/NFD `Å` and `é`) each produced **2 distinct files** on NTFS. Only
  ASCII `A`/`a` collapsed, so the `import FOO` case-insensitivity does not extend
  to any homoglyph.
* **A UTF-8 BOM is not silently stripped** — `expected token` at 1:0, and a
  UTF-16LE file is rejected outright. No editor-writes-BOM / Lean-ignores-BOM
  divergence.
* **The NFD direction is closed.** 395 of the 981 bare-legal codepoints have a
  multi-codepoint NFD, but every such decomposition ends in a combining mark and
  all `Mn` are rejected bare. Bare `é` can only collide with `«e◌́»`, never with
  another bare spelling.
* **No Cyrillic.** `isLetterLike` admits Greek, Coptic, Greek Extended,
  Letterlike Symbols, Mathematical Alphanumerics, Latin-1 Supplement and Latin
  Extended-A — but *not* Cyrillic, which rules out the most familiar homoglyph
  attacks (`с`, `а`, `е`, `о`). Perfect confusables do remain inside the
  admitted set, notably U+212A KELVIN SIGN ≡ `K` and U+2126 OHM SIGN ≡ `Ω`, and
  the Mathematical Alphanumerics NFKC-collapse to ASCII (`ℊ`→`g`, `ℓ`→`l`,
  `ſ`→`s`, `ℯ`→`e`).

## Running them

```bash
lean StringIdentity/EmbeddedNulDiff.lean      # differential fuzz, expect 0 mismatches
lean StringIdentity/NameIdentity.lean         # Name identity and hashing
lean StringIdentity/NormalizationForms.lean   # expect exactly 2 errors, at the NFD-bare and NFC-quoted lines
lean StringIdentity/TatweelIdentifiers.lean   # expect exactly 2 errors, at the two BARE tatweel lines
lean StringIdentity/NameRoundTrip.lean        # expect 3 round-trip failures, all involving »
lean StringIdentity/NameToStringCollision.lean # two distinct constants, one printed form
```
