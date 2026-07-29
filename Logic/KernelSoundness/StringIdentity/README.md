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

**Result: no soundness loophole.** Lean is byte-exact and *uniform* everywhere I
could probe. The genuine disagreements are all at the boundary between Lean and
the outside world (the filesystem, and Unicode's own notion of equivalence), and
they are auditing hazards rather than kernel unsoundness.

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

### 2. Module names vs. the filesystem

`ModuleNameVsFilesystem.md`. Lean's module identity is byte-exact; NTFS and
APFS/HFS+ are case-insensitive, and HFS+ normalises to NFD. On Windows,
`import FOO` silently loads `Foo`. Lean *does* catch the collision when both
spellings appear in one file, but a lone mis-cased import resolves to a module
other than the one written.

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
```
