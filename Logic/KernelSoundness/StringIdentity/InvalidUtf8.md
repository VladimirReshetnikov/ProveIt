# Lean's source reader is many-to-one, and silent about it

Byte-exact reproductions in [`invalid-utf8/`](invalid-utf8/). Those files cannot
be edited in a text editor — the whole point is that they contain byte sequences
which are *not* valid UTF-8, and an editor would silently repair them. Use
`invalid-utf8/regenerate.py` to rebuild them.

## The finding

**Lean's lexer does not validate UTF-8.** Any invalid byte sequence in a `.lean`
file is silently replaced with U+FFFD REPLACEMENT CHARACTER at read time — no
error, no warning, exit code 0. Because many distinct invalid sequences map to
the *same* replacement, the map from source bytes to declared meaning is **not
injective**.

`invalid-utf8/collide.lean` — five byte-distinct declarations:

| spelling of the middle byte(s) | |
| --- | --- |
| `ED A0 80` | lone **high** surrogate U+D800, WTF-8 encoded |
| `ED B0 80` | lone **low** surrogate U+DC00 |
| `FF` | not a legal UTF-8 lead byte at all |
| `C0 80` | overlong encoding of U+0000 |
| `EF BF BD` | **a genuine U+FFFD — perfectly valid UTF-8** |

```
collide.lean:4:4: error: `«X<U+FFFD>Y»` has already been declared
collide.lean:6:4: error: `«X<U+FFFD>Y»` has already been declared
collide.lean:8:4: error: `«X<U+FFFD>Y»` has already been declared
collide.lean:10:4: error: `«X<U+FFFD>Y»` has already been declared
```

All five declare **one** constant. The fifth line is the sharp one: a file
containing a *legitimate* replacement character is indistinguishable, to Lean,
from four different flavours of corruption.

`invalid-utf8/probe.lean` confirms the mechanism: a string literal built from the
lone surrogate reports `utf8ByteSize = 3`, `length = 1`, and
`toList.map Char.toNat = [65533]`. The bytes on disk were `ED A0 80`; the string
in the environment is `EF BF BD`.

## It silently changes what a theorem says

`invalid-utf8/silent.lean`, which compiles with **exit 0 and no output at all**:

```lean
theorem claim  : "a<ED A0 80>b".length = 3 := rfl   -- corrupted bytes
theorem claim2 : "a<EF BF BD>b".length = 3 := rfl   -- genuine U+FFFD
example : ("a<ED A0 80>b" = "a<EF BF BD>b") := rfl  -- accepted
```

The last line is proved by `rfl`: after reading, the two literals are the same
string. So a `.lean` file whose string literals were mangled in transit — by a
lossy UTF-16→UTF-8 transcode, a truncated multi-byte sequence, a byte-level
corruption — still compiles, still proves theorems, and says something different
from what its author wrote, with no diagnostic.

This is [Jon Skeet's "When is a string not a
string?"](https://codeblog.jonskeet.uk/2014/11/07/when-is-a-string-not-a-string/)
in Lean: a source file containing a lone surrogate is mangled by the compiler's
UTF-8 round trip, and the string constant you get out is not the one you put in.

## Why it is *not* a soundness hole

The substitution happens at the **file-reading** boundary, before anything else
sees the bytes. So:

* Lean's internal invariants stay honest. Every `Char` really does satisfy
  `isValidChar`, and every `String`'s `isValidUTF8` proof is true — U+FFFD is
  ordinary valid UTF-8.
* There is no kernel/compiler divergence, because the malformed bytes never
  reach either. Both see `EF BF BD`.

Contrast this with the alternative design, which *would* have been a soundness
hole: had the reader passed `ED A0 80` through, the kernel's
`string_lit_to_constructor` would `utf8_decode` it to `0xD800` and apply
`Char.ofNat`, which rejects surrogates and yields the default `'A'`, while the
compiled `String.data` would hand back the raw code unit — a `rfl`-vs-`native_decide`
divergence. Sanitising at the boundary is the right call.

## Why it matters anyway

It is an **integrity** boundary, not a soundness one. Wherever a workflow needs
"the file I reviewed is the file that was checked", the reviewed bytes and the
compiled meaning can differ:

* Byte-level corruption of a `.lean` file is **not detected**. It compiles.
* Two files that differ on disk — and therefore to `git`, to a diff, to a hash,
  to a reviewer — can be identical to Lean.
* `comparator`'s `Challenge.lean` is *trusted and human-read*; that is exactly a
  setting where silent lossy rewriting of the trusted artifact is undesirable.

A warning on invalid UTF-8 would close the gap without changing any semantics.

## A related positive result

[Skeet's second article](https://codeblog.jonskeet.uk/2014/12/01/when-is-an-identifier-not-an-identifier-attack-of-the-mongolian-vowel-separator/)
is about U+180E MONGOLIAN VOWEL SEPARATOR, which was reclassified `Zs` → `Cf`
between Unicode 6.2 and 6.3, so different .NET versions disagreed about whether
it was a legal identifier character.

Lean is structurally immune to that failure mode: `isLetterLike` and `isIdRest`
(`Init/Meta/Defs.lean:101-134`) are **hardcoded numeric range tables**. Lean
never consults a Unicode character database, so its identifier syntax cannot
drift as Unicode versions change. The sweep found U+180E among the 43 characters
Lean rejects bare, and re-running under 4.33.0-rc1 gave identical results.
