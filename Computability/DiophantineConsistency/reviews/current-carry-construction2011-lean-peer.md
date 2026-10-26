# Current carry construction: independent composition review

Date: 2026-10-26. Reviewer: `controller_certificate`. Author of the new
composition: root. Result: **PASS**, no changes requested.

## Frozen sources and review scope

Paths are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| Source | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `CurrentCarryConstruction2011.lean` | 108 | 5374 | `6efd60cd1ce0f40aa48e68ec7d9c2b2c680bbdc0aa289488c268e79fa68a026a` |
| `CurrentCarryConstruction2011Checks.lean` | 52 | 2512 | `7f737892951219779768fc8c013353ed9de8688de427fe2d699443ede8fd6408` |

I read both complete frozen sources before execution. I also read the
invoked fixed-point, digit decomposition, cyclic word congruence, binary
rotation and word-maximum lemmas, and checked the actual kernel's folded
word and mass budget against the new composition. I authored the existing
`CurrentKernel2011` and `CurrentWordConstruction2011` dependencies, as
well as local tile/label construction dependencies. This receipt is an
independent review of root's new composition, not independent authorship
or review of those earlier dependencies.

The main directly imports the actual kernel, the generic Boolean
rotation proof, and the assembled tile-word construction. In particular,
it does not import a native equivalence or assume a source-system zero.

## Proof review

The raw field is exactly the actual folded-kernel convolution plus
`binaryRotation 47 W c`, with unrestricted natural displacement `W`.
Boolean input bounds every temporal digit by `2^46`, including partial
phase46. The actual kernel mass budget then closes the carry box
`0..57`. Applying `NativeCyclicCarry.exists_bounded_carries` constructs
the simultaneous quotient recurrence with the real cyclic predecessor
`i-1`; no initial carry is fixed to zero.

The normalized digits are the remainders of these raw-plus-carry fields.
Their bounds and exact local decomposition follow directly. Their word
is bounded above by the modulus, allowing the exceptional all-maximum
representation at this stage. The transport congruence uses the exact
folded kernel identity and the complete binary-rotation identity, then
cyclic carry telescoping. Its direction and coefficient are exactly

```text
(K + 2^W) * word(radix,c) ≡ word(radix,digits) mod (radix^n - 1).
```

No positive or strict transport representative is supplied to obtain
this result. The `Facts` structure records the construction's proved
outputs, rather than presuming a desired equivalence.

The positivity helper uses one strictly positive weighted digit.
`Facts.word_lt` uses one digit strictly below `radix-1`, while every
other normalized digit may equal `radix-1`; the positive radix power
makes the corresponding summand strictly smaller than the maximum
word. Thus strictness and positivity can be discharged independently.

The assembled specialization derives its Boolean premise from the
independent dummy and marker maps and derives the product modulus's
nonzero instance from `N>0`. Its final positivity theorem concerns
only the assembled source word, using the actual origin Start selector.
It does not mislabel that result as positivity of the normalized
transport word. No unique-Start premise appears.

The checks retain the zero-word case, `n=1`, arbitrary large shifts,
partial phase46, one slack digit, and separate source positivity. They
therefore exercise the distinctions needed for later construction.
Whole high-mask tests, strict transport positivity, stronger upper
bounds, source rows, and controller arithmetic remain unproved here.

## Independent isolated replay

Both targets were rebuilt sequentially under `-M6000 -j1` with the
declared `Elab.async false`, using pinned Lean4.32.0. The overlay
`/tmp/current-carry-construction2011-controller-peer/` excluded both
reviewed target stems; the checks imported the freshly rebuilt main.
Other dependency objects were reused. This is not a full dependency
rebuild, and no shared object was overwritten.

Main: PASS in3.12seconds, peak3268216KiB, no Lean diagnostics.
Checks: PASS in2.71seconds, peak3250004KiB, five standard-only reports.
All printed axioms are among `propext`, `Classical.choice`, `Quot.sound`.
No `sorry`, `admit`, `native_decide`, or added axiom occurs in the new
sources. Both fresh target objects are byte-identical to the originals.
Twenty selected source/object/toolchain/manifest paths remained unchanged.

| Isolated evidence | SHA-256 |
| --- | --- |
| `inputs-before.json` | `ae675ebd0939e5f07e6affb37d4c0a7ce776542f63b150144c8730a0d812165b` |
| `main.log` | `59e59f52da351ba70fdfc0c21372bbcfdf2a4ae381734c0b966e5c4f9ba22c48` |
| `checks.log` | `4550e6b0d9df45f513830c78d97e0399c8a1ffa7cc42105e8072265d5e9a8ee8` |
| Main `.olean` | `623ee728704fd3702a97b2c2fea4633fc4d46faaf62071128299199ed8c23f2f` |
| Checks `.olean` | `1f7d634a2e415bf1c6b07cf49b40421702e98204f8a01f379bbabc815861ed98` |
| `results.json` | `cda9d5deda96d718e453e4f86c978fa2f87a5090d431417bfc99c6c5ccd28af9` |

Only this new peer receipt was added. No reviewed source or shared
document was edited, and no git operation was run.
