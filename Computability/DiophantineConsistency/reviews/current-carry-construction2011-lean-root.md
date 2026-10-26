# Constructing actual cyclic normalization: author receipt

Date: 2026-10-26. ROOT authored this composition and read both complete
final sources. This is an author self-review. The separate independent
composition review is `current-carry-construction2011-lean-peer.md`.

## Frozen files

Paths below are relative to `Lean/DiophantineConsistency/`.

| Source | Lines | SHA-256 |
| --- | ---: | --- |
| `CurrentCarryConstruction2011.lean` | 108 | `6efd60cd1ce0f40aa48e68ec7d9c2b2c680bbdc0aa289488c268e79fa68a026a` |
| `CurrentCarryConstruction2011Checks.lean` | 52 | `7f737892951219779768fc8c013353ed9de8688de427fe2d699443ede8fd6408` |

The direct dependency hashes are:

| Module | SHA-256 |
| --- | --- |
| `CurrentKernel2011` | `6f8642d8d3715335dcf61fb0060818226f227db24e126d4c14d58831e76d3a55` |
| `NativeBooleanRotation` | `d50110d8f2a959df7da69f23e80b4df09a1aad98ba2b66c67d2445203cf81f3e` |
| `CurrentWordConstruction2011` | `9455d6c2015906a8f76ff2be5275a95cae5340f0ca3e8dc16666ffc6bab2b5b8` |

The generic carry fixed point, decomposition, cyclic predecessor word,
binary rotation and maximum-word proofs were read in their actual source
contexts. Existing checked dependency objects were reused. ROOT also read
the entire new word-construction module, checks and author receipt.

## Construction and limits

For every Boolean digit function and every natural binary displacement W,
the raw field is the actual folded K convolution plus the actual binary
rotation. The literal mass budget closes the carry bound57, and the
existing simultaneous fixed point constructs carries with predecessor
i−1. Their remainders give bounded digits, exact local decomposition and
the congruence `(K+2^W)*word(c) ≡ word(digits)` modulo `radix^n−1`.

No positive strict F, mask test, source-system zero or desired native
equivalence is supplied. The word may initially equal the modulus.
One positive digit proves positivity; one nonmaximum digit, together
with the proved digit bounds, gives strictness below the modulus.
The assembled specialization uses independent Boolean dummy/marker maps.
Start at the origin proves positivity of the source C, not of transport F.

The checks include fractional phase46, n=1, unrestricted displacement,
the zero source, separate slack/positive digits, the assembled word and
marked-source positivity. All mask/copy constraints, stronger bounds,
controller arithmetic and positive polynomial witnesses remain open.

## Fresh bounded replay

Both complete final files were read and compiled sequentially using
`lake env lean -M6000 -j1`, their declared `Elab.async false`, and the
pinned Lean4.32.0 toolchain. The main wrote its named shared `.olean`;
the checks imported that fresh main and wrote their own named object.
Both final terminal results were exit0. The main log is empty; all five
intended axiom reports use only `propext`, `Classical.choice`, `Quot.sound`.
No new axiom, `sorry`, `admit` or `native_decide` was introduced.

| Evidence | SHA-256 |
| --- | --- |
| `/tmp/current-carry-construction2011-root-main.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/current-carry-construction2011-root-checks.log` | `48ca621ecf6b6ea36b68633fa94b249eb8af0d028f2d96c989449496d65c15e8` |
| Main `.olean` | `623ee728704fd3702a97b2c2fea4633fc4d46faaf62071128299199ed8c23f2f` |
| Checks `.olean` | `1f7d634a2e415bf1c6b07cf49b40421702e98204f8a01f379bbabc815861ed98` |

Development failures were an unnormalized radix alias in a word-add
rewrite and an underconstrained finite-sum summand. Explicit types and
the actual word sum fixed them without changing mathematical premises.
The final axiom command was qualified to distinguish this construction
from the older strict-F normalization theorem in the kernel module.
The independent peer then rebuilt both targets in isolation and obtained
byte-identical objects. No full closure or umbrella rebuild is claimed.

The maintained equation TeX/PDF were also read and checked against their
manifest: all715 decimal digits agree in TeX and actual PDF text, all14
unknowns are distinct and unsubscripted, and both artifact hashes remain
unchanged. The active goal and open internal-ZFC obligation are preserved.
