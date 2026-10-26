# Helical quotient and extension: independent review

Date: 2026-10-26. Reviewer: `controller_certificate`. Result: **PASS**, with no
requested source changes.

`complemented47_review` authored all four reviewed files and the imported
literal-table permutation proof. I read every line of the four frozen files,
both author receipts, the complete `WangTiles942Periodic` and
`WangTiles942Permutation` sources, and the actual `Allowed`/`allowed_iff_tile`
binding used here. I independently checked the signed-coordinate arguments
and freshly replayed all four files in an isolated object overlay. I authored
other native arithmetic, marked-window, and row-step modules in this project;
none of those modules is a premise or import of these two geometry packets.
This is an independent review of the new geometry, not a claim of independent
authorship or a fresh rebuild of the entire dependency closure.

## Exact frozen scope

The source paths below are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| File | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `WangTiles942HelicalQuotient.lean` | 147 | 6496 | `dd7e2a20254aba54f57d03cc6690a6c18d3d45d83fe3c44383f53be4c3162481` |
| `WangTiles942HelicalQuotientChecks.lean` | 91 | 3924 | `5be0501091408ae5bee59a2b863e81edc93ed3552d209d02701a2434348b8034` |
| `WangTiles942HelicalExtension.lean` | 187 | 7865 | `1ca88d926e0002f2ee0eb7974176ebbe0f400c473e3b7ab742a44421b834bdc6` |
| `WangTiles942HelicalExtensionChecks.lean` | 92 | 4065 | `4be293fb69c978e38d562934ef42370eb34b92e7899b8b00a9d0757c3abe7cda` |

Quotient directly imports `WangTiles942Periodic`
(`b426e06571ddc25095a0573784d2f289f116cb976468f826da128a4bb9713d53`)
and `WangTiles942Permutation`
(`3351336105f22baf653dcefb3bd83273924dd539353eebf5f1232da855045cef`).
Extension imports Quotient alone. The check files import their respective
main modules. Existing prerequisite objects were reused, with the recorded
source and object hashes unchanged throughout this review.

## Mathematical review

The quotient uses the exact existing address `-x-w*t`. Integer induction in
both directions proves `T x t = T (x+w*t) 0` from the period `(w,-1)`.
Combining this with vertical period `H` gives the row-zero period `w*H`.
The integer-remainder lemma is valid for negative addresses, and passing to
`ZMod (w*H)` requires the explicit nonzero-modulus instance. The final
positive-dimension wrapper derives that instance from `w>0` and `H>0`.

The selected quotient indices belong to the actual 942-tile table by
`allowed_iff_tile`; they are not an unrelated alphabet. Full pointwise tile
binding is proved before matching. Actual table injectivity then recovers
index zero from the Start tile at the origin. Spatial and temporal matching
use, respectively, addresses `j-1` and `j-w`, with the correct east/west and
south/north orientation. Neither a quotient factorization nor a unique Start
is supplied as a premise. The construction does not require coprime dimensions
or least periods.

The extension is exactly

```text
rep = (x+L) % w - L
q   = (x+L) / w
extend C w L x t = C rep (t+q).
```

Positive width guarantees `rep` lies in the half-open band `[-L,w-L)` for
every signed integer `x`. On that band, `q=0` and the original tile is retained
at the same time. Before the right boundary, moving one spatial site increments
the representative and leaves the quotient unchanged. At the boundary it
returns to `-L` and increments the quotient. Consequently the required seam
condition is precisely
`west (C (-L) (t+1)) = east (C (w-L-1) t)`; the proof uses it at `t+q`.
This also explains why the resulting helical period is `(w,-1)`. No truncated
natural subtraction or truncation-to-zero division is used.

Allowedness, time matching, and vertical periodicity are assumed only on the
canonical band and then transferred to all integer coordinates. The origin
binding uses both `0 <= L` and `L < w`. The extension theorem permits `H=0`
because merely preserving a period does not need positive height; composition
to a nonempty finite marked word explicitly adds `H>0`. The focused final
composition preserves every original band tile pointwise.

The checks cover arbitrary signed time, negative representatives, the wrong
temporal-address sign, noncoprime dimensions, modulus one, width one, both
band endpoints, the wrong seam-time sign, and the failure of origin binding
if `L<w` is dropped. The constant plain plane is used only to check quotient
binding, never to claim the Start condition. At width one the horizontal proof
correctly uses only the twisted seam condition.

These are geometric implications from explicit band/plane hypotheses. They
do not assert that a computation supplies such a band, prove cofinal widths
or heights, construct a polynomial witness, or prove a converse to the current
polynomial soundness theorem or the full `Con(ZFC)` equivalence.

## Independent fresh replay

The toolchain was `leanprover/lean4:v4.32.0`. I excluded all four target stems
from the prerequisite overlay at
`/tmp/wang-helical-geometry-controller-peer/DiophantineConsistency`, and then
compiled in this order: Quotient, its checks, Extension, its checks. Each
fresh target object is a regular file, not a symlink. Thus the checks imported
their freshly replayed main modules, and Extension imported the freshly
replayed Quotient. The shared prerequisite and target objects were untouched.

Each command used the following form, substituting the reviewed source stem:

```sh
lake env bash -c 'export LEAN_PATH="/tmp/wang-helical-geometry-controller-peer:$LEAN_PATH"; exec lean -M6000 -j1 SOURCE -o OVERLAY_OBJECT'
```

Both sources and both check files set `Elab.async false`. All four commands
exited zero. Both main modules produced no Lean diagnostics. The check logs
contain eleven and fourteen axiom reports, respectively, using only subsets
of `propext`, `Classical.choice`, and `Quot.sound`. The reviewed sources contain
no `sorry`, `admit`, `native_decide`, or new axiom.

| Replay | Seconds | Peak KiB | Fresh object SHA-256 |
| --- | ---: | ---: | --- |
| Quotient | 3.71 | 3201084 | `3d810df6b42c331248ada16ce3da6574dd2f2ea5a8e1818b0404dabb6d390e32` |
| Quotient checks | 3.35 | 3188952 | `f6a021298ea181874a1ff3b3dd98f00b5c0d046300b537cc87afc47a7719162e` |
| Extension | 4.60 | 3211856 | `be3dd6d5596b6561ec58894788108868f7d7a9092cd9d37f8bf30f3bb3f4ecef` |
| Extension checks | 3.60 | 3185772 | `b00f12525be3f1ad2c4537fce1e7fabb4644c9712a3f90a4235c451dc82a99a3` |

All four fresh objects are byte-identical to the corresponding pre-existing
objects. The 21 recorded source/object/configuration inputs remained unchanged.
`/tmp/wang-helical-geometry-controller-peer/inputs-before.json` has SHA-256
`0bd6bad37a9b94746d9fa7994dde6ee52db307ad682ac17dc4f1c91f3b887455`;
the post-replay report `replay.json` has SHA-256
`414b20609357168501158ee67329671b330b688e18e46e528f2706b5ecb93871`.

The following log paths are relative to that temporary directory. They include
the separate `/usr/bin/time` summary as well as any Lean output.

| Log | SHA-256 |
| --- | --- |
| `quotient-main.log` | `21c3ad809ebbd0c113feda6f1e323e0d7e4ebcb2912855fe03e866f34795c0a1` |
| `quotient-checks.log` | `dfd3d99e0511c5c4b5d1dd46288a45ec6d54a2d0c24402fcc9f87daefb21847c` |
| `extension-main.log` | `fb9ee636c4027b04e84b8d8789a011f3abc3d56f633f712bc42059f0d2b1289f` |
| `extension-checks.log` | `546ff6e09bd5e4fa8aba82e96d26d9107228f06bd116bc67c6f7840a1128cb79` |

Only this peer receipt was added to the repository. No source, frozen
prerequisite, shared document, or git state was changed by this review.
