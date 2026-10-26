# Canonical Carrier66 to the literal 31-coordinate source

Date: 2026-10-25. Author: controller_certificate. This is an ordinary algebraic
audit of the complete proposed forward map, not a new Lean theorem. No existing
Lean source was changed or incoming code executed for this audit. The machine215
dependency build proceeds separately.

The inspected source bindings are:

| File under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| Carrier65.lean | be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154 |
| Carrier66.lean | 22ab116b489cacf7652dc490448e26e4aa1bc7735e35284c33449b0bf27a92eb |
| SplitCertificate59.lean | 0b6082b0af3f092f6914263eb1568da1d3730df24032b6c1dff5489875da0a03 |
| ShortCircuit.lean | b66cf8e69b669c6d4efec6213fc1a1808a9ecd10db33032c7a601288568680c9 |
| NativePellBootstrap.lean | 89b10d72a75e7b95dfb587312cb0d89e38bc9874524dc4536bb4e44bd3946e60 |
| NativeSourceMask.lean | c92d1ee93dff4e8655005bf73d2cedb6ae95a55819c0a14de76202cd0b2a913e |
| NativeSourceWindow.lean | ed24370b1588e660829c26eefc0439a2ac8a53c7cdba73937c4175244418b09f |

## Exact map

Keep the four ports `beta,K,MC,MF_source` unchanged, with the fourth port already
shifted. Let `b = Carrier66.core p v`, using its displayed fields, and write
`R=b.rank`, `delta=b.delta`, `d0=c*T-R`. Set

`e = f^2 - delta*i^2*c^4 - 1`.

The proposed integer source assignment, in all 31 positions, is:

| Index | Value | Index | Value |
|---:|---|---:|---|
| 0 | J | 16 | q^3 |
| 1 | F | 17 | E |
| 2 | alpha | 18 | ell+k |
| 3 | z | 19 | c |
| 4 | f | 20 | a |
| 5 | h | 21 | X |
| 6 | i*delta | 22 | D |
| 7 | f*d0 | 23 | c^2 |
| 8 | T + delta*i^2*c^3*d0 - 1 | 24 | q^2-1 |
| 9 | s | 25 | f^2 |
| 10 | w | 26 | V=f^2*d0-c |
| 11 | tau | 27 | y^2-V^2 |
| 12 | eta | 28 | S=i*delta*c^2 |
| 13 | zeta | 29 | S^2 |
| 14 | y | 30 | delta |
| 15 | gamma | | |

In particular, the old source coordinate 8 is not `f*T`. The latter substitution
relates the intermediate ShortCircuit parameter to the current auxiliary
formula, but does not give the final 31-coordinate source assignment. The exact
identity needed in source rows 12 and 13 is

`c*x8 - V - R = -e*d0`.

It follows immediately by expanding `d0=c*T-R`. Thus canonical strong norm
`e=0` gives the source rank `nativeRank = c*x8-V = R`.

## Every source row

After substituting the assignment above, the 22 literal
`SplitCertificate59.sourceRows` have these values. These identities hold over
any commutative ring, before imposing the canonical norm values:

| Row | Substituted value |
|---:|---|
| 0 | 0 |
| 1 | 0 |
| 2 | 0 |
| 3 | 0 |
| 4 | 0 |
| 5 | 0 |
| 6 | 0 |
| 7 | P-1 |
| 8 | 0 |
| 9 | 0 |
| 10 | 0 |
| 11 | Q-1 |
| 12 | index-1+e*d0 |
| 13 | -e*d0 |
| 14 | W-1 |
| 15 | 0 |
| 16 | 0 |
| 17 | 0 |
| 18 | 0 |
| 19 | 0 |
| 20 | -delta*e |
| 21 | U-1 |

Rows 0 and 1 use `q=beta*J+1`; row 4 uses `E=X*Y` and `a=E+Y`;
rows 5 and 6 use `k=eta+zeta`, `c=k*Y+eta`, and `ell=E*k*Y`.
The first Pell residual in row 7 uses `x18=ell+k`, not `ell`.
Row 13 is exactly the source rank minus the displayed rank target, after
rows 0 and 1 are identically zero. Row 14 retains the old positive `z`
coordinate: it equals the current `W-1`, without a coordinate shift.
Rows 18--20 require the new source slot `x6=i*delta`; using `i` alone would
give the wrong strong coefficient.

For integer canonical parents, `Z=delta` and `delta>0` imply `e=0` because
`Z-delta=delta*e`. Therefore all 22 source rows vanish using exactly the six
canonical factor values already present in `Carrier66.Canonical`.

## Positivity, including the three nontrivial slots

Assume `beta>0`, every parent coordinate positive, and `Canonical p v`.
Then `q>=2`, `Y=s*q^3>=8`, `E>0`, `k>=2`, and `c=k*Y+eta>2*k`.
The canonical index gives `R=k-h*E-1<k`, hence `2*R<c`.
Consequently `d0=c*T-R>c/2>0`. All of these facts precede the use of source
positivity; there is no circular appeal to `NativePellBootstrap`.

The strong norm gives `f^2=1+delta*i^2*c^4>1`, so positive integer `f>=2`.
Thus `V=f^2*d0-c>c>1`. Slot 8 is positive directly from
`T>=1` and `delta*i^2*c^3*d0>0`. Slot 7 is positive because `f,d0>0`.
For slot 27, put `g=y^2-V^2`. The canonical auxiliary equation implies

`(S^2-1)*g = V^2-1`.

Here `S=i*delta*c^2>1` and `V>1`, so `g>0`. No sign of `g` is assumed.
Every other source slot is a positive original coordinate or a positive
displayed block. Casting each integer slot to `Nat` therefore preserves both
its value and its strict positivity and gives the required natural source
assignment.

## Reusable arithmetic window and remaining proof boundary

`NativeSourceWindow.source_native_window` is generic in
`NativeSourceMask.Interface ports d MC MF`. That interface has only these exact
coefficient obligations: `d>=4`, `beta=2^d-1`, `K>=0`, the two port equalities
`ports2=MC`, `ports3=MF+beta`, both masks below beta, `MC mod 2=0`,
`MF mod 8=4`, and `popcount(MC)+popcount(MF)=d`. It contains no machine or
tableau calibration assumption. Its existing proof can be reused unchanged.

For the current 2011 page, the ordinary finite packet gives `d=47*2011=94517`,
978 clear bits in MC and 978 set bits in native MF. The latter consists of one
origin test, 916 padding tests, 43 clause bits, 17 copy bits, and one marker bit.
The merged low recipe `8*G917-4` has low residue 4 modulo 8. These observations
identify the coefficient lemmas to formalize; this audit does not claim those
huge finite definitions or population proofs already exist in Lean.

After the explicit map and finite interface are Lean-proved, the existing
window theorem yields `q=(2^d)^N`, actual repunit J, the positive gap C, the two
native mask tests, rank population `3*d*N+2`, the precise spatial power, and
the unchanged old-z transport equation. The coordinate map preserves J,F,
alpha,z,w and gives `nativeRank=R`, so those conclusions refer to the actual
current front. A subsequent current-2011 tableau/computation decoder remains
necessary. This forward algebraic map neither proves the converse source
construction nor assumes a native calibration theorem to conceal that work.

Implementation proposal: a new `Carrier66Source.lean`, importing `Carrier66`
and `NativeSourceWindow`, with the 31-coordinate map, all-row identity,
derived positivity, natural cast, and a generic window corollary. No existing
source module needs alteration. Ownership should be assigned before work.

## Implementation addendum

The root agent subsequently assigned that implementation. It is complete in
the two new modules below; existing Lean source files were not modified.

| New module | Lines | SHA-256 |
|---|---:|---|
| Carrier66Source.lean | 418 | c4c9db61501f2130998be82af68fa200d848a9bd1175f15a2ac4431eb4879388 |
| Carrier66SourceChecks.lean | 60 | f350fb6b76eef0d9d2d7b387866972d1829fbe6b808528acfa04a418c9f62623 |

Both files were fully reread after the final changes and freshly compiled with
`lake env lean -j1 -o ...` on Lean 4.32.0. The main module's diagnostic log is
empty. The checks log SHA-256 is
`a9b80d9e01723dec03dcd227be1c0aef2a42c4baf665e89ea5600b1dec4ff843`;
every printed axiom report contains only `propext`, `Classical.choice`, and
`Quot.sound`.

`row_formula` proves the entire residual table over every commutative ring.
`canonical_rows`, `source_pos`, and `sourceNat_rows` derive all required
source equations and positivity. `nativeRank_eq`, `sourceQ_eq`, and `gap_eq`
bind the old source abbreviations to the current parent exactly.
`canonical_window` states every native arithmetic-window conclusion in the
current parent's coordinates under the explicit finite `Interface` alone.
`positive_carrier_zero_source` additionally composes the proved Carrier65
restoration, starting from an actual positive Carrier65 zero and its scalar
port bounds. No new native or refutation calibration premise is introduced.

The focused checks fix all 31 slots and include a positive but noncanonical
input with source coordinates `x6=675`, `x8=26530200`, and `V=-9`. This both
distinguishes the map from the incorrect `x8=f*T` substitution and shows why
the canonical norm hypotheses are required for positivity.

Dependency reuse was scoped explicitly: the entire 50-custom-module closure
of `NativeSourceWindow` had exact source-byte equality with the 62ff checkout,
as did the toolchain and lake manifest. Only its 21 missing object bundles were
copied, including available private/server companions. The receipt is
`/tmp/diophantine-nativewindow-identical-cache-receipt.json`, SHA-256
`997158e16f55039b6838f006d4a7422f702df0e73bea400dca73c5580fd5b0ea`.
The two new modules were freshly compiled; no claim of a fresh rebuild of all
their inherited dependencies is made. Development fixes were limited to
restricting arithmetic tactic inputs, the natural-cast API form, and finite
coordinate reduction. No theorem statement was weakened to bypass a failed
proof. Independent peer review is separate from this author receipt.
