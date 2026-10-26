# Additional arithmetic simplification

## Retain: direct exponent-divisibility obstruction

Pinned source: `89226e3921bce3e8949fadd12d3efb6914c7630c`,
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeBinaryScale.lean`,
`width_dvd_exponent`, source lines 61-72.

The current proof first obtains `2^(u%d)-1=0`, then reconstructs
`2^(u%d)=1`, then rewrites `1` as `2^0` and invokes injectivity of exponentiation.
The proposed proof uses the same trusted Mathlib remainder identity but takes
its order consequence directly. If `u%d` were positive, `2^(u%d) <= 1`
would imply `2 <= 1` by `Nat.pow_le_one_iff`. Thus the remainder is zero.

This removes the intermediate power equality and exponent-injectivity bridge.
The exact public signature, including its currently unused `hd : 0 < d`, is
preserved. No auxiliary theorem is introduced into the production patch.

Measured declaration change: 12 physical/nonblank lines to 8; proof body
10 to 6; 502 to 319 UTF-8 bytes. The containing module loses four lines.
These are proposed-source measurements relative to the pinned commit, not a
claim about a fully integrated hypothetical tree or build speed.

Both complete original and replacement declarations compiled independently
under Lean 4.32.0 with narrow imports. Both have exactly
`[propext, Classical.choice, Quot.sound]`. Both produce the same pre-existing
unused-variable warning for `hd`. There is no `sorry`, added axiom, or native
evaluation. The full modified project module and its clients were not built.
The production source was not modified.

Files: `width-divisibility.patch`, `WidthDivisibilityBefore.lean`,
`WidthDivisibilityAfter.lean`, corresponding logs,
`arithmetic-width-divisibility-metrics.json`, and `arithmetic-width-divisibility-validation.json`.

## Optional extension: recover the block radix directly

`PrimeRadix.lean` proves the following separate API candidate without importing
any project theorem. For prime p and natural d,q,R,

    1 < q,  q | p^R,  (p^d - 1) | (q - 1)
       => exists N > 0, d*N <= R and q = (p^d)^N.

There is also the affine adapter `q = 1 + J*(p^d - 1)`, matching `sourceQ`.
The proof extracts `q=p^u` once, applies the exponent-divisibility lemma once,
and substitutes `u=d*N`. This gives the positive cell count and its exponent
budget together.

Target: `source_q_power_radix`, with `source_X_eq_two_pow_rank` and
`source_X_eq_q_mul` supplying the prime-power divisor premise and the existing
`sourceQ_cast`/beta binding supplying the affine premise. Retain the public
`source_q_power_two` theorem as a compatibility result where required.

This extension is optional. It simplifies the arithmetic interface at clients,
but adding a reusable helper for only one current source need not reduce the
total line count. Do not add its helper-inclusive size to the four-line patch
saving, and do not claim the production adapter is compiled. Standalone kernel
compilation succeeded; `arithmetic-validation.json` and `PrimeRadix.log` record the result.
The kernel needs no separate d>0 assumption: at d=0 the other assumptions
already contradict 1<q. At q=1 a positive N need not exist, which is why q>1
is explicit. Primality is not dispensable: for p=6,d=2,q=4096,R=12 the two
divisibilities hold but q is not a power of 36.

## Novelty boundary

The independent audit screened a-w and all five incoming ZIPs
(28 packets through closing snapshot `7df43cdfacb490cd3ca3acd23e39027efebf8801`) and found no
prime-power/Mersenne exponent classification proposal. Earlier coherent source
and window packaging assumes recovered powers; this proposal shortens the
arithmetic reason why the recovered exponent is a multiple of the block width.
Its local patch is deliberately scoped to that exact proof obligation.

Rejected as already covered: aligned-cell subgroups, cyclic convolution as
monoid-algebra evaluation, rotations from point masses, finite-fibre support
pushforward, twisted helical coordinates/periods, generic geometric-sum
replacement in PolynomialRangeBounds, selector color-moment mass sums, and
fixed-six Pell comparison. Finite signed-borrow closed forms are explicitly
covered by the signed-prefix quotient/remainder proposal in the fifth incoming
ZIP; they are excluded as a direct overlap.
