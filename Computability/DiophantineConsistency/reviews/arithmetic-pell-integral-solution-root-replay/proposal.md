# Proposed internal large-index forcing and integral Pell solution

Read-only proposal, 2026-10-27. No new Lean source, overlay, compiler, or
prerequisite refresh has been created for this proposal. The frozen
StrongDivisibility source/packet is unchanged and remains explicitly
provisional pending ROOT's independent acceptance supplement.

Proposed pair: `ArithmeticPellIntegralSolution.lean` and focused Checks.
Only imports: `ArithmeticPellCommonUnit` and
`ArithmeticPellStrongDivisibility`. All parameters and indices below are
inside an arbitrary `ORingStructure V` satisfying IΣ1. Write
`X_j(b)=xcoord j b`, `Y_j(b)=ycoord j b`, `A=a+2`, and
`D=delta a=(a+1)*(a+3)=A²−1` (the last equality is expressed additively).

## Precise endpoint and intermediate interface

The actual public endpoint is intended to have the following signature:

```lean
theorem integral_solution (a c p i f : V)
    (hp : 0<p) (hi : 0<i) (hf : 0<f)
    (hcp : c=ycoord p a)
    (hnorm : (i*c*c)*(i*c*c)+delta a=delta a*(f*f))
    (hbig : (a+2)*delta a*delta a<c) :
    ∃ m : V, 0<m ∧ p∣m ∧ f=xcoord m a ∧
      i*c*c=delta a*ycoord m a
```

A second literal-input adapter replaces `hnorm` by
`(i*c*c)*(i*c*c)=delta a*(f*f-1)`. It must derive `1≤f*f` from
`hf` and justify the truncated subtraction before applying the additive
endpoint. No extra base, unit, index, coprimality, parity, or solution
classification premise is supplied.

The coherent intermediate large-index theorem can be stated independently
of the particular common-unit witness:

```lean
theorem large_index_multiple (b n M S T A D c : V)
    (hn : 0<n) (hM : 0<M) (hS : 0<S) (hT : 0<T)
    (hSA : S<A) (hD : D=T*S)
    (hYM : ycoord M b=S*c)
    (hcN : c∣T*ycoord n b)
    (hbig : A*D*D<c) : M∣n
```

These are explicit algebraic coordinates, not an assumed desired index.
The public endpoint derives every premise of this intermediate theorem
from the actual norm via the accepted `common_unit_composition` theorem.
In that application `M=e*p`; thus it genuinely proves `e*p∣n` before
constructing `m`. An enriched helper may retain `n=e*m` for inspection,
but it does not become a public hypothesis.

## Actual growth and divisor argument

1. Derive `Y_j(b)<X_j(b)` for every internal `j`, including zero, from
   the actual norm `X_j²=1+delta b*Y_j²` and `1≤delta b`. A square-order
   comparison suffices; no positive-index premise is needed here.
2. For `g>0`, `time_le_y` gives `0<Y_g`. Actual addition at `(g,g)` then
   gives `Y_(2g)=2*X_g*Y_g`, hence `2*Y_g²<Y_(2g)`. The strict step
   explicitly uses `g>0`; it is not claimed at index zero.
3. For the intermediate theorem, `hbig` gives `c>0`, and `hD` with
   positive `T,S` gives `D>0`. Put `g=gcdValue n M`. The actual
   `gcd_spec` gives `g∣n` and `g∣M`. Since `n>0`, `g=0` would force
   `n=0`; therefore `g>0` and `Y_g>0`.
4. From `Y_M=S*c`, derive `c∣T*Y_M` by the explicit witness `T*S`.
   Apply actual `scaled_common_divisor` to `hcN` and this witness:
   `c∣T*Y_g`. Since `T*Y_g>0`, its quotient witness is positive, so
   `c≤T*Y_g`. This can be proved directly from the witness and the
   discrete `1≤quotient` bound, without importing a new dvd/order API.
5. Assume `M∤n`. Then `g≠M`, since otherwise `g∣n` contradicts that
   assumption. Write `M=g*k` using `g∣M`. The positive `M` excludes
   `k=0`; `g≠M` excludes `k=1`. Discreteness gives `2≤k`, so
   `2*g≤M`. This is a bounded proper-divisor argument in `V`, with no
   ordinary-Nat gcd or standard-index shortcut.
6. Actual `y_strictMono` gives `Y_(2g)≤Y_M=S*c`. Combining with step 2:
   `2*Y_g²<S*c`. Since `S≥1`, `T≤T*S=D`. Thus `c≤D*Y_g`.
7. Square and multiply these nonnegative inequalities:

   `2*c² ≤ 2*(D*Y_g)² = D²*(2*Y_g²) < D²*S*c ≤ D²*A*c`.

   The strict multiplication uses `D>0`. The final weak inequality uses
   `S<A`. Reassociate and cancel the positive `c` in the strict order
   to obtain `2*c<A*D²`. This contradicts `A*D²<c` and `c≤2*c`.
   Therefore `M∣n`.

No finite search, squarefree decomposition, unbounded generic Pell
existence theorem, or new represented recursion is needed in this step.
All growth used is derived from the existing internal norm/addition.

## Binding the actual norm and recovering the original base

With `c=Y_p(a)` and `p>0`, `time_le_y` gives `c>0`; hence
`R=i*c*c>0`. Invoke `common_unit_composition a R f` exactly once.
It derives the same witnesses `b,e,n,S` with

- `e,n,S>0`, `S<A`, `S=Y_e(b)`, `A=X_e(b)`, `f=X_n(b)`;
- `D=delta b*S*S` and `R=delta b*S*Y_n(b)`;
- for every internal query `j`, `X_j(a)=X_(e*j)(b)` and
  `Y_j(a)*S=Y_(e*j)(b)`.

Let `T=delta b*S` and `M=e*p`. Then `T,M>0`, `D=T*S`, and the
query `j=p` gives `Y_M(b)=S*c`. The equality `R=i*c*c` supplies
`c∣T*Y_n(b)` directly, so the intermediate theorem proves `e*p∣n`.

Choose its witness `k` with `n=(e*p)*k` and define `m=p*k`.
Associativity yields `n=e*m`; since `n>0`, `m>0`. The witness `k`
gives `p∣m`. Now use the *same* composition theorem at `j=m`:

- `f=X_n(b)=X_(e*m)(b)=X_m(a)`;
- `R=T*Y_n(b)=T*(Y_m(a)*S)=D*Y_m(a)`.

This restores the integral Pell pair at the original parameter from the
actual relaxed norm. It does not assume `e*p∣n`, `e∣n`, or an integral
Pell pair in order to apply classification or growth.

## Zero cases and explicit exclusions

The public statement retains `p,i,f>0`; it makes no claim when any of
these is zero. `c`, `R`, `e`, `n`, `S`, `T`, `M`, and `g` are proved
positive before the associated cancellations or strict bounds. The
existing strong-divisibility and gcd APIs still include all zero cases;
the new proof derives why its particular application cannot have `g=0`.
There is no division by `Y_0`, no hidden reduction modulo zero, and no
unjustified truncated subtraction. Focused checks should exercise the
additive and literal truncated inputs, the intermediate theorem with
`M=1` (conditional on its full hypotheses), and the exact original-base
output with arbitrary internal parameters.

The final `c∣m` conclusion is deliberately separate. The ordinary guide's
Step 7 needs a cubic ordinate congruence at multiples of `p`, coprime
power cancellation, and reduction by `gcd(c,D)`. Those substantive
internal claims are not provided by the present imports. No full relaxed
auxiliary norm, subsequent target-index identity, equation equivalence,
HA endpoint, or cofinal witness theorem is asserted here.

## Source contracts and provenance

The external guide read in full is
`Computability/HilbertTenthProblem/Lean/Diophantine/Paper1980/PellRelaxedMain.lean`;
its Steps 5–6 motivate the inequality above, but no theorem or object from
that module is imported. Its squarefree and external fundamental-unit
Steps 1–4 are replaced by the accepted internal CommonUnit construction.

The actual imported source pins are:

| Module | Source SHA-256 |
| --- | --- |
| ArithmeticPellCommonUnit | `ec63496db122b74dede3417231e5752dff9ba0ea15e63618738617a87a69b089` |
| ArithmeticPellStrongDivisibility | `a98ec37a7c16151236e8dacdd433c6ecd2e7d870c7a58c4b710267f6c9fd6c92` |
| ArithmeticPellRecurrence | `92acf4d2ce4d63e13cccb1afc5ebe5731e3648957dfd18a5311e537c41597c0e` |
| ArithmeticGcdNormalization | `488783700b1663f66b4caee71e7121eb6c50ab4efe04b39f30d63727cc6c8627` |

CommonUnit is ROOT-accepted at commit `e072abe66c`, with object
`274259f176d6f15ec83e534eff12f28d956d5868d98c5c681611a03a7af231d9`
from `/tmp/arithmetic-pell-common-unit-root-m1m65ryx/lib`. Its accepted
packet/manifest are `c3d7187860435dcbbb97a651aecb47ef0d43ad4e27afcb6f4e308b74479e4fda`
and `f2971527011060ca1ce991b7c1c3319e009aed8b21695a24c74f71ef7a6ddf51`.
StrongDivisibility is still explicitly author-validated/provisional here:
object `51fe8bb3ed563268ec08c8e00a42a46825daac58f58874228713895b71de2385`
from `/tmp/arithmetic-pell-strong-divisibility-author-rkedmwpb/lib`.
Before any future compiler, a separately frozen accepted ROOT supplement
must replace that provisional provider, leaving this inventory unchanged.

The read-only cache auditor merges the prior complete CommonUnit and
StrongDivisibility inventories, authenticates all overlaps by source and
object bytes, retains the accepted Gcd provider from the latter, and adds
only the two named main objects. The result is 101 custom modules
(95 Foundation), 386 custom artifacts, 38 boundary modules with 114 total
boundary artifacts (38 primaries plus 76 companions), and zero refresh.
All 500 first providers are mapped explicitly without creating an overlay.
Implicit Init and all package-boundary names are included. The full JSON
contains every source/header/import/object/provider path and inherited
provenance pin, including Classification and KnownUnit transitively.

Frozen read-only artifacts:

- auditor `arithmetic-pell-integral-solution-cache-audit.py`:
  `5d872a3d1ba50c8a67d8d3c69ba4cc59fb70c93d3a5f62d47cf638d18fa892e6`;
- cache JSON `arithmetic-pell-integral-solution-cache-plan.json`:
  `27b365f34e47feeaaaa6e32c3987ed2cebbb3a6e333673c4d4717b52b3afcee2`;
- mapper `arithmetic-pell-integral-solution-providers.py`:
  `a081ca7c01814e0b53622635dfb12bc9bc408442460278c9847da6190d1896eb`;
- provider JSON `arithmetic-pell-integral-solution-providers.json`:
  `5cc1286a113f8f6af6a2ade661176a708909980cc6968de9ff2a81b8212a70d7`.

The auditor completed 3,007 comparisons over 801 pinned paths; the mapper
verified all 500 provider pairs. Both scripts were fully read before
execution. They only hash/read authenticated inputs and write new plan
artifacts. No Lean source, compiler, overlay, or dependency refresh was
created. Any later authorized pair must retain the same 512MiB reserve,
Lean4.32 `-M6000 -j1 -DElab.async=false`, fresh regular private outputs,
and complete attempt/source/driver/log preservation.
