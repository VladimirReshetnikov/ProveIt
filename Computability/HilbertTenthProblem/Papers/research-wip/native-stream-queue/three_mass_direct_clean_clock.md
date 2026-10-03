# Direct unbounded clean clocks for four complete three-mass sources

The four emitted integer polynomials use **597/472/470/473 operations**, with
**59/57/57/57 positive witnesses** and **19 comparisons**. Their two free natural
coordinates are the raw input `x` and requested first clean-target time `U`.
The native clean clock is imposed directly on the packed clock word. There is
no separate forward-time witness or extra clean-time comparison.

These are complete sources for the same four fixed nonuniversal machines used
in Report 21, placed under `22-clean-clocks-`. They save six operations and one
positive witness from that report's folded native sources. The improvement is
a new composition using the current target-free-height source, not a correction
to the report's historical counts. It gives no numerical universal bound,
ordinary-input loader, or improvement to the universal 74/85/86 sources.

## 1. Frozen dependencies and actual source change

The immediate parent is `three_mass_target_free_height`:

- Python: `7df5a60888976b55599014406c9b325a86428da6603f527b8a6fb35cff783d49`
- Receipt: `a263e7423cdc57b8fceb66ef9021be843c8a9c69a7f897ee4d3e38eac2488830`
- Proof: `61c207bf1d50729667fe2ea9dd94c49f66e2d4a848a0d6d12968e9dfd9f01e7a`

The helper authenticates these bytes, their twelve pinned ancestral
source/receipt/proof files, the immediate independent source review, and the
placed clean-wrapper theorem, Report 21 theorem and folded addendum. Report 20's
proof is pinned only for intake provenance; its finite-event arithmetic is not
a mathematical dependency of this new construction. All complete parent rows
are read from JSON as data. No historical Python is imported or executed.

The four literal programs are `s INC2 a; a DEC2 h`, `s ZERO3 h`, `s NOP h`,
and `s POSITIVE3 h`. Entry has no incoming instruction, the distinct halt has
no outgoing instruction, and all instruction groups are separated singletons.
The raw input mass is `N0=x+1`; it encodes counters by its 2- and 3-adic
valuations. The fixed state modulus is `K=5`, residue modulus `m=30`, initial
code 1, and halt code 3 for inc/dec or 2 for the other programs. Rejecting,
halt and unused-state continuations go to an absorbing trap preserving payload.

Write `F` for the positive final raw payload and `Ctau` for the already-paid
packed sum of physical source-step durations. Starting from each actual parent:

1. Rename its natural `T` port to the new natural `U`. There are exactly two
   consumers: the height definition and the final clock right-hand side.
2. Rename its natural `y` port to the positive existential `clean_final_payload`.
   This is `F`. Its encoded endpoint and all consumers remain paid.
3. Change the single radix literal from 131072 to 262144, justified below.
4. Compute the following five new gates and use their result as the left
   operand of the existing last comparison:

   ```
   sum = x + F
   payload_ticks = 192 * sum
   doubled = 2 * Ctau
   partial = doubled + payload_ticks
   Dclean = partial + 208
   ```

Every other certificate gate and the first eighteen comparison pairs are
literal copies after the stated renaming. All sixteen native comparisons,
the global bound and chronological transport remain. The last comparison is

\[
 D_{clean}=(B-1)(\widehat\kappa-1)+U,
 \qquad D_{clean}=2C_\tau+192(x+F)+208.              \tag{1}
\]

The full nineteen-row SOS is emitted and counted. No opcode, scalar
multiplication, endpoint extraction, or finalizer operation is free.

## 2. Pretyping with the external clean time

The computed height and radix are

\[
 h=n_0+U+\eta,\quad n_0=5x+1,\quad
 B=C h^2,\quad C=262144,\quad \eta>0.             \tag{2}
\]

Thus `h>=2`, `0<n0<h` and `0<=U<h` before any equation or native theorem is used.
The new final payload is positive by its supplied domain. The proof below
would also recover its positivity by chronological cancellation, so this
domain strengthening excludes no genuine history.

The multiplier is chosen by an explicit fixed recipe:

\[
 C=2^{\lceil\log_2 \max\{C_{parent},4768m+2310\}\rceil}.
                                                               \tag{3}
\]

Here `Cparent=131072`, `m=30`, giving `C=262144`. This is a literal numeral
recipe, not an exponentiation gate or a claim of the least sufficient radix.
It remains dyadic and satisfies every old fixed lower bound, including the
bounds on map slopes/intercepts, `C>=m+1` and `C>=4`.

To recall the exact pretyping chain, unhat the positive selectors and quotient
coordinates. Let their sum be `J`, their quotient word be `W`, and selected
quotient words be `Za`. The retained equation is

\[
 J+\widehat W+\sum_a\widehat Z_a+\beta=P,
 \qquad P=(B-1)J+1.
\]

If `J=0`, the right side is 1 but the quotient hat and positive global slack
already sum to at least 2. Hence `J>=1`, `P>=B`, and all old nonnegative lane
bounds follow. In particular `(h-1)J<P`, every selector is at most `J`, and the
joined padded native input ports satisfy precisely the old positive
prescribed-scale hypotheses. This argument uses neither an exact forward time
nor the new clock equation. The actual native theorem then gives the AND,
dyadic `B,P`, and hence dyadic `h`. Since `B-1` divides `P-1`, one obtains
`P=B^t`, `J=1+B+...+B^(t-1)` with `t>=1`.

The unchanged selector/range/class lanes type all digits with quotient
`0<=q_i<h`. For current and next encoded states, the bounds are
`1<=c_i<=mh` and `1<=n_i<B`. The actual transport row

\[
 B\sum_{i<t} n_iB^i+n_0
   =\sum_{i<t}c_iB^i+B^t n_f
\]

forces `c0=n0`, `n_i=c_(i+1)`, and `n_f=n_(t-1)>0` by successive reduction
modulo `B` and division by `B`. No assumed bound on `nf` is needed. This
constructs a genuine chronological source run before using the clock row.
Rejecting totalization and terminal halt make it a first halt. A deterministic
current encoded state cannot repeat on such a run, so `1<=t<=mh`.

## 3. Clean-time no-wrap proof

Let `theta` denote the **semantic** forward physical time of this decoded run.
It is not a supplied coordinate. A source step `N -> N'` takes

\[
 108N+96N'+8\quad(\mathrm{INC}),\qquad
 96N+108N'+8\quad(\mathrm{DEC}),\qquad
 192N+8\quad(\mathrm{test/NOP}).
\]

The clean wrapper has a forward copy, a reverse copy with inverse operations,
and NOP bridges at halt and at the fresh entry. Each reversed step has exactly
the same duration as its forward mate. The first whole-configuration target
therefore occurs at

\[
 L=2\theta+192(F+N_0)+16
   =2\theta+192(F+x)+208.                            \tag{4}
\]

The wrapper restores the entire raw integer, including factors coprime to 6.
Fresh entry prevents an early reverse exit; a disabled guard never reaches the
backward copy. Equality concerns the exact finite configuration at its original
absolute coordinates, not only a control observation. The two bridges and
these facts are inherited from the pinned clean-wrapper theorem.

The encoded-current bound gives `N_i<=6h`. Every enabled prime multiplication
is at most threefold, so the final payload obeys `F<=18h`. Also `N0<=6h`.
These deliberately loose estimates cover all allowed source instructions, not
only the one/two-step fixtures. Each tick is at most `396N_i+8<=2384h`, hence

\[
 \theta\le2384m h^2,
 \qquad L\le4768m h^2+4608h+16.                     \tag{5}
\]

For every integer `h>=2`, the exact identity

\[
 2308h^2-4608h-16=(h-2)(2308h+8)\ge0
\]

gives `L< B-1`, because (3) makes

\[
 L\le(4768m+2308)h^2,
 \qquad B-1-L\ge2h^2-1\ge7.                       \tag{6}
\]

The typed packed word satisfies `Ctau congruent theta (mod B-1)`.
Equation (1) therefore yields `U congruent L (mod B-1)`. Independently
`0<=U<h<B-1`. Together with (6), this forces **U=L**. In particular `U=0`
is rejected on every nonempty accepted run. A fabricated clean clock shifted
by `B-1` cannot satisfy the independent height range.

This proves soundness directly. It never obtains a positive parent tuple by
setting the parent's forward-time port to `U`; such a parent would generally
have the wrong clock. Neither an old parent zero nor a bound on a supplied
forward-time witness is used in the proof.

## 4. Completeness and fiber scope

Given a genuine first halt, form `F,theta` and the actual clean time `U` by (4).
Choose any sufficiently large dyadic height satisfying `h>n0+U` and all current
quotient bounds. Set `eta=h-n0-U>0`, use (3), and pack the same chronological
source trace in radix `B`. The old selector, class, range and transport rows
then hold. The global slack has the unchanged positive lower bound

\[
 \beta\ge(B-2h)J-g>0,
\]

where `g<=m-1` is the number of exceptional slope classes. Every padded lane
and prescribed native scale remains valid. The inherited prescribed-AND
theorem supplies fresh positive native witnesses at this new scale.

If the actual source ticks are `tau_i>0`, then

\[
 C_\tau-\theta=\sum_{i<t}\tau_i(B^i-1)
\]

is a nonnegative multiple of `B-1`. Set

\[
 \widehat\kappa=1+\frac{2(C_\tau-\theta)}{B-1}>0.   \tag{7}
\]

This satisfies (1) exactly. No divisibility or exponentiation in this
existence proof is being offered as an uncharged circuit gate; these are
values of the already supplied native/packed witnesses. No enormous complete
native Pell tuple has been materialized.

Consequently, for the four fixed sources, positive witnesses exist exactly at
the first exact native clean-target pairs `(x,U)`. Every accepted nonempty
fiber is infinite: arbitrarily large dyadic heights give distinct retained
`height_slack` values, with fresh native extensions. There is no positive
zero-tuple bijection with the immediate parent or Report 21. The old native
time and old radix need not agree with the new ones. Zero-step and phase-four
sources are not emitted here; the separate affine zero-step circuits in the
report remain applicable on their own scope.

## 5. Whole source algebra, ledgers and exact degrees

For the limited algebra comparison only, define `P_adj` by taking the actual
parent source, renaming `T=U,y=F`, and replacing its radix literal as in (3).
Keep its original last comparison `Ctau=rhs`. The emitted source satisfies the
all-value polynomial identity

\[
 Q=P_{adj}-(C_\tau-rhs)^2+(D_{clean}-rhs)^2.         \tag{8}
\]

This is a complete SOS correction, verified from the literal eighteen retained
rows, exact affine bridge expansion, and full finalizers. `P_adj` is not being
claimed equal to the frozen parent polynomial, or sound for the same clock.
No off-zero polynomial equality between the old and new clean sources is
asserted. Their equivalence is the existential first-target theorem proved
above.

| Fixed source | M | A | Complete total | Positive witnesses | Comparisons | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
| inc2;dec2 | 237 | 360 | 597 | 59 | 19 | 2344 |
| zero3 | 182 | 290 | 472 | 57 | 19 | 1192 |
| nop | 180 | 290 | 470 | 57 | 19 | 1192 |
| positive3 | 187 | 286 | 473 | 57 | 19 | 1192 |

The nineteen-comparison finalizer is still 56 gates: 19 subtractions,
19 squares and 18 accumulator additions. Relative to the target-free-height
parent, the only added gates are the five bridge gates, `2M+3A`. Moving `y`
from a free natural port to a positive witness costs one supplied coordinate.
All gates and every coordinate are output-live. The four full arrays contain
2,012 paid gates.

Report 21's folded native totals are 603/478/476/479, with 60/58/58/58 positive
witnesses and twenty comparisons. A straightforward composition of its
five-gate bridge with the current target-free parent would instead cost
600/475/473/476 and retain a separate positive `theta` and a twentieth row.
The present direct congruence removes that extra row and `theta`, saving a
further `1M+2A` and one witness. These are complete-source comparisons under
the literal integer constant model, not global optimality statements.

Formal total-degree propagation on each actual new gate list gives
2344/1192/1192/1192. To certify matching lower bounds, substitute coordinate
`i` in the emitted ordered `parameters+auxiliaries` list by `(i+2)z` and
propagate the coefficient at each formal upper bound modulo 1,000,003. Bounds
are never lowered when an intermediate coefficient vanishes. Output
coefficients are **667404/476833/476833/476833**, all nonzero. Thus the reported
degrees are exact integer-polynomial degrees; no inference from an observed
fixture zero or a degree upper bound alone is used. The trace digests and
all full sources are in the receipt.

## 6. Bounded reproducibility and exclusions

The helper reads pinned data only and provides a bounded CLI, not a maintained
public compiler API. Its fresh receipt verifies all four complete source
rewrites, closure/liveness, full finalizers and degree certificates. It also
independently checks all 120 literal residue-map and physical-clock rows
against the four instruction tables. The affine dependence on the residue
quotient is checked coefficientwise; each divisibility guard is constant on
its residue class.

Supplementary checks comprise 48 complete signed SOS corrections, including
16 rational assignments, and 84 genuine outer histories at original and
doubled chosen heights. All three actual outer equations and the full joined
bitwise AND hold on those outer fixtures. There are 168 adjacent-time mutation
rejections. The native witness coordinates in those fixtures are placeholders;
no zero of the entire Pell block is claimed numerically. Exact native extension
comes from the inherited theorem.

The `--expect` comparison is recursive and type-exact after a JSON roundtrip.
Optimized Python is rejected because assertions carry the checks. From any
working directory, using the standard library:

```
python /path/three_mass_direct_clean_clock.py --repo ABS_REPO \
  --expect /path/three_mass_direct_clean_clock.json
```

All free coordinates are natural integers and all witnesses are strictly
positive integers. There is no rational/real zero-exactness assertion. The raw
input `x+1` loader still exposes only its prime valuations to control flow;
hiding the requested clock preserves the old coprime-cofactor obstruction.
The theorem is not a fixed universal target, arbitrary later-return relation,
stationary halt, finite-fold representation, or numerical universal-source
compiler. It does not supply the missing paid ordinary-input connection from
Report 16's finite-tape exponential loader.
