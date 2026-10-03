# Polynomial bit complexity of accelerated first-revisit detection

Independent mathematical review, 2026-10-03. This is an extension result; the frozen boundary proof and implementation are unchanged.

## Verdict and scope

**The accelerated first-revisit algorithm has polynomial bit complexity in the explicit input length.** It can also produce the exact first-revisit time and witness, or the no-revisit certificate, together with the compressed path in polynomial time and output size.

This claim covers `decide` in the frozen `one_visit.py`. It does **not** claim polynomial complexity for arbitrary observation formulas, their least satisfying times, Presburger quantifier elimination, or any dynamics after the first repeated arrival. An explicitly listed palette is essential to the stated input-size analysis.

Here is a fully explicit numerical bound. Let

- `S = 4uv`;
- `K` be the number of distinct defect positions;
- `R = max {|z_x|, |z_y| : z is the initial position or a defect position}`;
- `B = R + S + 1`;
- `Q = S(2B + 1)`;
- `A = Q + 1`;
- `T = (K + 1)A`.

If the first revisit exists, its time is at most `T`. Every restart time, every finite time returned by **any** pair-intersection call during the algorithm, and every stored lane-base time is at most `T`. All finite stored lane endpoints have index at most `2B`. Every prospective or historical lane base has both coordinates of magnitude at most `B`.

The bounds are deliberately loose. `R`, and therefore the numerical time bound, can be exponential in the binary input length. Its bit length is polynomial; the algorithm never expands a path of that numerical length.

## 1. Pure cycles and bounded bases

Use the frozen proof's before-departure convention. A revisit is equality of lattice positions, without a heading condition. Before the first revisit, the changing-board run agrees with the static-shadow run.

On the defect-free background, the projected transition on `(x mod u, y mod v, heading)` is a permutation. To recover a predecessor from a successor position and heading, subtract that heading's unit vector, read the background turn at the recovered position, and undo it. Consequently every projected orbit is a pure cycle: the reference implementation's generic transient length `mu` is always zero on these inputs.

At restart time `r`, write the prospective excursion as

    p_(r+i+nL) = a_i + n delta,     0 <= i < L, n >= 0,

where `1 <= L <= S`, every component of `delta` has magnitude at most `L`, and `delta` is a background-period vector.

A restart position is either the initial position or one unit step from a defect. Thus its coordinate magnitudes are at most `R+1`. Each `a_i` is reached in fewer than `S` further unit steps, so `|a_i,q| <= R+S <= B`. The extra position used to calculate the displacement also lies in `[-B,B]^2`.

Additionally, within one excursion,

    |a_i,q - a_j,q| <= |i-j| <= L-1.

These facts are independent of the restart's absolute time.

## 2. Completed history remains inside a fixed box

Every completed finite excursion ends at a defect `z`, at time `F`, and has no collision through that time. Consider any nonempty lane retained when that excursion is truncated at `F`. Let its last index be `N` and last point be `e = a_i + N delta`.

By the truncation formula,

    0 <= F - (r+i+NL) <= L-1.

Between this last lane point and the terminal defect the hypothetical excursion makes fewer than `S` unit moves. Therefore each coordinate of `e` has magnitude at most `R+S-1`, hence at most `B`.

Both the first and last point of this lane lie in `[-B,B]^2`. Each coordinate of its intermediate affine points lies between the corresponding endpoint coordinates. Thus **every represented historical point**, even in an extremely long excursion, lies in `[-B,B]^2`. This argument bounds the entire history, not merely its listed bases.

If `delta != 0`, select a coordinate `q` with `delta_q != 0`. Then

    N |delta_q| = |e_q-a_i,q| <= 2B,

and integrality gives `N <= 2B`.

If `delta = 0`, the hypothetical excursion revisits its start after `L` steps. A defect is processed only when its first-arrival time is strictly before the first collision. Hence `F < r+L`. Every lane retained from a completed zero-drift excursion has `N=0`.

These conclusions hold for every completed excursion regardless of which defects remain unseen or of its heading at the terminating defect.

## 3. Every pair-call answer has a small local index

All historical times are strictly less than the current restart `r`. All prospective times are at least `r`. This strict separation makes the chronological inequality automatic for a prospective/history pair after both index-domain conditions are imposed.

### 3.1 Prospective lane versus bounded history

Suppose a prospective lane intersects a historical lane at new index `n` and historical point `y`.

If `delta != 0`, choose `q` with `delta_q != 0`. Both `a_i,q` and `y_q` have magnitude at most `B`, so

    n |delta_q| = |y_q-a_i,q| <= 2B.

Every feasible new index, not just the minimizing one, satisfies `n <= 2B`. The old witness index is at most the historical lane endpoint, also at most `2B`.

If `delta = 0`, the new lane is spatially stationary. If any historical point matches it, the chronological inequality already holds at new index zero. Thus the minimizing new index is `n=0`.

### 3.2 Prospective lane versus a defect

A defect is a singleton at a position with coordinate magnitudes at most `R <= B`, and chronology is omitted. The same argument gives `n <= 2B` for nonzero drift. For zero drift, any hit occurs already at `n=0`.

In particular, a distant, never-encountered defect cannot cause a hidden large intermediate first-hit index: a returned candidate obeys this bound, and an unreachable defect produces no candidate.

### 3.3 Two phases of the prospective excursion, nonzero drift

All phases have the **same** spatial drift `delta` and time period `L`. Equality of phase `i`, index `n`, and phase `j`, index `k`, is

    (n-k) delta = a_j-a_i.

For nonzero drift there is at most one integer `d=n-k` satisfying the vector equation. If it exists, select a nonzero component of the drift to obtain

    |d| <= |a_j,q-a_i,q| <= L-1 <= S-1.

The strict chronological condition is

    i-j+Ld > 0,

which is independent of a common increase in `n` and `k`. If it holds, the minimum feasible new index and its old witness are

    n=max(0,d),    k=max(0,-d).

Both are at most `S-1 <= 2B`. If chronology fails, this ordered pair has no collision candidate.

This includes cross-phase intersections, a position occurring with different headings, and all signs or zero components of the drift. For a same-phase pair with nonzero drift, only `d=0` is possible, and strict chronology correctly rejects it.

### 3.4 Two phases of the prospective excursion, zero drift

If their base positions differ, there is no intersection. If they agree, take old index `k=0`; the minimizing new index is `n=0` when `i>j`, otherwise `n=1`. Hence each pair answer has `n <= 1 <= 2B` and lies before `r+2L`. In particular, the same-phase pair at phase zero guarantees a collision by `r+L`.

No heading comparison enters any case.

### 3.5 Consequence for candidate times

For every finite answer from every prospective/history, prospective/prospective, or prospective/defect pair call,

    new time = r+i+Ln <= r+(S-1)+2BS < r+Q.

This is stronger than a bound only on the winning event. It also controls candidates later discarded because a defect or another collision happens first.

## 4. Absolute times and final output size

A processed defect is fresh: if it were a historical point, collision would win at or before its arrival. Thus at most `K` defect departures and at most `K+1` excursion constructions occur.

At a completed defect excursion the next restart is `r'=F+1`, so the preceding bound gives `r'-r <= Q <= A`. After `j` processed defects,

    r <= jA.

Any candidate event in that iteration has time below `jA+Q <= T`. Its lane-base times are also bounded by `T`, since `i<S<=A`. On the terminating collision branch, `tau <= T`; on the no-revisit branch the last-tail start is at most `KA`.

For the finite final excursion truncated at a winning collision, let the winning phase have new index `n <= 2B`. Because all phases share one `L`, every phase's truncated endpoint index is at most this `n`: changing the phase can only change the endpoint index by zero or minus one. Thus every finite lane in the complete output has endpoint index at most `2B`.

The final collision excursion need not stay inside the smaller historical box. A sufficient coordinate bound for all of its represented points is

    |coordinate| <= B + 2BS = B(2S+1).

On the no-revisit branch, unbounded future coordinates are represented symbolically by at most `S` unbounded lanes; no future index or coordinate is enumerated. The output contains at most `(K+1)S` lanes, with infinity represented by a fixed symbol.

## 5. Bit size of all intermediate arithmetic

Bounding returned events alone would leave a gap: an implementation could create enormous temporary Diophantine solutions and then cancel them. The frozen intersection routine does not do so.

The following explicit (generous) bound covers its temporary integers. Keep `T` above and put

    U = 2T + 4BS^2 + 2B(S+1) + 2S^2 + 4,
    M = 2T + 4(S+1)^2 U + 4(B+1).

Every integer created in a pair call or excursion construction has magnitude below `M`; input rule/colour indices are additionally bounded by `m=|w|`. To verify this:

1. Spatial coefficients have magnitude at most `S`; right-hand-side coordinate differences have magnitude at most `2B`. Determinants have magnitude at most `2S^2`; Cramer numerators have magnitude at most `4BS`. An integral Cramer quotient has no greater magnitude than its numerator, since a nonzero integer denominator has absolute value at least one.
2. Extended Euclid is applied only to two coefficients of magnitude at most `S`. Its stored Bezout coefficients have magnitude at most `S` (with zero-input cases bounded by one), and temporary quotient/coefficient products by `S^2`. Multiplication by the right-hand side divided by the gcd gives `|n0|, |k0| <= 2BS`. Solution-direction coefficients have magnitude at most `S`.
3. Testing the other spatial equation creates terms and sums bounded by `4BS^2`. Index-bound constants have magnitude at most `2B(S+1)`. The chronological constant has magnitude at most `2T+4BS^2+1`; its coefficient has magnitude at most `2S^2`. Thus every constant and coefficient entering the integer-interval calculation has magnitude below `U`.
4. An interval endpoint is a floor or ceiling of one such integer divided by a nonzero integer. Its magnitude is at most `U`. The selected parameter `z` is either one endpoint or zero. Therefore the intermediate reconstructed indices have magnitude at most `2BS+SU <= 2SU`.
5. Multiplying reconstructed indices by a time period or displacement and adding a base creates numbers of magnitude at most `T+2S^2 U+B`, below `M`. Rank-zero chronology calculations and excursion-coordinate increments are smaller. Truncation uses only already bounded times, periods and indices.

The same estimates cover unsatisfiable pairs, rejected rank-two solutions, inconsistent rank-one systems, and temporary expressions before cancellation. No recurrence exponentiates a previous stage's numbers.

Consequently one may take

    beta = 1 + ceil(log2(max(M,m)+1))

as a common bit-width bound. Since `M` is a fixed polynomial in `K,S,B`,

    beta = O(log(K+2) + log(S+1) + log(R+S+2) + log(m+1)).

## 6. Polynomial running time

The frozen pair-call count is

    P <= S^2 (K+1)(K+2)/2 + SK(K+1).

There are `O((K+1)S)` projected successor steps and `O((K+1)S)` output records. Each intersection uses a bounded number of arithmetic operations, apart from extended Euclid, which has `O(log(S+1))` iterations. Ordinary schoolbook integer arithmetic gives the coarse bit-operation bound

    O(P beta^3)

for all pair calls. Excursion construction, truncation, input validation, and output writing also take polynomial time. Hash-table guarantees are not essential: direct finite-state arrays or deterministic dictionaries suffice; even linear-scan lookup would add only polynomial overhead.

If `N` is the total ordinary explicit binary input length, then `S=O(N)`, `K=O(N)`, `m=O(N)`, and `log(R+1)=O(N)`. Thus `P=O(N^4)` and `beta=O(N)`. The arithmetic estimate above is at most `O(N^7)`, a coarse bound rather than an optimized implementation claim. The compressed output uses `O((K+1)S beta)` bits plus ordinary record overhead, hence polynomial space and output size.

**Conclusion:** the first-revisit problem in the frozen explicit periodic-background/finite-defect model is in P, with a polynomial-time exact compressed certificate algorithm. Numerical time to first revisit may still be exponentially large in input bit length. No analogous polynomial bound for the extension's general observation first-hit procedure is established here.

## 7. Supplemental implementation check

A separate read-only test run imported the frozen `one_visit.py` and checked 10,000 deterministic random instances (seed `301003`; palette dimensions 1–5; rule length 1–5; 0–10 generated defects in `[-20,20]^2`; initial coordinates in `[-12,12]^2`). All instances obeyed the stated excursion-count, stored-base, stored-time, finite-index and final-coordinate bounds. This is a supplementary sanity check, not an ingredient of the proof. The frozen files were not edited.
