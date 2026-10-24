# Fixed-prime radical compression: review

The fixed-prime argument and its compatible pentagonal positivity guard are sound ordinary mathematical reductions under the stated source34/native calibration. All seven complete literal equations pass the full release replay normally and under `-O`, including native numeral reconstruction, live-DAG counts, exact specialized degrees and corruption controls. No Lean or internal object-ZFC certificate is added; formalization remains paused.

The arrival is `1072d31072`, `ConZFC_FixedPrime_Radicals_2026-10-23.zip`, SHA256 `1bb263b6144177021329db51000816d326201a965bb8d80ad976aa8036b12a0e`. Its full 104-file tree and 103 manifest entries are preserved unchanged. The [read-only focused checker](tools/review_fixed_prime_radicals.py) and [normal](data/fixed-prime-radicals-review.json)/[optimized](data/fixed-prime-radicals-review-optimized.json) receipts authenticate all six actual source34 coefficient payloads against the previous integer reviews and independently check every literal DAG's topology and liveness. Replays used complete scratch copies, rather than a deduplicated placed tree.

## Measured complete equations

| Unrestricted integer unknowns | Exact degree | Live binary operations | Comparison after root fusion |
|---:|---:|---:|---|
| 13 | 1392 | 475 | Dominated by root fusion |
| 13 | 1408 | 473 | Dominated by root fusion |
| 14 | 652 | 230 | Surviving lower-degree tradeoff |
| 14 | 664 | 223 | Surviving lower-cost tradeoff against preceding row |
| 14 | 700 | 217 | Dominated by root-fusion14/696/150 |
| 14 | 748 | 215 | Dominated by root-fusion14/696/150 |
| 15 | 214 | 139 | Lower degree, more operations than root-fusion15/344/131 |

The archive predates the root-fusion comparison. Its 13-variable endpoints do not improve the now-available 13/1088/195, 13/1392/186 or13/1408/185 alternatives. The two centered fourteen-variable equations and the fifteen-variable equation remain useful. These comparisons use the identical whole source34 tuple, unrestricted integer domains and live binary-operation convention. They are not comparisons of expanded coefficient height or bit complexity.

The fixed leaves are exactly `beta,K0,MC,MF,cone_A,cone_B`, with `beta=2^1064921-1`, MF already shifted, `cone_A=2^1113`, `cone_B=2^666104`. Their decompressed bytes total 615,883. Both the authoritative and component copies authenticate to the preceding root-fusion and saturated-certificate raw hashes. No compact36/compact44/H2082 substitution occurs.

## The reusable valuation lemma

Let nonzero rational radicands d_i have pairwise distinct even valuations at a fixed prime p. A rational signed sum of their square roots forces every d_i to be a rational square. This holds for signed d_i and therefore does not presuppose positivity.

To prove it, group the radicands by rational squareclass. In one class write `sqrt(d_i)=a_i sqrt(d)`, absorbing signs into nonzero rational a_i. The distinct valuations of d_i give distinct valuations of a_i. Their sum cannot vanish: clear denominators and divide by the uniquely least-valued term, leaving one p-adic unit and all other terms divisible by p. Distinct squareclass radicals are linearly independent over Q, as follows from character projections in the finite multiquadratic Galois extension. Thus no nontrivial squareclass can occur in a rational total sum. Negative squareclasses are covered by the same extension argument.

This avoids a common failure of ordinary root-sum compression: signed cancellation inside dependent squareclasses. For example, `sqrt(2)+sqrt(8)-sqrt(18)=0` does not make those roots rational, but the distinct-valuation hypothesis fails there. The present proof needs neither pairwise independent squareclasses nor an ordering of the root magnitudes.

The literal affine restrictions give, for every signed input,

```
J=6j+1, q=beta J+1=2 mod3,
W=4(3w+1)=1 mod3, X=qW=2 mod3,
Y=(2v+1)q³, a=(X+1)Y,
Delta=a²+4a+3, H=4a+3.
```

Hence `3|Delta`, `3|H`, and H is a nonzero odd integer. The four Pell base radicands are all 1 modulo3, including the rational auxiliary radicand

```
(QV²-1)/(Q-1), Q=Delta²(2r+1)²c⁴.
```

Here `Q-1=-1 mod3`, so its denominator is nonzero before any guard is known. The pentagonal base radicand below is also1 modulo3. Weighting the five roots by `3H,9H,1,81H,27H` gives squared-root valuations `2e+2,2e+4,0,2e+8,2e+6`, where `e=v3(H)>=1`. They are distinct even integers for every signed input. No zero radicand is silently removed.

## Positivity and the order of soundness

The fifth base radicand is

```
S=24N-21-(6u1-1)²-(6u2-1)².
```

It is always1 modulo3. For every integer N,

```
N>0 iff there exist integer u1,u2 with S a rational square.
```

A rational square root of integer S is integral. If S is square, `24N-21>=2`, so N>=1. For completeness, write `24N-21=9^e M0`, with `M0=3 mod8` and `9` not dividing M0. Legendre's three-square theorem represents M0 by three odd squares. The integral matrix

```
L = [ 1  2  2 ]
    [ 2  1 -2 ]
    [-2  2 -1 ],    transpose(L)L=9I
```

multiplies squared norm by9. For every vector nonzero modulo3, independent sign changes make all three coordinates of its L image nonzero modulo3. Iterating e times gives three odd coordinates coprime to3. Choose their signs to be -1 modulo6, obtaining S square. When e=0, the original three coordinates are already all units modulo3 because their squares sum to0 modulo3 and they are not all divisible by3. The archive includes this proof and correctly attributes the classical three-generalized-pentagonal theorem; the theorem itself is not new here.

At a new norm zero the valuation lemma first makes all five roots rational, including S. It follows that N>0. The joint guard then gives determinant G>0 and `eta*zeta>0`. Only now does one derive `|c|>2` and Q>1, then apply the denominator-preserving adjacent-coefficient Pell descent to the auxiliary rational root. This sequence handles c=0 and all signed inputs without assuming the desired guard or inferring integer roots from an arbitrary rational Pell equation.

The main carrier recovers `H|(d-D0)` because the other weights are multiples of H and the auxiliary root is now integral. The explicit maps restore the main quotient, the half-centered first root, the old odd strong coordinate `(Delta(2r+1)-1)/2`, and `T_old=fT`. The private old positivity triple is regenerated from N>0. The focused checker verifies the first-root, auxiliary and gap identities over a free sparse integer polynomial ring.

## Completeness and the companions

Completeness uses the source34 canonical family, not an assertion that every old zero has the new normalization. Its native repunit satisfies `J=1 mod6`, and `W/4=2^(R-t-2)=1 mod3` because R,t are odd. Thus the stronger affine restrictions preserve canonical existence. The canonical main Pell witness has positive odd c and `R=3 mod4`.

The construction chooses the new strong witness at index Rc. Composition proves `c²|psi_A(Rc)`; the recurrence modulo2 proves the quotient is odd. It then chooses the squared-modulus auxiliary witness with residues `V=-c mod f²` and `V=-R modc`, making `T=(V+c+Rf²)/(cf²)` integral. This is an explicit Pell construction, not a cofinality assumption. Choose the pentagonal witnesses and only then the free carrier coordinate. The named inherited determinant/native calibration applies to this same canonical family; an arbitrary same-sign tuple would not by itself prove determinant completeness.

The fourteen-variable equations retain three old positivity coordinates and use a four-root norm. Their finalizer `(1+4G0)(1+4N14)-1=0` forces both residuals to vanish: integer factors whose product is1 are units, and -1 is excluded modulo4. No sign promise on N14 is needed. Doubling the carrier and all root weights restores the main quotient via `H|2(d-D0)` and odd H. Centering auxiliary, first and normalized strong roots yields norm degree608 and final degree652; the other centers yield the declared664/700/748 controls.

The fifteen-variable equation keeps f and the ordinary strong residual, with `J=3j+1`. Its three-factor unit finalizer first forces the strong row, guard and three-root norm to vanish. The guard gives Q>1; the strong row gives `3|I`, so the norm denominator is nonzero and the three relevant roots have distinct valuations. The doubled main carrier gives the missing parity and quotient exactly. Its compact three-root norm has degree156, and the retained strong/guard factors add14 and44, giving attained degree214. No normalization or pentagonal theorem is needed for this companion.

## Evidence and immediate size lead

Both full release modes reconstruct the native coefficients, compare all seven DAGs byte-for-byte with their builders, check exact specialized nonzero degree witnesses, and compare the main article formula against an independently written multiquadratic evaluator on48 signed modular assignments. Both modes pass the component norm/adaptor checks and coefficient/input corruption controls. The delivered graph mutation control detects a mismatch with the regenerated graph; it should not be described as a universal semantic counterexample detector.

The independent focused tool checks all seven graphs and every input/fixed leaf live, the matrix identity, all26 nonzero modulo3 vectors,729 base-radicand residue controls and512 positive pentagonal fixtures. These supplement the universal arguments; they do not test consistency or replace the unbounded source theorem.

The universal norm evaluator is a concrete next reduction target. This archive expands generic Taylor coefficients, costing475 operations in the centered thirteen-variable equation and230 in degree652. Root fusion supplies much smaller division-free biquadratic norm recipes. Replacing only this universal evaluator can preserve the **entire polynomial**, coefficient binding and exact degree, while lowering the live graph count. That is a separate candidate to materialize and prove over free radicands; no reduced count is asserted by this review.
