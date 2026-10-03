# Independent review of the complete74 equation-orientation family

**PASS; no correction requested.** I read the frozen author source and complete note, reconstructed the 56 intended instruction sets, and checked the actual saved schedules and finalizers without importing or executing the author helper or any historical compiler. The [independent checker](review_complete74_equation_orientation_census.py) and [receipt](review_complete74_equation_orientation_census.json) authenticate the complete author trio and all ten declared dependencies.

| Interface | Positive witnesses | Equations | Complete certificate | Complete SOS | Symmetric minimum degree | Asymmetric minimum degree |
|---|---:|---:|---:|---:|---:|---:|
| raw30 | 30 | 19 | 74 = 40M + 34A | 130 = 59M + 71A | 20 | 20 |
| positive22 | 22 | 11 | 74 = 40M + 34A | 106 = 51M + 55A | 56 | 48 |
| signed20 | 20 | 9 | 74 = 40M + 34A | 100 = 49M + 51A | 84 | 64 |

These are minima in the declared 56-source family. The verified sources give these degree upper-bound witnesses for the inherited ordinary-input universal relations on admissible fixed compiler slices. They do not improve the operation bounds of 74 for comparisons or 86 for the separate product polynomial, establish unrestricted degree optimality, or supply a maintained compiler API. The name `signed20` permits signed computed intermediates; its supplied witnesses remain strictly positive.

## 1. Actual source reconstruction and paid scope

The independent emitter starts from the pinned original74 JSON and applies only the named producer changes. It enumerates 16 raw, eight positive22 and four signed20 choices at each of two scales. I compare every resulting producer and operand with the saved source, then verify the actual saved order is topological. Different valid topological orders are allowed; no arithmetic gate is added, omitted or treated as free in this comparison. The asymmetric baseline is also compared literally with the separately authenticated asymmetric74 source.

All supplied coordinates and fixed numeral ports are preserved. Every comparison is checked in its actual order. Every subtraction, square and accumulation instruction in each complete SOS is independently rebuilt. All advertised free ports and all instructions are live. The totals are 4,144 certificate instructions and 6,656 complete polynomial instructions across the 56 saved sources, with 856 comparisons.

The checker uses the actual supplied `k` in raw30. It does not replace that coordinate by `eta+zeta` off the equality locus. The positive22 input-gap orientation redirects both remaining kappa consumers and retains the old computed index. No corresponding gap switch is available or emitted for signed20.

## 2. Exact scope of zero equivalence

The defining residual identities are all-value polynomial identities:

```
a-(XY+Y) = (a-Y)-XY,
c-(kY+eta) = (c-eta)-kY,
c-(kappa+phi) = (c-phi)-kappa.
```

Their retained equations therefore define the same locus before any other equation is used. On that locus, every redirected downstream value agrees with its old producer. The auxiliary alternatives are protected by the unchanged strong comparison `(i*c²)² = Delta*(f²-1)` and linear comparison `j*c-r = o*f-c`.

My independent affine-normalized expression DAG verifies all 96 chosen protecting residuals identically before imposing any cut. It then derives the monic free-coordinate substitutions directly from the original source and checks their absence of cyclic dependencies. For the auxiliary cuts it verifies that both right sides are independent of both cut ports. Under precisely these retained equations, all 856 complete residuals and all 56 finalized SOS expressions agree. No author-provided symbolic cut certificate is trusted as evidence.

This proves both directions: a zero of either comparison system satisfies the common protection equations, on which every remaining residual agrees. The comparison zero sets thus coincide over commutative rings; over the reals, the SOS zero sets also coincide. In particular this is a same-coordinate bijection on positive integer zeros within each fixed scale. No positivity of the reoriented computed differences is assumed off zero.

The full polynomials generally differ away from the protection locus. This review does not promote conditional equality to an unconditional polynomial identity. Across symmetric and asymmetric scales, the required positive-zero coordinate change is the separate authenticated asymmetric74 theorem, including its divisibility proof; it is not deduced from the equation orientations.

## 3. Uniform exact degrees, independently certified

The degree proof is not based on testing 56 fixed numerical compiler instances. I execute every actual source in the exact integer polynomial ring

```
Z[t, Bm1, Kconstant, twice_cell_bits, inner_bits, MC, MF].
```

Each supplied witness and ordinary input is replaced by a distinct positive integer multiple of `t`. All six fixed numeral ports remain independent symbolic variables throughout the expansion. Thus the exponent of `t` measures the intended degree after specialization, while the numeral symbols still describe every fixed compiler slice.

For an upper bound, I independently propagate total degrees with fixed numerals assigned degree zero. I guard the complete main and input norm cones against the reconstructed literal source and prove their cancellation identities by exact coefficients in independent formal atoms. Writing `H=Delta-a²`, these identities are

```
(X+ac+G)²-(a²+H)c²-1
 = X²+2Xac+2XG+2acG+G²-Hc²-1,

(W+a*kappa+rho*H)²-(a²+H)*kappa²-1
 = W²+2aW*kappa+2rho*W*H+2a*rho*kappa*H
   +rho²*H²-H*kappa²-1.
```

For every one of the 856 actual residuals, the exact symbolic `t` degree attains its independently derived upper bound. More strongly, every form has at least one maximal residual whose specialized leading coefficient is a **single nonzero monomial in `Bm1` alone**. The other five fixed-symbol exponents are zero. The full coefficient and its monomial are saved in the review receipt. Therefore this leader cannot vanish on any admissible slice `Bm1>0`, regardless of the other fixed numerals. A specialization cannot increase degree, so the uniform upper bound is attained. Finally, a real sum of squares has a nonzero sum of maximal homogeneous squares, proving the claimed exact full SOS degree uniformly.

This is a symbolic nonvanishing certificate, not interpolation or a finite sample argument. The author’s separate modular diagnostics are not needed for this conclusion.

The independently obtained raw first-residual degrees, ordered by the two binding switches `00,01,10,11`, are `26,18,18,10` symmetrically and `22,14,18,10` asymmetrically. Auxiliary switches do not alter the resulting raw minimum. In projected forms the auxiliary residual degrees, ordered by coefficient/root choices `00,01,10,11`, are `34,32,30,28` symmetrically and `34,32,26,24` asymmetrically. The old input residual has degrees 42/32; the reversed positive22 input residual has degrees 22/18. These give all six minima in the table.

Ties are preserved. For example, the doubly reversed raw first norm can tie the original auxiliary residual at degree 10, and the asymmetric signed20 root-only auxiliary rewrite ties the input residual at degree 32. No unique-leading-residual assumption is needed for the SOS argument.

## 4. Receipt, replay and limits

The independent receipt records 56 complete source checks, 856 symbolic residual expansions, 96 unconditional protection identities, 56 full conditional polynomial identities, 56 uniform exact-degree certificates, all degree histograms and six minima. The actual author degree metadata, including the honest gate-level upper bounds and all dominant-residual ties, agrees with these checks.

Replay with the author trio and dependencies in the same directory:

```
python3 review_complete74_equation_orientation_census.py \
  --root /path/to/native-stream-queue \
  --expect review_complete74_equation_orientation_census.json
```

If the frozen author trio is elsewhere, pass `--author-root /path/to/author-trio`. Only the Python standard library is required. The helper checks hashes before reading mathematical packets and rejects optimized execution. This is a standalone research review CLI; it makes no hostile-packet or maintained in-process API claim. I did not rerun any historical source suite or broaden the finite orientation search.
