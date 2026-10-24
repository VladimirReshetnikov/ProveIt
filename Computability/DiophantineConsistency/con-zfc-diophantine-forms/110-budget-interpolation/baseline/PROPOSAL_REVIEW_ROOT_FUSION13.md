# Thirteen-integer root fusion: ordinary proof and release review

The new root-fusion reductions are mathematically sound under their stated inherited source34/native/Pell calibration. In particular, the five-root argument establishes realness and its strict guards before extracting square roots, and its CRT variant recovers both missing congruences without assuming them. The supplied whole equations and source coefficients pass the complete release verifier normally and under Python `-O`. This is ordinary mathematical and finite arithmetic evidence; it adds no Lean or internal object-ZFC theorem. Lean work remains paused.

The reviewed arrival is `751bc067e2`, `ConZFC_13_Integer_Norms_2026-10-24.zip`, SHA256 `d800f0fb608d4301b8888b589a97477da836b00c93c66db0668e1cc0c2b0b41f`. All 93 original files and 92 manifest entries remain unchanged. The [focused tool](tools/review_root_fusion13.py) authenticates the whole tuple, checks independent local identities, and embeds both full release receipts in the [normal review receipt](data/root-fusion13-review.json). The [optimized focused receipt](data/root-fusion13-review-optimized.json) repeats the same explicit checks; assertions are not the acceptance mechanism.

## Complete equations and comparisons

| Unrestricted integer unknowns | Exact degree | Live binary operations |
|---:|---:|---:|
| 13 | 1088 | 195 |
| 13 | 1392 | 186 |
| 13 | 1408 | 185 |
| 14 | 696 | 150 |
| 14 | 792 | 137 |
| 15 | 344 | 131 |

All rows are complete fixed equations with counted live addition, subtraction and multiplication, rather than local gadget estimates. Every row uses the same six fixed leaves and whole source34 tuple. The three thirteen-variable rows are genuine cost/degree tradeoffs. Translating the norm carrier by the auxiliary register V lowers degree from 1408 to 1392 for one extra addition; the CRT carrier lowers it further to 1088 for nine more operations. The fourteen-variable pair likewise trades thirteen operations for a degree reduction of 96. No optimality or coefficient bit-complexity claim follows from these DAG counts.

The four quotient companions are 20/24/120, 19/28/116, 18/32/112 and **17/88/110**, in variable/degree/operation order. The last improves the recently reviewed saturated-certificate 17/88/114 interface by four operations. It uses the stronger auxiliary expression `V=f²(cT-R)-c` and a fresh canonical squared-modulus construction. It is an equivalent calibrated existence statement, not the identical polynomial or a pointwise projection of every preceding zero. The fifteen-variable degree344 point has fewer unknowns and greater degree than that seventeen-variable endpoint; lower-operation or lower-degree endpoints with other numbers of variables remain separate tradeoffs.

## Binding and proof dependencies

The six decompressed payloads, totaling 615,883 bytes, match all six raw hashes of the earlier saturated-certificate review:

```
beta=2^1064921-1, K0, MC, MF (already shifted),
cone_A=2^1113, cone_B=2^666104.
```

The tuple is `mixed-parity-unrounded-1064921`, pinned to source commit `2605669a532342f153b13eb6b4a0af4b54f5fa37`. No compact36/compact44/H2082 coefficient is substituted. The release replay reconstructs all six integers from the retained machine, all 943 tiles and 69,230 basis convolution checks. This authenticates the complete finite recipe. The unbounded native/refutation correspondence and ordinary source34 orientation/Pell results remain named mathematical dependencies; their truth is not established by a finite replay.

The following common registers expose the relevant order of reasoning:

```
J=6j+1, q=beta J+1, W=12w+4, X=qW,
Y=(2v+1)q³, a=(X+1)Y, H=4a+3, Delta=a²+H,
i=2r+1, I=i c², Df=1+Delta I²,
Q=Delta² I², delta=Q-1,
V=Df(cT-R)-c, Cy=QV²-1.
```

The five radicands are `Dm`, `H²Df`, `H²Dt`, `H²Ag`, `H²Cy/delta`, where `Dm=1+Delta c²` and Dt is the first-index norm. The printed equation is the product over all 32 sign choices, cleared by `delta^16`. It is an integer polynomial; the division-free evaluator and exact generic norm identity are separately checked.

## Guard first, root extraction second

For every signed integer input, q is even, `q=2 mod3`, `|q|>=16`, W is nonzero, `|X|>=64`, a is even, `Delta>1`, and H is nonzero. Thus Dm, Df and Dt are positive before invoking any source equation. If c=0, then Q=0, delta=-1 and Cy=-1, so the auxiliary rational radicand is still positive. If c is nonzero, then Q>1 and `Df>|c|+1`; splitting on `cT-R=0` proves `|V|>=1`, hence `Cy/delta>=1`. There is no discarded zero denominator or assumption c>0 here.

Consequently the only potentially negative radicand is Ag. If Ag<0, each conjugate factor has exactly one nonzero imaginary summand and all its other summands are real, so it cannot vanish. Norm zero forces Ag>=0. Its private representation gives

```
Pair=G eta zeta-(t²-G-eta zeta+1)²>0,
Ag=Pair-1-p2²-p3(p3+1).
```

The joint positivity lemma now gives G>0 and eta*zeta>0. In particular c=0 is excluded at this stage because it would give `eta*zeta=-Y(Y+1)k²<=0`. The guard is proved before using squarehood or strong-rank conclusions.

Writing `Cabs=|c|`, `K=|k|`, the guard gives `K>=2` and

```
K(|Y|-1)<Cabs<K(|Y|+1).
```

The determinant identity

```
12G=4q²-[3(cone_A F+cone_B C)-4q]²
          -3(cone_A F-cone_B C)²
```

supplies the small guard-root bound. Together with the main, first and strong bounds this makes the five nonnegative root magnitudes superincreasing, with their order depending on whether `cT-R` vanishes. The zero guard root is omitted. This establishes that **every nonempty signed subset of the nonzero roots** has nonzero sum. Merely separating their total sum would be insufficient: `sqrt(2)+sqrt(8)-sqrt(18)+10+11=21` is a counterexample to that weaker argument.

The multiquadratic automorphism argument therefore forces every root to be rational even when their square classes are dependent. Rational roots of integer radicands are integral. The final auxiliary rational root becomes integral by the adjacent-coefficient Pell descent. No pairwise-coprime squareclass hypothesis is introduced.

## Restoring the ordinary source and completeness

Once the strong root f is integral, the ordinary source witnesses are restored by

```
I_old=Delta i c²,
r_old=(Delta i-1)/2,
o_old=f(cT-R),
j_old=Df T-1-R Delta i² c³.
```

Delta and i are odd, so r_old is integral. The exact polynomial identities give `f o_old-c=V=c j_old-R`. The signed strong/root witnesses and old private guard triples are thus genuine integers. There is no quotient inferred from a congruence before its divisibility is available.

Completeness chooses a compatible canonical family; it need not transform every old zero. For `A=a+2`, canonical odd `R=3 mod4` gives odd `c=psi_A(R)`. The fresh choice `I*=psi_A(Rc)` is divisible by c². Composition gives that divisibility, and the recurrence `psi_A(n)=n mod2` proves that `i=I*/c²` is odd. Inferring this parity just from the first binomial term would be inadequate. A subsequent squared-modulus Pell choice gives

```
V*=-c mod f²,  V*=-R mod c,
T=(V*+c+Rf²)/(cf²) in Z.
```

The required gcd(c,f)=1 is already available from the canonical strong norm. Guard witnesses are chosen next, and only then the total root carrier n. The order avoids choosing a witness by a condition involving that same witness. The retained source34 proof supplies joint determinant/native/parity calibration for this canonical family.

## Why the degree1088 CRT variant is valid

The CRT variant starts with `Y=qv`, allowing v=0 initially. Its guard is instead `Ag=v²Pair-1-p2²-p3(p3+1)`. Unconditional realness still holds, including v=0 (where a=0, Delta=3, H=3). Norm zero first forces Ag>=0, hence v is nonzero and Pair>0. Only then may the strict bounds use `|Y|>=|q|` and `Cabs>30`.

Put `M=2q²`, `Lambda=4H+1`, `U=MH`. The center is

```
Z=U(n+V)+M Lambda b0+H(v-q²), b0=X+ac.
```

The main-root weight is `M Lambda`; the other four weights are U. The ratio `Lambda/H` lies strictly between 3 and 5 for every permitted signed H. The revised separation estimates are proved before root extraction; the main/first ordering is not copied from the unweighted construction. The focused tool independently verifies the relevant positive-coefficient inequality on the full `|X|>=64,|Y|>=16` cone.

After integrality, reducing the root relation modulo M gives `v=q² mod 2q²`, restoring exactly `Y=(2v_old+1)q³`. Reducing modulo H gives `H|(d-b0)`, restoring the main quotient. These cancellations use the actual facts `H=3 modq`, `q=2 mod3`, H odd and `Lambda=1 modH`, hence `gcd(H,M)=1`. They do not use the generally false assertion `gcd(H,q-1)=1`.

The new private guard represents v²Pair. Soundness regenerates an old private triple for the positive unscaled Pair; it does not pretend the same triple represents both numbers. Completeness takes v=Y_old/q, regenerates the scaled private triple, then chooses

```
n=Lambda gamma+f+tau+p1+y-V-(v-q²)/M.
```

This is an integer by the restored residue and satisfies the complete carrier equation exactly. The CRT coefficient witness is `2^976 3^640 beta^480` at `j^480 w^160 v^208 h^32 r^64 c^128 z^16`, proving attained degree1088 on this fixed slice.

## Replay boundary

Both scratch full releases pass. They verify all six norm equations and four quotient companions, complete fixed coefficient reconstruction, exact generic three/four/five-root norm polynomials (35/495/20,349 monomials), circuit identity/topology/liveness and exact degree witnesses. Both reject the operation-preserving 64-to-65 norm-coefficient mutation. The focused checker additionally verifies determinant, restoration and CRT carrier identities over a free sparse integer polynomial ring, and 175 signed CRT residue controls including v=0 and negative H.

No mathematical defect was found in the new ordinary reductions. Finite controls are diagnostics, not searches for a refutation or proofs of the universal source semantics. A Lean proof, an internal nonstandard-omega transfer and an independent reproving of the inherited unbounded native theorem are not claimed here.
