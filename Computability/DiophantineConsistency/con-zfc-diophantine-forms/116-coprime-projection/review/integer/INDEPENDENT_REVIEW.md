# Independent review of the eleven-integer coprime-fusion equations

## Result

**PASS for the new ordinary arithmetic reductions and the four advertised literal equations.** No soundness, sign, zero-factor, coprimality, completeness-order, or degree defect was found. The reviewed outputs are:

- `guard_fused11_direct.json`: 11 integer variables, 122 live binary operations, exact degree 728.
- `guard_fused11_aux.json`: 11 integer variables, 126 live binary operations, exact degree 688.
- `fused11_rational.json`: 11 integer variables, 114 live binary operations, exact degree 1632.
- `fused11_integral.json`: 11 integer variables, 114 live binary operations, exact degree 1892.

The source/native/compiler/refutation calibration is an explicitly imported ordinary mathematical theorem, not a new proof-assistant or object-language certificate. This review verifies the new arithmetic composition and its source interfaces; it does not independently reconstruct every imported compiler or model-theoretic theorem. The final Con(ZFC) equivalence has precisely that inherited calibration boundary.

`AUDIT_RESULTS.json` binds the reviewed literal DAGs by SHA-256. `independent_audit.py` provides separate exact algebra, exact leading coefficients, full fixed-coefficient reconstruction, literal diagnostics, and comparisons against actual pinned Git source objects. No finite test is used in place of the unbounded arguments below.

## 1. Literal equation and universal norm

The front-end formulas in `integer/PROOF.md` agree with `build.py`, including the factor 4 in `Dg=1+4D Dt s^2`, the even multiplier `I=2src^2`, and the short scalar carrier `K=X(3c-2X)+2`. The four JSON DAGs use only the eleven stated integer leaves, the six fixed numeral ports, and binary addition/subtraction/multiplication. Every advertised operation count was recomputed.

Independent exact polynomial multiplication of the eight signed linear factors proves the complete 35-coefficient three-root identity. Separately, exact expansion of the literal output nodes with their radicand registers cut to indeterminates proves that each released DAG implements its displayed finalizer. A 495-coefficient four-root identity was also checked, although the scalar four-root experimental siblings are not released.

Independent transcriptions compare every named live register at 27 assignments per equation, alternating arbitrary coefficient residues and genuine coefficient residues modulo three primes. These are explicitly finite implementation diagnostics, not semantic evidence.

## 2. Nonzero bootstrap and signs

The affine restrictions imply `H!=0`, `Delta>1`, `Dt>=1`, and `a+2!=0`, without positivity assumptions on the integer coordinates. If `I=0`, all scaled radicals vanish and the equation reduces to `Ac^8`, `Ac^2`, or `-Ac^2`. None can vanish: `Ac=H^5 pi(T+K/H)` and `pi(x)=(x^2+3)(x^3-19)` has no rational zero.

Hence every zero has `I!=0` and `c,s,r!=0`. The stronger fused multiplier still has absolute value at least `c^2`: its additional integer factors have absolute value at least one. In particular `Dg` cannot be zero because it is odd. The estimate `Df>|c|+1` gives `|V|>=1` by considering `c-R+4IT=0` and its complement separately. Thus `Q>1`, `delta>0`, `Cy>0`, and `Da>0` precede every division or square-root extraction.

For the three-root finalizer a negative `Dg` would produce the sole nonzero imaginary term in a vanishing factor. For either two-term finalizer, positivity of all other factors forces `Dg>=0`, and oddness improves this to `Dg>0`. If `Budget<=1`, then `D<=-1` and `Dg<=-3`. Consequently `Budget>=2`. This recovers the centered strip and common native signs, not an unjustified early assertion that `eta>0`.

## 3. Selective fusion and parity extraction

At a zero, `Df`, `Da`, and `Dt Dg` are positive odd integers. The corresponding signed roots have coefficients 1, 2, and 4 after division by the nonzero scale. In any irrational squareclass, each root is an odd integer times the same odd squarefree radical; the least 2-adic order occurs uniquely, so that class cannot cancel. Independence of distinct squarefree radicals makes all three roots integral.

The identity `gcd(Dt,Dg)=1` is unconditional. Positive coprime integers with square product are individually squares. Therefore the fused first/guard root recovers both original roots, including all signs and possible unit factors.

From `Da=delta Cy` square, `y=sqrt(Da)/delta` is rational and satisfies `QV^2-(Q-1)y^2=1`. The retained adjacent-Pell descent is applicable. In lowest terms the denominator squared divides `Q-1`; multiplication by the norm-one unit of abscissa `2Q-1` preserves that denominator and the integrality of the abscissa while decreasing its absolute value until it is one. Then the ordinate is also one. This proves integrality, rather than assuming that a rational Pell ordinate is automatically integral.

## 4. All-four fusion

The four positive radicands are `Df,Dt,Dg,Da`. All six pairwise gcds are one:

1. `gcd(Dt,Dg)=1` by the guard definition.
2. Divisibility `Dt Dg | I` gives `Df=Da=1` modulo either `Dt` or `Dg`, covering four more pairs.
3. Modulo `Df`, one has `Q=-Delta`, `delta=-(a+2)^2`, `V=-c`, and `Cy=-Dm`; hence `Da=(a+2)^2 Dm`. Since `(a+2)Dm | I`, the remaining gcd is one.

The integral equation makes `(Z/S)^2` equal to the product of the four radicands. The rational-cleared equation makes `(delta Z/S)^2` equal to the same product. A rational square root of an integer is integral; coprimality therefore makes each radicand a square. In the rational-cleared case this does **not yet** imply `Z/S` integral. The adjacent-Pell descent is essential: after it, `sqrt(Da)=delta y` with integer `y`, so `Z/S=+/-f tau g y`. Both variants then yield `S|Ac`. The proof uses this correct order.

## 5. Scalar projection and signed main-Pell recovery

From `S|Ac`, prime valuation comparison in the monic homogeneous quintic gives `H|K`, including negative `H` and primes dividing 3 or 19. If the argument has smaller valuation than `H`, its fifth power is the unique lowest-valuation summand; coefficients divisible by the prime can only raise the other valuations.

The exact polynomial identity `K=HXc-2Kquad`, where `Kquad=X(X+2ac)-1`, and oddness of `H` give `H|Kquad`. This is not cancellation of a possible nonunit modulo `H`.

Independently of that projection, the strong Pell root has `I_abs=psi_B(m)` and `f_abs=chi_B(m)`, with `B=|a+2|`, `I_abs>=|c|`, and `f_abs>2I_abs`. Classifying the auxiliary Pell norm produces an odd index. The quotient-polynomial identity gives `psi_B(nu)=+/-|c| mod f_abs`. Folding the index modulo `2m` and reflecting into `[0,m]`, the strict bound `psi_B(p)+|c|<=2I_abs<f_abs` rules out every wrap and yields `|c|=psi_B(p)`.

This is exactly the missing main-Pell classification required by the **pre-projection** part of the centered signed-rank proof. Its use is not circular. The auxiliary residues remain `V=-c mod f` and `V=-R mod c`; the latter follows directly from `c^2|I`. Lucas composition proves the nonodd strong-rank divisibility, so the incoming even multiplier is never falsely normalized as odd. The rank proof yields `p=R` and the sign-uniform ratio bound before using any main projection.

The retained whole-product estimate then turns `H|Kquad` into `sign(c)X=2^R`: it bounds the whole product below `|H|` and excludes the odd second factor from vanishing. Only afterward are positivity, the centered half-binomial interval, and fresh odd strong/auxiliary witnesses restored. This explicitly reaches the predecessor's actual signed kernel and its imported native/refutation theorem.

## 6. Completeness and interpolation

The canonical native witness fixes all outer quantities, including `Budget` and the square `Dt`, before guard or strong witnesses are chosen. Here `Dt=1 mod 3` because `XY^2` is 0 or 2 modulo 3. Thus `D Dt` is positive and 2 modulo 3, hence nonsquare. Pell existence followed by squaring a unit gives nonzero `s` with precisely `Dg=1+4D Dt s^2` square. No unproved simultaneous-Pell assertion is used.

The full-residue interpolation lemma fixes a strong pair before the carrier residue is selected. Its required modulus is `4 n0 f`, not the insufficient `4 n0`. The source proof shows this is a period modulo `f^2`; the Lucas valuation inequality gives `gcd(4 n0 f,4 I^2)|4I`, which licenses the two index congruences. The canonical promises `R=3 mod 4` and `c=R mod 4` then give an integer `T` in every residue modulo the **same** fixed `I`.

For selective fusion take `N=2s`; for all-four fusion take `N=2s Dt Dg Dm(a+2)`. Every factor in the latter modulus is fixed before interpolation. The theorem's `4Nc^2|I` implies the prescribed quotient defining `r` is a nonzero integer. Intersectivity of `pi` supplies the carrier residue only after `I` is fixed. Interpolation then chooses `T/y`, and the free coordinate `n` closes the equation. This verifies the complete quantifier order and excludes hidden variation of `I` after choosing the residue.

The intersective proof covers all primes, including the exceptional prime 3 via `x=1+3t` and `t+3t^2+3t^3=2`, whose derivative is one modulo 3.

## 7. Exact degree certificates

For the selective pair the degrees of `S,Df,Da,Dt,Dg` are `34,20,114,34,60`. The three radicands have degrees `88,182,162`. In the direct equation the unique highest term is the fourth power of the middle radicand, giving degree 728.

For the centered equation put `W=Sn-Ac`, `B=4S^2 Da`, and `Z=W+S(2Q-1)V`. The exact identity

`Z^2-B=W^2+2WS(2Q-1)V+S^2(V^2+4(Q-1))`

has degree at most 126. Thus `Z^2-B-u-e` has degree 162. The inner bracket of the octic has degree 344 with unique top form `-4 B_top e_top`; the remaining subtracted term has degree 614. The exact degree is consequently 688, with top form `16 B_top^2 e_top^2`. The syntactic 728 bound is not confused with the exact degree.

For all-four fusion `deg I=118`, `deg S=148`, `deg Df=248`, `deg Cy=994`, and `deg Da=1254`. The product term uniquely dominates, giving degree 1632 or 1892. Nonzero monomial certificates, verified by exact sparse polynomial arithmetic, are:

- Direct: coefficient of `j^352 w^88 v^88 s^48 r^48 c^96 T^8` is `2^768 3^440 beta^352`.
- Centered: coefficient of `j^376 w^84 v^96 s^32 r^28 c^56 h^12 T^4` is `2^780 3^462 beta^376`.
- All-fused rational: coefficient of `j^1004 w^186 v^264 s^38 r^12 c^48 h^78 T^2` is `2^1728 3^1203 beta^1004`.
- All-fused integral: coefficient of `j^1164 w^216 v^306 s^44 r^14 c^56 h^90 T^2` is `2^2000 3^1395 beta^1164`.

The exponent sums are respectively 728, 688, 1632, and 1892, and authentic `beta` is positive. These are universal degree proofs, not interpolation from samples.

## 8. Binding and calibration boundary

All six compressed numeral payloads were decompressed, checked against fixed raw hashes and bit lengths, and reconstructed as complete integers from the retained tile/coefficient recipe. The shifted `MF` convention is preserved. The literal machine digest, 943 tile count, and 989 native support count agree.

All nine `upstream_ordinary/SOURCES.json` entries match both their local hashes and the actual Git blob at commit `9a33342a03d19cf5b061b2083c6b5d3f27f752ed`. `PREDECESSOR_BINDINGS.json` also records byte identity of all four directly used new-reduction source notes with the supplied baseline archive/repository.

These source hashes authenticate what was cited; they do not prove the cited mathematics. In particular the copied external Lean endpoint is not an encoded derivation inside the repository's object-ZFC calculus. The report must retain the distinction already made in `CALIBRATION_STATUS.md` and must not advertise a new end-to-end formal certificate, a proof of consistency, or a global minimum.
