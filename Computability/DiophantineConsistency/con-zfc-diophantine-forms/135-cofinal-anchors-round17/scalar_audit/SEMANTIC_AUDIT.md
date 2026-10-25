# Independent audit of the eleven-integer linear-cofactor family

## Verdict

PASS, with the inherited ordinary native/compiler/refutation calibration boundary retained exactly as stated in the release. No defect was found in the new arithmetic zero-existence reduction, its six literal equations, the four recommended metrics, the complete coefficient specialization, or the portable executable replay.

The independently verified recommended degree/operation pairs are 328/130, 340/129, 352/125 and 398/121. The 366/126 and 382/125 weak-scale equations are valid but dominated controls. Each graph has eleven unrestricted integer variables and the same six fixed positive numerical ports. This audit makes no global-minimum, consistency-truth, new proof-assistant, or encoded object-ZFC endpoint claim.

The producer directory was not edited. New audit files are kept separately in `scalar_audit/`.

## Independent finite verification

`audit_scalar.py` imports no producer, producer checker, coefficient-recipe code, or release polynomial implementation. Its newly implemented sparse polynomial arithmetic checks:

1. All 131 release-file pins and all 110 retained source/coefficient/license pins, including inclusion of each pinned dependency in the release whitelist.
2. The six actual minimal unsigned little-endian numerical payloads, their byte lengths, bit lengths and SHA-256 values.
3. A fresh reconstruction of all 430 machine actions, all 943 ordered tiles, and all four joint source34 ports; both cone ports are separately rebuilt. MF is compared after the beta shift, not before it. No individually substituted or symbolic-only coefficient is accepted.
4. Binary topology, exact operation census, full liveness, the exact eleven variable leaves, exact six numerical leaves, and all literal polynomial definitions. Every reference used as a local cut must already have been verified; the checker does not accept a self-referential or unverified register name as evidence.
5. The full four-conjugate norm identity, the cofactor rescaling and product identities, the coprimality remainders, both exact center identities, and the entire centered cancellation identity.
6. The complete highest homogeneous polynomial at every live gate, not merely one numerical specialization or a syntactic bound. All genuine variable-monomial coefficients are grouped before specializing the six ports. Each group has one nonzero sign, and all six authenticated ports are positive; specialization therefore cannot annihilate it. The only cancellation cut is the independently expanded centered-inner identity. Its unique highest term is checked against the complete leading polynomial.
7. Every advertised recommended graph hash, degree, operation count, leading monomial and actual leading coefficient in RESULTS.json.

Normal Python and `python -O` produce byte-identical audit JSON. Fifteen targeted formula/metadata corruptions are rejected in each mode. `audit_mutations.py` additionally changes every live arithmetic gate once, across all six graphs: all 756 corruptions are rejected, normally and under optimization.

`replay_release.py` copies only the release whitelist plus its manifest to a new temporary directory and runs the release replay there, with PYTHONPATH and PYTHONHOME removed. The clean build, normal checker and optimized checker all pass, and all generated graph, metrics and checker-report bytes agree with the frozen release. This establishes executable/numerical closure; it is not an unbounded proof checker.

## Semantic review

### 1. Unconditional and zero cases

The fixed beta and affine front end give q even, q = 2 modulo 3, X divisible by 8, X = 2 modulo 3 and |X| >= 4|q|. Consequently a is divisible by 3. For Y = 0, A = 2 and Delta = 3; otherwise |a| >= |X|-1 excludes A = 0 and gives Delta > 1. H is odd and cannot vanish. These statements do not require any sign of q, X or Y.

Dt >= 1 follows from the integer consecutive-product inequality. The cone multiples are divisible by 16, so B0 + (qk)^2 is divisible by 16. Both definitions of Budget therefore imply D = Budget-4 is 8 or 12 modulo 16. Thus D is nonzero and nonsquare, Dg and P are odd and nonzero, and Dt is 1 modulo 8. This argument applies to negative budgets too; positivity is not smuggled in.

Q cannot equal 1, Df cannot equal 0, and Q is even for both parities of A. Therefore delta is odd and nonzero. Cy cannot vanish either. The zero-free rational quintic and Dc != 0 give Ac != 0. At S = 0 the final polynomial is delta^2 Ac^4, not zero, so s and r are nonzero at every zero.

The Da positivity split is valid in all three cases: c = 0 gives Da = 1; c != 0 and B < 0 makes both auxiliary factors negative; c != 0 and B > 0 makes Df > |c|+1 and V != 0. In the latter case Cy > 0. For c != 0, B and Df have the same sign. No negative root case is discarded without an argument.

### 2. Two-root separation and coprime recovery

The norm identity is valid over the complex numbers even when its radicands are dependent or negative. After S and delta are known nonzero, a vanishing factor gives a rational signed sum of 2 sqrt(B Df Da) and delta sqrt(P).

Exactly one negative radicand is impossible by its imaginary component. If both are negative, c must be zero and imaginary cancellation would require 4B = P, contradicting P = 1 modulo 4. Both radicands are thus positive.

For a common nontrivial squarefree class, the first root has an even coefficient and the second an odd coefficient, because P and delta are odd. Cancellation is impossible. Different nontrivial squarefree classes are rationally independent. Thus both radicands are squares.

The three factors B, Df and Da are nonzero and pairwise coprime. The exact remainders are Df = 1 modulo B, Da = 1 modulo B, and Da = A^2 Dm modulo Df; moreover Df is 1 modulo each of A and Dm. The claims hold with signed B and Df. Absolute prime valuations therefore make each factor a signed square. Da is positive, so B and Df have the same sign; Df = 1 modulo 3 excludes their negative-square branch. This recovers B = u^2 and Df = f^2 positively. It does not incorrectly conclude that r or Dm was a square at this stage.

The independent gcd(Dt,Dg) = 1 recovers the first and guard squares. Since s != 0 and Dt >= 1, Budget <= 3 would make Dg <= 0. The mod-16 restriction strengthens Budget >= 4 to Budget >= 12.

### 3. Scale, strip and denominator order

In the free family, the positive Budget forces k and Y nonzero and B0 > 0. Since B0 <= k^2 q^2, it gives |Y| > |q|^3. The centered strip then excludes c = 0. The common-sign disk argument works for either sign of q, and it restores exactly the inherited signed packing interval for R.

Define proof-only I = c^2 u and T_old = uT. The equality A U = c^2 B makes the literal auxiliary expression exactly f^2(c-R+4I T_old)-c. Thus c^2 divides I and I is nonzero whenever c is nonzero. These are the needed strong-rank hypotheses, not an oddness requirement on I/c^2.

The rational auxiliary root has an integral denominator descent. A reduced denominator b satisfies b^2 | Q-1; the stated unimodular transformation keeps V integral and preserves the reduced denominator, because 2Q-1 is 1 modulo b. After choosing signs, V > 1 implies V < y < QV/(Q-1), so the new V lies strictly between -V and V. It cannot be zero. At |V| = 1, |y| = 1. This proves integrality. The c = 0 branch has Q = 0 and y = -1 directly, so the weak-scale argument can establish S | Ac before excluding c = 0.

### 4. Carrier divisibility and pre-projection rank

For either sign of M and H, the monic valuation comparison in the homogeneous quintic proves M | zc from M^5 | Ac. In the free family it initially gives only M | H(Y-q^3). Taking its 2-primary part is legitimate because H is odd, and gives even Y. The proof correctly postpones gcd(H,q) = 1.

Reducing Ac modulo H and using K = HXc-2Kq gives H | q^15 Kq^5 in the free family. No nonunit q is canceled at this point.

The omitted main square is recovered by the absolute Pell folding argument using B_abs = |A|, C_abs = |c|, I_abs >= c^2, f > 2I_abs and V = -c modulo f. The fold lies between 0 and the strong index; its possible residue has magnitude strictly below f, so it cannot wrap. This recovers |c| = psi_|A|(p) with p >= 1 without a main projection or sign assumption.

The source's nonodd strong-rank proof applies: c^2 | I implies p | m; composition then gives |c| | m/p, so |c| | m and m > 2p. The two residues V = -c modulo f and V = -R modulo c follow from the exact restored auxiliary formula. The centered strip and |XY| > 3R+1 provide the first-index and no-wrap bounds. Consequently the pre-projection conclusions p = R = 2t+1 and the uniform ratio-growth bounds are licensed before any power-of-two conclusion.

For weak scale, H = 3 modulo q and q = 2 modulo 3 give gcd(H,2q^2) = 1 immediately. Its carrier restores Y as an odd multiple of q^3, then excludes c = 0 using B0 > 0. The same rank argument uses |Y| >= |q|^3; strict inequality is not required there.

### 5. Fifth-power projection and original source restoration

For free scale, the projector gives H | q^15 Pi^5. With x = |X| and R = 2t+1, the explicit bounds are

    |q|^15 |Pi|^5 < 2^(20t-10) x^25,
    |H| > x^(t+1)/2^t.

The inherited packing bound implies t >= 36. At x >= 2^64, the exponent margin is 64(t-24)-(21t-10) = 43t-1526 >= 22. The divisible integer is strictly smaller than |H| and must vanish. The second factor of Pi is odd and nonzero, so sign(c)X = 2^R. This is a whole-product bound, not an invalid cancellation modulo composite H.

Only now does q | X imply that |q| is a power of two, permitting the full free-scale carrier congruence to be canceled through odd H. The literal odd cubic scale follows. The mod-3 restriction then chooses c > 0 and X > 0; the surviving first-index sign gives k > 0 and the strip gives Y > 0. The inherited centered half-binomial result recovers the positive narrow interval.

The final handoff is not merely a list of inequalities. The proof names the exact fresh odd strong and auxiliary witnesses I_star, f_star, rho_star, V_star and y_star. The quotient-polynomial residues restore the original signed Q41 private coordinates, and the square coordinate restores its positive power-of-two chart. Thus the inherited native/compiler theorem receives an actual old source zero. It is not applied prematurely to the new graph.

### 6. Completeness and fixed-pair interpolation

The canonical source supplies even positive A, Dm = d^2, the first square, the narrow positive strip and B0 > q^2 k^2/4. Its large canonical Y makes both budgets greater than 64. Therefore D is positive and nonsquare; multiplication by the already fixed nonzero square Dt preserves nonsquareness, so ordinary Pell existence supplies the guard s,g.

The next choice is one strong pair with 4s A d c^2 dividing I. With t_strong = I/(A d c^2), u = A d t_strong and r = A t_strong^2, the identity r A Dm = u^2 holds exactly. Every prime of u s r divides I. This matches the supported-modulus theorem's actual hypothesis, rather than assuming u s r itself divides I.

The intersective quintic has roots at all prime powers: ordinary simple-root lifting handles generic primes and 2 and 19; at 3, x = 1+3t reduces the equation to a polynomial with derivative 1 modulo 3. CRT handles any positive modulus.

After the pair I,f is fixed, choose a quintic root class a0 modulo sr, then request T_old = u a0 modulo u s r. Supported-modulus interpolation applies to the same pair and supplies an integral auxiliary root. Division by u is licensed by that congruence and gives T = a0 modulo sr. The carrier quotient is therefore integral. Finally the displayed n annihilates one norm factor. There is no reselection of the strong pair after requesting a residue and no missing divisibility before division.

The supported-modulus theorem itself was checked at its interface and proof: its exact squared-modulus period includes the factor f; the p-adic isometry is stronger than the first-order congruence alone; and the valuation of the chosen progression step matches the denominator at every supported prime. Finite-ring bijectivity and CRT then give all requested residue classes.

## Exact-degree conclusion

The full independent highest forms are single monomials, with the release's stated positive powers of 2, 3 and beta. In particular the degree-328 coefficient is

    2^270 3^176 beta^118

at j^118 w^58 v^58 s^4 r^18 c^68 T^4. This is nonzero at the authentic numerical tuple. The centered degree reductions use the exact identity lambda^2-4BDf = U^2-4B or 4A^2U^2-4B, respectively. The remaining norm correction has strictly smaller degree. Thus the numbers are exact whole-polynomial degrees, not generic or sampled degrees.

## Closure and logical boundary

The release is standalone for its six exact numerical polynomials, finite recipe, literal build/check/replay, and the new arithmetic reduction plus identified retained ordinary interfaces. The explicit CLOSURE_MAP points to the relevant local copies, and the source pins authenticate them.

It is not a standalone rederivation of the entire native compiler and K215/refutation calibration from foundational axioms. The retained CALIBRATION_STATUS.md explicitly treats those as imported ordinary mathematical theorems, and some of their older dependencies are referenced rather than recopied transitively. Nor does it contain a newly checked object-language ZFC derivation or an end-to-end Lean/Rocq endpoint. This is an existing disclosed boundary, not a new defect in the cofactor argument. The appropriate claim is the proved arithmetic zero-existence equivalence, composed with the precisely named inherited ordinary calibration.

## Reproduction

From the parent directory containing scalar/ and scalar_audit/:

    python scalar_audit/audit_scalar.py
    python -O scalar_audit/audit_scalar.py
    python scalar_audit/audit_mutations.py
    python -O scalar_audit/audit_mutations.py
    python scalar_audit/replay_release.py

The principal receipts are AUDIT.json, AUDIT_OPTIMIZED.json, ALL_GATE_MUTATIONS.json, ALL_GATE_MUTATIONS_OPTIMIZED.json and CLEAN_REPLAY.json. The two ordinary/optimized audit pairs must be byte-identical.
