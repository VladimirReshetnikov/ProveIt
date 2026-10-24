# Independent skeptical audit of the round-15 eleven-integer scalar equation

## Verdict and scope

**PASS for the new arithmetic reduction and the literal integral equations identified below.** No unresolved new semantic gap was found. The selected paired-norm equations have eleven unrestricted integer variables and the authentic coherent six-coefficient tuple:

- `../norm/integral_centered_paired.json`: exact degree **464**, **119** live binary arithmetic operations.
- `../norm/integral_direct_paired.json`: exact degree **488**, **118** live binary arithmetic operations.

The complete graph hashes, counts, identities, degree witnesses, and negative controls are in `AUDIT_RESULTS.json`; an independent `python -O` run is retained separately. The proof reviewed is `../scalar/PROOF.md`. The audit independently read the selective-coprime parent, the centered eleven-integer argument, the signed quadratic/folding argument, the round-14 powered saturation/interpolation proof, and the explicitly retained calibration-status statement. It did not import any executable producer module.

This verdict is an ordinary mathematical audit of the new source-zero equivalence. The final consistency interpretation composes it with the named inherited ordinary native/compiler/refutation theorems. Those theorems are not replaced by bounded tests, and this audit does not newly reconstruct every earlier machine/compiler theorem, compile their proof-assistant sources, or produce an encoded internal-ZFC derivation. If the imported calibration is treated as an obligation rather than an accepted referenced theorem, the consistency interpretation remains conditional on that obligation. No claim of consistency, inconsistency, global minimality, or historical priority is certified.

## 1. Freeze the actual candidate, not an obsolete proposal

The initial discussion mentioned an even multiplier and parity separation. Those are not the selected equations. The audited candidate uses

    I = r c^2,                 S = s r H,
    D = 3 Budget - 4,         Dg = 1 + D Dt s^2,
    Pg = Dt Dg,
    K = X(3c - 2X) + 2,
    Ac = ((HT+K)^2 + 3H^2)((HT+K)^3 - 19H^3),
    Df = 1 + Delta I^2,       Q = Delta^2 I^2,
    delta = Q - 1,
    V = Df(c - R + 4IT) - c,
    Da = (Q-1)(QV^2-1).

The normalized radical weights are **3, 1, 9**, on `Df, Da, Pg`, respectively. The centered expression is `Z=S(n+QV)-Ac`, not `S(n+(2Q-1)V)-Ac`. The three-radical polynomial is

    F8(Z;u,b,e)
      = [(Z^2-u-b-e)^2-4(ub+ue+be)]^2 - 64ubeZ^2,

with `u=9S^2 Df`, `b=S^2 Da`, `e=81S^2 Pg`. The cheaper paired evaluator is exactly the same polynomial:

    [(Z^2+u-b-e)^2-4(uZ^2+be)]^2 - 64(uZ^2)(be).

No conclusion about evenness of I, oddness of Dg, or the older normalization is imported. The direct equation changes only the integral shear in n. This shear is a bijection of unrestricted integers with the other ten variables fixed.

The final literal schedule additionally uses D81=243Budget-324, Dg81=81+D81 Dt s^2, P81=Dt Dg81 and e=S^2 P81. The independently checked identity P81=81Pg proves this is polynomial-identical, saving one multiplication without changing any semantic premise.

## 2. Nonzero and sign bootstrap, in logical order

The immutable tuple gives `beta=2^1064921-1`, beta odd and 1 modulo 3. Since `J=6j+1`, q is even, 2 modulo 3, and `|q|>=beta-1`. The affine W cannot vanish; consequently `|X|>=4|q|`, while `|Y|>=|q|^3`. Thus `H=4(X+1)Y+3` is odd and nonzero, `Delta=(a+2)^2-1>1`, and `Dt=1+ell(ell+1)k^2>=1` for integer ell=XY^2. These statements hold for both signs of q, X and Y.

The carrier has no rational zero because `(x^2+3)(x^3-19)` has none. Therefore `Ac=H^5 pi(T+K/H)` never vanishes. At `S=0` the entire norm is `Ac^8`, so every zero has **s and r nonzero**. This alone says nothing about c. The proof correctly delays that inference.

After r is known nonzero, split the c cases before using the auxiliary Pell equation:

- If c=0, then I=Q=0 and Da=(-1)(-1)=1.
- If c is nonzero, `|I|>=c^2`, `Df>|c|+1`, and Q>1. For the integer `b0=c-R+4IT`, either b0=0 and `|V|=|c|>=1`, or `|V|>=Df-|c|>1`. Hence Da>0.

Thus Df and Da are positive in both cases, and Dt is positive unconditionally. If Dg were negative, its fused radical would be the sole nonzero imaginary term in a vanishing conjugate factor. Since S is nonzero, this is impossible. Therefore Dg is initially nonnegative. Budget<=0 would give D<=-4 and Dg<=-3. Hence Budget>0.

**The zero-guard edge case was explicitly checked and repaired during review.** Merely saying Budget>0 would not by itself imply D>0 for arbitrary integers. Here q and both cone coefficients are even, so q^2 and Derr are divisible by 4, hence **Budget is divisible by 4**. Budget>0 therefore implies Budget>=4, D>=8 and **Dg>0**. An alternative independent exclusion is that Dg=0 would force D=-1, Dt=1 and s^2=1; Dt=1 forces k=0 because ell is neither 0 nor -1, contradicting Budget=1. The released proof uses the simpler authentic parity argument.

Budget>0 now implies k nonzero, Derr<q^2 and `|eta/k|<1/2`. If c=0 then eta=-Yk and

    Budget = k^2(q^2-Derr-4q^2Y^2) <= 0,

a contradiction. Only now are c, I nonzero and Q>1 established. The strict disk bounds give the common sign of q,F,C,q-F-C. The centered strip gives

    |k|(|Y|-1/2) < |c| < |k|(|Y|+1/2),
    sign(c)=sign(kY).

No early inference eta>0 or k-eta>0 is permitted or used.

## 3. Extraction and selective fusion

Modulo 3, X=-1 and therefore a=H=Delta=0. Moreover ell=XY^2 is 0 or -1 modulo 3, giving Dt=1 modulo 3. It follows that

    Df=Dt=Da=1 modulo 3.

The normalized radical coefficients have squared 3-adic orders 2, 0 and `4+v3(Pg)`. In any common nontrivial squareclass, the coefficients of the associated irrational root have distinct 3-adic valuations. The unique least one cannot cancel in a signed sum. Different squareclasses are linearly independent over Q. Consequently a rational signed sum of these three positive radicals forces each radical rational, hence integral. This argument allows any parity of I and any 3-adic order of Pg. It does not claim rationality just from rationality of an arbitrary radical sum.

The extracted Pg square splits because the factors are strictly positive and

    gcd(Dt,Dg)=gcd(Dt,1+D Dt s^2)=1.

Unique prime factorization yields separate integer roots tau and g. Without the positivity or coprimality premises this inference would be invalid; both have already been proved.

The Da root gives rational `y=sqrt(Da)/delta` and the adjacent-coefficient equation `QV^2-(Q-1)y^2=1`. Q>1 was established first. If y=A/B is reduced, B^2 divides Q-1. The norm-preserving integral matrix

    (V,y) -> ((2Q-1)V-2(Q-1)y, (2Q-1)y-2QV)

preserves the pair's least common denominator and keeps the first coordinate integral. After sign reflections, for V>1 the inequalities `V<y<QV/(Q-1)` imply a strict reduction in |V|. V'=0 is impossible for Q>1. At |V|=1, |y|=1. Thus B=1. This confirms the denominator descent rather than assuming an integer auxiliary root.

The vanishing conjugate factor is now an integer identity and gives S|Ac, hence H|K^5. No claim H|K follows just from this divisibility.

## 4. Pre-projection rank interface

The needed source interface is the **pre-projection** portion of the signed centered proof, not its already-oriented conclusion. Its actual inputs have all been supplied: cubic Y, common strict packing signs, the centered absolute strip, the first and strong norms, c^2|I, and the two residues

    V=-c modulo |f|,
    V=-R modulo |c|.

The second follows from the exact identity `V+R=Delta I^2(c-R)+4I Df T`. No factor s in I and no odd multiplier are needed.

Before applying the rank argument, absolute folding really recovers the missing main norm. Put B0=|a+2|, C0=|c| and I0=|I|. The strong pair is `(|f|,I0)=(chi_B0(m0),psi_B0(m0))`, with `|f|>2I0`. The auxiliary index is odd, since its abscissa is divisible by rho=Delta I0 while every even-index abscissa is +/-1 modulo rho. Its odd quotient identity gives `psi_B0(nu)=+/-C0 mod |f|`. Fold modulo 2m0 into `0<=p<=m0`; because `psi_B0(p)+C0<=2I0<|f|`, the congruence cannot wrap, so C0=psi_B0(p)>0.

The nonodd strong-rank step is valid. Strong divisibility gives p|m0; writing m0=pv, composition gives `I0=C0 psi_D(v)` with D=chi_B0(p). Since `psi_D(v)=vD^(v-1) mod C0` and gcd(D,C0)=1, C0|v, hence C0|m0. The subsequent signed step-down and no-wrap bounds yield p=R before any main projection. The centered first-norm bounds then give

    R=2r0+1, r0>=24,
    |Y|>(|X|-3)^r0/2-1.

These steps do not use eta positivity. From the last estimate,

    |H|>=4(x-1)|Y|-3 > x(x-3)^r0,  x=|X|,

because `(x-2)(x-3)^r0>4x-1` holds throughout the established range. This is the exact margin needed for powered saturation.

## 5. Fifth-power saturation and late restoration

The current K has the opposite sign from the round-14 reduced K. The proof correctly uses the corresponding identity

    2Kquad = HcX - K,     Kquad=X(X+2ac)-1.

Together with odd H and H|K^5 this gives H|Kquad^5. The actual signed Pell congruence is `2^R Kquad=Pi mod H`, where

    Pi=(sigma X-2^R)(2^R sigma X+1), sigma=sign(c).

Taking fifth powers gives H|Pi^5. This is an exact congruence, not a use of a theorem that already assumed the projection. No nonunit is improperly cancelled.

The authentic base gives x>=2^64. The independently checked estimates are

    |Pi|^5 < 2^(20r0+20)x^10,
    |H| > x^(r0+1)/2^r0,
    64(r0-9)-(21r0+20)=43r0-596>=436.

Hence |Pi|^5<|H| and Pi=0. Its odd second factor cannot vanish; therefore sigma X=2^R. The signed main root and the exact congruence H|(d-X-ac) follow. Only now do the retained centered orientation and uniform half-binomial theorem recover X,c,k,Y positive and `0<eta/k<1/4`. Fresh odd strong/auxiliary witnesses are then regenerated as in the explicit centered source. This is the proper restoration of an actual old signed Q41 witness, not a claim that the incoming r is already odd.

## 6. Supported-modulus interpolation and completeness

This audit independently checked the stronger interpolation proof, especially its 2-adic case. The strong pair is chosen once with `4s c^2|I`, then held fixed. Its genuine squared-modulus period is `lambda=4m0 f`, not merely 4m0. For `d0=lcm(lambda,4I)` and every p|I,

    v_p(d0)=v_p(4I),

because gcd(f,I)=1 and v_p(m0)<=v_p(I). A single existing interpolation solution nu0 is advanced by d0 h, preserving both required congruences and giving integral T(h).

For a nonzero increment D0 divisible by 4, the Pell addition formula has a second summand of valuation exactly v_p(D0), because psi_rho(nu) and rho^2-1 are units and

    v_p(psi_rho(D0)/rho)=v_p(D0).

The first summand has strictly greater valuation. The first-coordinate valuation is `2(v_p(rho)+v_p(D0))` at odd primes, and one less at p=2. The base identities at index 4, odd-prime binomial lifting, and 2-adic doubling establish these claims. At p=3 with the smallest possible valuation the last binomial term has valuation 3>2, so there is no exceptional tie. At p=2, the even-index chi remains odd and chi+1 has valuation 1. Dividing the difference by 4If^2 yields

    v_p(T(h1)-T(h2))=v_p(h1-h2).

Therefore h->T(h) is a well-defined injection and hence bijection on each residue ring supported on I. CRT supplies arbitrary T residues modulo **any** such modulus, not just divisors of I. The result is unbounded; finite prime-power examples are not its proof.

Canonical completeness fixes the outer variables first. The canonical centered budget is strictly positive, Dt is a square and is 1 modulo 3, so D Dt is positive and 2 modulo 3, hence nonsquare. Ordinary Pell existence supplies s,g with Dg=g^2. Then choose one strong pair with 4s c^2|I and put r=I/c^2. For M=sr, all prime factors divide I, although M need not divide I. This is exactly within the proved interpolation scope.

The canonical main projection gives H|K; write kappa=K/H. The intersective quintic has a root modulo M, including the explicitly checked primes 2,3,19. Choose that residue only **after** I,f,r and M are fixed. Supported interpolation then supplies T in the chosen residue without changing the pair. Thus Ac/S is integral. Finally choose

    n=Ac/S+3f+delta*y+9tau*g-QV

for the centered equation, omitting -QV for the direct equation. One conjugate factor vanishes. This witness order is noncircular and matches the frozen formula.

## 7. Exact arithmetic-artifact audit

`independent_audit.py` independently verifies all leaf types, the exact eleven-variable set, the six fixed ports, topological order, complete backward liveness, output identity, and all published operation metadata. Every source register and every norm register is checked against a separately transcribed symbolic polynomial using already verified cuts. The full three-root sign product has all **35** coefficients checked, not just selected evaluations. Both paired and centered rewrites are exact universal polynomial identities.

The six payloads are decompressed and checked against independently transcribed authentic SHA-256 pins, bit lengths, minimal little-endian lengths, beta/cone recipes, and the shifted-MF convention. A toy beta or a changed port cannot inherit the calibration or this audit.

For degree, the expanded centered graph has a syntactic upper bound of 464 and is identically tied to the paired 119-operation graph. Independently, exact univariate evaluation with every variable=t and the **actual** coefficients reduced modulo 1,000,003 yields degree 464 with leading coefficient 338332. This is a rigorous nonzero specialization certificate for the lower bound, not an extrapolation from random evaluations. The direct graph has upper bound 488 and nonzero degree-488 coefficient 587871 under the same specialization. The symbolic leading-form derivation was also independently checked, including the attained coefficient

    [j^260 w^56 v^64 C^4 h^12 s^12 r^24 c^32] P
       = 2^460 3^326 beta^260 > 0.

Six deliberately altered graphs are rejected after recomputing their superficial operation/degree metadata: wrong final norm sign, wrong I factor, wrong K sign, wrong guard sign, wrong 3-adic weight, and wrong QV product. Their rejection reasons are mathematical-register failures, not merely stale counts. Normal and optimized Python runs pass identically; no check relies on Python assertions.

## 8. Remaining boundary and release requirements

The new scalar proof passes the above checks. Its consistency-language conclusion should retain the explicit ordinary-calibration qualification and the inherited `CALIBRATION_STATUS.md` distinction. Do not describe this as a new kernel-checked native/compiler certificate or an internal object-ZFC derivation. The complete coefficient tuple must remain fixed and coherent. Do not replace the current ternary separation by the abandoned parity proposal, omit the Budget mod 4 step, claim M|I in completeness, or infer H|K from H|K^5 without the growth argument.

The audit applies to graph and proof hashes recorded with this artifact. If any mathematical definition, payload, output graph or proof dependency changes, rerun the checks and review the changed semantic obligation before reusing the verdict.
