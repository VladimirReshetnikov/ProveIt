# Independent ordinary review: eleven-integer powered carrier with selective fusion

Date: 24 October 2026. Reviewer: a separately tasked research agent.

## Verdict and review boundary

The proposed synthesis is mathematically sound, subject to the same explicitly retained ordinary native/compiler/refutation calibration as its two parents. No additional unproved arithmetic assertion is needed. The synthesis is not a pointwise identity with either parent: it preserves existence of an unrestricted integer zero by a new soundness argument and fresh completeness witnesses.

I inspected the complete `ZFC_Diophantine_Coprime_Projection/integer/PROOF.md`, its retained `source/centered11-proof.md` Sections 5--6, and `ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/radicals/PROOF.md`, including the supported-modulus interpolation argument. The claim reviewed here is the unbounded arithmetic transformation. It does not newly audit all transitive native compiler dependencies, assert a proof-assistant endpoint, or certify any literal output circuit or its degree/operation count; those are separate checks.

Keep every common definition of the coprime-fusion eleven-integer source, including its budget, `Dt`, `Dg`, and fixed six-port tuple, but replace

    I = 2*s*r*c^2     by     I = 2*r*c^2,
    S = I*H^5         by     S = s*r*H.

Use `K = X(3c-2X)+2`, `zc=HT+K`,

    Ac = (zc^2+3H^2)(zc^3-19H^3),
    Z = S(n+(2Q-1)V)-Ac,
    u = S^2 Df, b = 4S^2 Da, e = 16S^2 Dt Dg,

and the complete three-root norm `F8(Z;u,b,e)=0`. All eleven coordinates remain unrestricted integers. The positive-/natural-domain frontiers cannot be substituted into this comparison.

## 1. Essential correction to the bootstrap order

The old proof obtained `c!=0` directly from `I!=0`. That argument cannot be copied: the new scale `S=s*r*H` may be nonzero when `c=0`. The following case split closes the issue without circularity.

The unconditional affine front supplies `H!=0`, `Delta>1`, `Df>=1`, and `Dt>=1`. The factor

    Ac = H^5 pi(T+K/H), pi(x)=(x^2+3)(x^3-19)

never vanishes over rational inputs. If `S=0`, every scaled radicand is zero and the polynomial is `Ac^8!=0`. Thus `s,r!=0` at every zero.

Now prove `Da>0` before assuming `c!=0`:

* If `c=0`, then `I=Q=0`, `delta=Cy=-1`, and `Da=1` exactly. (The value of `V=-R` is immaterial.)
* If `c!=0`, then `|I|>=2c^2`, `Q>1`, and `Df>|c|+1`. Write `V=Df*b0-c`, where `b0=c-R+4IT` is integral. If `b0=0`, `|V|=|c|>=1`; otherwise `|V|>=Df-|c|>1`. Hence `Cy=QV^2-1>0` and `Da=(Q-1)Cy>0`.

Consequently `Df` and `Da` are positive in both cases. In a vanishing conjugate norm factor, `Dt*Dg` is the only possibly negative radicand. If `Dg<0`, its nonzero imaginary contribution cannot cancel the two real contributions or the real center. Also `Dg=1 mod4`, so it is not zero. Therefore `Dg>0`.

Since `Dg=1+4(3Budget-4)Dt*s^2` and `s!=0`, the integer inequality `Budget<=1` would imply `Dg<=-3`. Thus `Budget>=2`. If `c=0`, then `eta=-Yk` and

    Budget = k^2 [q^2(1-4Y^2)-Derr] <= 0,

contradiction. We have now proved `c!=0`, and only now conclude `I!=0`, `Q>1`, and invoke the ordinary strong and auxiliary Pell classification.

## 2. Radical extraction and coprime fusion survive unchanged

`I` is even; hence `Df` and `Da` are odd (indeed `1 mod4`). `Dt` and `Dg` are odd too. Dividing a vanishing factor by nonzero `S` gives a rational signed sum of

    sqrt(Df), 2sqrt(Da), 4sqrt(Dt Dg).

For each odd positive radicand, its square part has odd root. Within any irrational squareclass, the nonzero integer coefficients of the roots have distinct 2-adic orders among 0,1,2. Their sum cannot vanish, since the unique term with least 2-adic order cannot cancel. Independence of distinct squarefree radicals therefore makes every root rational, and hence integral. This argument permits coincident squareclasses and does not assume the radicands pairwise coprime.

Only the last fusion uses coprimality:

    gcd(Dt,Dg)=gcd(Dt,1+4(3Budget-4)Dt*s^2)=1.

Thus `Dt=tau^2` and `Dg=g^2` separately. The recovered `Da` square gives a rational `y=sqrt(Da)/(Q-1)` satisfying

    Q V^2-(Q-1)y^2=1.

For completeness, the adjacent-coefficient integrality lemma has a direct descent proof. Suppose `Q>1`, `V` integral, and `y` rational satisfy this identity. Take absolute values. If `V>1`, then

    V<y<QV/(Q-1).

The norm-preserving transformation

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

has `|V'|<V`. Writing `y=a/b` in lowest terms gives `b^2|(Q-1)`; therefore `V'` is integral, and `y'` has the same reduced denominator because `2Q-1=1 mod b`. The transformed norm excludes `V'=0`. Descent ends at `|V|=1`, where `|y|=1`. Hence `b=1`. This validates the inherited descent at the actual parameters and makes the unbounded integrality step explicit.

After descent, all normalized roots are integers. The vanishing factor gives `S|Ac`, independent of the sign of `S` or the center shear.

## 3. The sign change in the projector is harmless

The powered-carrier parent writes `Kred=X(2X-3c)-2`, whereas the eleven-variable parent uses `K=X(3c-2X)+2=-Kred`. The exact identity needed here is

    K = H X c - 2 Kquad,
    Kquad = X(X+2ac)-1.

Because `H|S`, `S|Ac` implies `H|K^5`. As `H` is odd, this yields `H|Kquad^5`. This does not assert the generally invalid inference `H|K` from `H|K^5`.

The pre-projection signed folding/rank argument of the centered-budget source applies: it needs `c^2|I`, `|I|>=|c|`, the three recovered norms, the two residues `V=-c mod f` and `V=-R mod c`, and the centered budget strip. It does not require `s|I`. In particular its conclusion `p=R=2r0+1`, `r0>=24`, and the ratio bound is used before either main-projector conclusion. The final orientation paragraphs of the old proof must not be inherited prematurely.

Set `x=|X|` and `sigma=sign(c)`. The unchanged signed projection congruence gives

    2^R Kquad = Pi mod H,
    Pi=(sigma X-2^R)(2^R sigma X+1).

Thus `H|Pi^5`. The authentic tuple supplies `x>=2^64`; the pre-projection ratio supplies

    |H| > x(x-3)^r0 > x^(r0+1)/2^r0.

Each factor of `Pi` is strictly smaller in absolute value than `2^(R+1)x`, so

    |Pi|^5 < 2^(20r0+20)x^10 < |H|.

The second strict inequality follows from `x^(r0-9)>=2^(64(r0-9))` and

    64(r0-9)-(21r0+20)=43r0-596>=436.

Hence `Pi=0`; its odd second factor is nonzero, and `sigma X=2^R`. This recovers exactly the old main projection and licenses the unchanged orientation, half-binomial recovery, and fresh old-source witness restoration. No nonunit has been cancelled modulo composite `H`.

## 4. Completeness and the supported-modulus theorem

Begin with the canonical outer tuple from an actual finite refutation. Its budget is positive with the inherited strict margin. Also `Dt=tau^2` and `Dt=1 mod3`. Since `(3Budget-4)Dt` is positive and `2 mod3`, it is a nonsquare. An ordinary positive Pell solution, squared once, provides positive `s,g` with

    g^2=1+4(3Budget-4)Dt*s^2.

Choose the strong pair by the retained finite-matrix-period construction, with positive even index and

    4s c^2 | I, f^2-Delta I^2=1.

Keep this one pair fixed, and define `r=I/(2c^2)`. It is a positive integer divisible by `2s`, exactly realizes `I=2rc^2`, and every prime dividing `M=sr` divides `I`. Although `M` need not divide `I`, this is precisely the hypothesis of the supported-modulus interpolation theorem. One cannot replace that theorem by the old all-residues-modulo-`I` statement.

I independently checked the arithmetic of the strengthening. With strong index `m0`, its period is `lambda=4m0 f`, not merely `4m0`. Let `d=lcm(lambda,4I)`. For every prime `p|I`, the inherited valuation inequality `v_p(m0)<=v_p(I)` and `gcd(f,I)=1` give `v_p(d)=v_p(4I)`. Starting from the already supplied odd auxiliary index `nu0=3 mod4`, define `nu(h)=nu0+dh`. Each corresponding `T(h)` is integral. For any `p|I`, the Pell addition formula and the explicit fourth-step unit give

    v_p(T(h1)-T(h2))=v_p(h1-h2).

For odd primes, the second-coordinate lifting valuation is `v_p(psi_rho(4k))=v_p(rho)+v_p(k)`; for 2 it is `v_2(rho)+2+v_2(k)`. The first-coordinate difference has strictly larger valuation. Dividing by `4I f^2` yields the asserted isometry, including at 2. Consequently `h -> T(h)` is a permutation modulo every prime power supported on `I`, and CRT attains every residue modulo `M=sr`, while the strong pair stays fixed.

The canonical projection already gives `H|K`; write `kappa=K/H`. Intersectivity of `pi` gives a class `a mod M` satisfying `pi(a+kappa)=0 mod M`. Apply the supported-modulus theorem to choose `T=a mod M` and an integer `y` with the auxiliary equation. Then

    Ac/S = H^4 pi(T+kappa)/(sr)

is an integer. Finally choose the unrestricted integer

    n=Ac/S+f+2(Q-1)y+4tau*g-(2Q-1)V.

One norm factor vanishes. The witness order is canonical outer tuple, guard `s,g`, fixed strong `I,f,r`, intersective residue, `T,y`, and `n`. No strong witness changes after the residue is requested. All signs and every formerly nonzero exceptional case have been covered.

## 5. Consequence and remaining literal checks

The synthesized polynomial has an integer zero iff the same calibrated source has a finite syntactic ZFC refutation. Composing the retained ordinary native/compiler/refutation proof gives the desired ZFC-formalizable equivalence between absence of integer zeros and `Con(ZFC)`.

The new literal circuit should be checked independently for the exact replacements `I=2rc^2`, `S=srH`, unchanged projector sign, unchanged center shear, all six fixed constants, and the three-root norm. Its exact degree requires cancellation-aware reasoning; the previous 688-degree certificate must not merely be copied. This review certifies the arithmetic proof of the transformation, not an as-yet-unread circuit or numerical metric.

## 6. Additional accepted change: a smaller index modulus

The subsequent proposal replaces `k=R+1+hXY` by `k=R+1+4h q^4`. This is also sound and complete; it does not require any earlier positivity assumption on `h` or `k-R-1`.

Let `M=4q^4>0`. The unchanged packing bounds give `R<q^4-2`, so `M>3R+1`. With `W=12w+4`, `X=qW`, and `Y=(2v+1)q^3`,

    2XY^2 = 2W(2v+1)^2 q^7

is divisible by `M`, since `4|W`. The signed first Pell parameter `P0=|2XY^2+1|` therefore satisfies `P0=sign(X) mod M`. The first norm gives `|k|=2psi_P0(n0)` with positive `n0`, while recovered main folding and the centered strip give `|c|=psi_B0(p)`, `p>n0`. The elementary recurrence modulo `M` yields

    epsilon*2n0 = R+1 mod M,
    epsilon=sign(k)*sign(X)^(n0-1).

If `epsilon=1`, then `2n0>=R+1`. If `epsilon=-1`, then `2n0>=M-R-1>2R`. The remaining pre-projection rank argument uses only these lower bounds, the recovered strong/auxiliary norms, their actual residues, and `c^2|I`. It supplies `p=R`. Thus `n0<R` excludes the negative branch. In the positive branch, both `2n0` and `R+1` are strictly between zero and `M`; hence `2n0=R+1` exactly.

At this point, and not earlier, use the same first recurrence modulo `|XY|`. We still have `P0=sign(X) mod |XY|`, and the already identified positive sign gives

    k = R+1 mod |XY|.

Thus the integer `h_old=(k-R-1)/(XY)` restores the old literal index coordinate while every other arithmetic value stays fixed. The sign of `XY` is harmless. This permits the unchanged downstream source restoration and calibration. The earlier inequality `|XY|>3R+1` remains true from the affine front, but its old congruence is not assumed before this recovery.

For completeness retain the canonical positive first-Pell tuple, with `n0=(R+1)/2` and positive `X,k`. Its recurrence modulo `M` directly gives `M|(k-R-1)`. Define the new unrestricted coordinate `h=(k-R-1)/M`; all other values and every guard remain unchanged. No witness-dependent variable is introduced into the modulus, and no source coefficient is changed.

Inspection of the inherited centered and signed rank proofs confirms that `h` is used only through the definition of `k`. Their congruence argument never uses `k>=R+1` as an independent premise: the original `h` was unrestricted as well. Consequently the modulus replacement composes with the powered-carrier/selective-fusion theorem above.

## Final register sharing in the short-index norm graph

The delivered centered short-index norm graph shares the register `4*q^2` between the index modulus `4q^4=(4*q^2)*q^2` and the centered budget. This is an identical-polynomial change and does not alter any arithmetic argument in this review. I independently counted the final graph ancestors: 126 live binary gates (80 multiplications, 24 additions, 22 subtractions), 152 live nodes in total, and no dead nodes. This supersedes the earlier127-gate count. The separately certified exact degree remains440; the register sharing makes no change to that polynomial or its leading form.
