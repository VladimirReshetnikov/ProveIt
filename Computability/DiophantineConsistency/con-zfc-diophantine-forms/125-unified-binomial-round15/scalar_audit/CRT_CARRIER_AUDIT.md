# Independent audit of the bounded weak-Y split-carrier extension

## Status and boundary

The **new arithmetic reduction and its literal graphs pass** independent review. The exact centered metric is **416 / 125 operations**, and the direct companion is **456 / 124 operations**, both with eleven unrestricted integer variables. The baseline degree-464/119-operation and degree-488/118-operation equations remain separately approved and unchanged. The exact graph verdicts and hashes are recorded in `CRT_AUDIT_RESULTS.json` and `CRT_AUDIT_RESULTS_OPTIMIZED.json`. Normal and optimized runs agree.

This extension inherits the same ordinary native/compiler/refutation calibration, with exactly the restrictions stated in `SEMANTIC_AUDIT.md`. It is not a new kernel proof or an encoded object-ZFC certificate. The present review addresses one bounded additional construction, not an open-ended optimality search.

## Exact changes

Replace the baseline cubic Y by `Y=qv`. Leave the native transport F,R, the definitions based on X,Y, the centered Budget, the strong and auxiliary Pell data, and the three-adic radical weights unchanged. Define

    M=2q^2, Dcar=HM,
    zc=HM T + M K + H(v-q^2),
    Ac=(zc^2+3Dcar^2)(zc^3-19Dcar^3),
    S=srH M^5.

The short K is still `X(3c-2X)+2`. The centered coordinate is `Z=S(n+QV)-Ac`; the direct one is Sn-Ac. The normalized radicands remain Df,Da,Pg with weights 3,1,9. The weighted-guard implementation is only a polynomial-identical schedule, not a new semantic premise.

## 1. Unconditional input checks, including v=0

The immutable affine restrictions still give q even, q=2 modulo 3, q nonzero and huge, X=2 modulo 3, and |X|>=4|q|. Y=qv may now vanish, so **the old large-Y bootstrap cannot be imported**.

Nevertheless `a=(X+1)qv` is either zero or has huge absolute value. If a=0, then H=3 and Delta=3. If a is nonzero, the established lower bounds on X,q give |a|>4, so H=4a+3 remains nonzero and Delta=(a+2)^2-1>1. In both cases H is odd, and H=3 modulo q. Since gcd(q,3)=1,

    gcd(H,q)=1, gcd(H,2q^2)=1.

Thus M is strictly positive, Dcar is nonzero, and H is a unit modulo M, even when v=0 or any other input is negative. No sign assumption on H enters these gcd statements.

The carrier equals `Dcar^5 pi(zc/Dcar)`, with pi(x)=(x^2+3)(x^3-19) having no rational zero. Hence Ac never vanishes. At S=0 all scaled radicands vanish and the norm is Ac^8. Therefore r,s are nonzero at every zero.

## 2. Extract integral roots before attempting auxiliary descent

If c=0, then I=0 and Da=1. If c is nonzero, r is already nonzero and |I|>=c^2. Since Delta>1, `Df>|c|+1`, and the same integer b0 case split as in the baseline proves |V|>=1 and Da>0. Df>0 and Dt>=1 hold in both cases.

A negative Dg would give the sole imaginary term in a vanishing norm factor. Thus Dg>=0, implying Budget>0 as before. q and the cone coefficients are even, so Budget is divisible by 4. Hence Budget>=4, D>=8 and Dg>0. This step is valid even with Y=0. **Budget>0 does not yet exclude c=0 in this weak-scale setting.**

For every v, X=-1 modulo 3, so a=H=Delta=0 modulo 3. Since Y^2 is 0 or 1 modulo 3, ell=XY^2 is 0 or -1 modulo 3, and Dt=1 modulo 3. Consequently Df=Da=Dt=1 modulo 3. Three-adic separation works exactly as before and gives integral roots of Df, Da and Pg. Positivity plus gcd(Dt,Dg)=1 splits Pg into separate squares.

At this point the Da root is integral even if I=0. There is no need to divide by delta or invoke Pell descent yet. The vanishing factor, with integer center and integer roots, already gives

    S | Ac.

This is the essential repair of the bootstrap ordering.

## 3. Decode the cubic scale through the M^5 carrier

Since M^5 divides S, it divides Ac. The homogeneous carrier is

    Phi_D(z)=z^5+3D^2z^3-19D^3z^2-57D^5,

with M|Dcar. Fix any prime p with p^e exactly dividing M. If b=v_p(zc)<e, the leading term zc^5 has valuation 5b, while every other displayed term has strictly greater valuation: at least 2e+3b, 3e+2b, or 5e. Extra valuations in the integer coefficients only increase those bounds. This contradicts p^(5e)|Ac. Therefore p^e|zc for every p|M, so

    M | zc.

Modulo M, zc=H(v-q^2). The already established gcd(H,M)=1 implies M|(v-q^2), i.e.

    v=q^2(2v_old+1), v_old=(v-q^2)/(2q^2) in Z.

Therefore Y=qv=(2v_old+1)q^3 is exactly the old cubic scale. This works for negative q and negative v; no positivity or odd-multiplier assumption was used. It also excludes the previously dangerous v=0 branch because v=0 cannot satisfy this congruence.

Only now does Budget>0 exclude c=0: if c=0, eta=-Yk and the restored |Y|>=1 would force Budget<=0. Hence c,I are nonzero and Q>1. Adjacent-coefficient descent is now justified and gives an integer auxiliary y.

## 4. Recover powered projection independently of the M decoding

Since H|S and S|Ac, H|Ac. Reducing the homogeneous carrier modulo H gives H|zc^5; reducing zc modulo H gives zc=MK. Thus

    H | M^5 K^5.

Because gcd(H,M)=1, M^5 is a unit modulo H and can be cancelled, yielding H|K^5. This cancellation is justified for every composite or negative H; it is not an invalid cancellation of a nonunit.

After replacing the original v coordinate by the decoded integer v_old, every source quantity q,X,Y,F,R,k,eta,Budget,Dt,I,Df,Q,V agrees with the baseline arithmetic interface. The preceding signed folding, nonodd strong-rank argument, ratio estimate, and fifth-power saturation therefore apply verbatim. Their hypotheses are supplied only after the restored cubic scale and c nonvanishing have been established. Late orientation and fresh odd-kernel regeneration produce the same old signed source witness.

## 5. Completeness and fixed witness order

Given a canonical old outer witness, set the new v to `q^2(2v_old+1)`, preserving Y and all dependent guards. Choose the guard Pell pair, then one strong pair with 4s c^2|I and r=I/c^2, exactly as in the baseline. Put N=sr for the supported interpolation modulus; this N is distinct from the carrier modulus M=2q^2.

The canonical projection gives H|K, and the encoded v gives M|(v-q^2). Consequently

    kappa=K/H+(v-q^2)/M in Z,
    zc=HM(T+kappa),
    Ac=(HM)^5 pi(T+kappa),
    Ac/S=H^4 pi(T+kappa)/(sr).

The shift kappa depends only on already fixed outer data, not on the later T residue. Every prime of N divides I. Choose an intersective root of pi(T+kappa) modulo N, then apply the proved supported-modulus interpolation theorem with the **same fixed I,f,r**. This makes Ac/S integral without changing any earlier witness. Finally choose n from the vanishing conjugate factor, subtracting QV for the centered equation.

The witness order is noncircular. The scalar denominator sr, not M, is the remaining completeness modulus; no unsupported assertion about prime factors of q in I is needed.

## 6. Independent degree expectations

With weak Y, the exact relevant prefix degrees are

    Y:2, a:4, H:4, Delta:8, I:3,
    Df:14, Q:22, V:19, Da:82,
    Budget:16, Dt:22, Dg:40, Pg:62,
    M:2, Dcar:6, zc:7, Ac:35, S:16.

The scaled radicand degrees are u:46, b:114, e:94. For the centered coordinate, Z has degree 57; B0=Sn-Ac has degree 35. In

    Z^2-b=B0^2+2SQVB0+S^2[Q(V^2+1)-1],

the last two terms can both have degree 92, but an upper bound of 92 suffices. Then the paired norm's first register has degree 94 from -e, and the inner register has unique top term -4be of degree 208. The final correction has degree at most 368. Thus the centered degree is 416 with nonzero top form 16 b_top^2 e_top^2. The direct equation has degree 456 with top form b_top^4. These symbolic expectations must be bound to the actual literal graphs by the independent artifact check; operation counts must be read from live graphs, not estimated.

## Review conclusion

No new semantic gap was found. In particular the tempting order “Budget>0 implies c!=0, then descent, then carrier decoding” is invalid at the weak scale and is not the reviewed proof. The valid order is integral radical extraction, S|Ac, M^5 decoding, restored cubic Y, c!=0, adjacent descent, then signed ranks and saturation. The extension is acceptable only with that order and the unchanged ordinary-calibration qualification.

## Literal-graph and proof-text closure

The complete `../scalar/CRT_CARRIER_PROOF.md` was independently read after it was written, including its leading-form tie `k_top=R_top+h a_top`. Every new source register and complete norm cut in both literal graphs passed independent symbolic checks. The upper-degree proof propagates through the entire DAG after applying the proved source-centering identity at the precise norm cut. The authentic finite-field lower witnesses are degree 416 with leading coefficient 809968, and degree 456 with leading coefficient 576411, modulo 1,000,003 with every variable=t. These are exact nonzero specialization certificates combined with universal upper bounds, not random degree estimates.

The printed attained coefficients were independently derived as well: the centered h^12,C^4 branch has coefficient 2^388 3^278 beta^212; the direct C^8 branch has coefficient 2^400 3^280 beta^216. The tie in k_top is harmless because only its h a_top term can contribute h^12. Six generic norm/source mutations and the additional split-carrier controls are rejected. Full graph/source hashes are included in `REVIEW_BINDINGS.json`.
