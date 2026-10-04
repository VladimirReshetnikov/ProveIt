# Affine coupling confines the noncanonical input branch of independent-gamma83

Fix one inherited valid compiler-numeral slice of the unchanged independent-gamma83 source. Let **E** be the 71 literal values listed in Section 2: all 52 computed registers and all 19 free ports independent of `delta,rho,i,f,auxiliary_quotient,y_aux`. In particular E includes the ordinary input, all six fixed numerals, and the independent positive main quotient `sigma=gamma`.

Choose fixed integer polynomials `P(E),Q(E),S(E)`. Their coefficients may depend on this fixed compiler, but not on its varying input or witnesses. Set

    t=max(deg P,deg Q,deg S,0),
    L=max(1,||P||_1,||Q||_1,||S||_1),
    K=8t+4+ceil(log_2(23L^2)).                            (1)

Here coefficient norms are taken after combining like monomials in the 71 named formal arguments; these arguments need not be algebraically independent. A zero polynomial contributes degree zero for this convention.

At every full positive integer zero of the actual83 polynomial satisfying

    P(E)*delta+Q(E)*rho=S(E),
    (P(E),Q(E)) != (0,0),                               (2)

either its input Pell index is the canonical index `v=u=2d*x+b`, in which case the positive parent84 inverse exists at the same ordinary input, or

    R^2<K,
    2d*x+b<R<=floor(sqrt(K-1)).                          (3)

Thus the **noncanonical** zeros in the nondegenerate sector of (2) have an explicitly bounded finite ordinary-input projection. This is not a finite-language assertion for the canonical sector. Moreover, if `K<=2401=49^2`, every zero in this nondegenerate sector is canonical, because the native range gives `R>=3q+1>=49`.

If `P(E)=Q(E)=0`, relation (2) can hold only when `S(E)=0`, and then it supplies no constraint. No bound is claimed for that degenerate sector. In particular, a formal nonzero polynomial P can vanish on the actual dependent exterior values; formal nonzeroness alone does not discharge the nondegeneracy condition.

This is a new obstruction to **joint affine coupling of the two large input witnesses**. Cancellation between their positive values is allowed. It does not add a free equation to the83 source, construct a new circuit, prove that such a relation preserves all accepted inputs, control the alias period, or settle the ordinary-input language. Any proposed source transformation must establish or pay for its additional relation and retain the hypotheses used here.

## 1. Inherited full-zero facts, without canonical input recovery

The circuit remains83=47M+36A, with eighteen strictly positive witnesses, ordinary positive input x, six fixed valid compiler numeral ports, and exact degree187. Its sole change from complete84 is deletion of `gamma_sum=rho+sigma`, using the supplied positive `sigma` as the independent main quotient gamma. The all-ring identity is

    P83(gamma)=P84(sigma_parent=gamma-rho).                (4)

The inverse in (4) is not presumed positive. On every full positive83 zero, the native bootstrap and quotient dichotomy, Sections 2–5 of the pinned `complete83_input_quotient_dichotomy.md`, already prove

    q>=B=2^d>=16, X=wq=2^R, Y=sq^3,
    k=eta+zeta, c=kY+eta=psi_A0(R), a=Y(X+1),
    A0=a+2>2^R, Delta=A0^2-1, H=4a+3,
    D=chi_A0(R), 3q+1<=R, R+2<q^4<=XY<a,
    C=q-F-Z-alpha-2d*x>=0, |W|=|C-Z|<q,
    3<=u=2d*x+b<2q<R<A0,
    0<gamma<c.

The source register `A` is Delta, not A0. The five unit registers used in the exterior census are exactly one; the input norm is also one. These conclusions use positive gamma to obtain a positive main root, but do not use gamma>rho, positive W, canonical input, or an accepted computation. They follow by cancelling the positive discriminant through the normalized source identity before proving unit signs and rank. No units are inferred directly from an arbitrary product equaling Delta.

The actual input rows give

    kappa=u+Delta*delta=psi_A0(v),
    mu=W+a*kappa+H*rho=chi_A0(v),
    mu^2-Delta*kappa^2=1,                               (5)

with a positive integer index v. The established dichotomy is

    v=u:         0<rho<gamma<c;
    v!=u:        rho>c>gamma, v>=A0*u.

The latter includes both the even progression `v=A0*u+2Delta*j` and the noncanonical odd progression `v=u+2Delta*j`, with the relevant nonnegative integer j. The independent order congruence can exclude some progression members; this proof does not assume every member occurs.

Write

    ell=floor(A0*u/R).

The pinned power-gap proof supplies, for every noncanonical full zero,

    kappa=psi_A0(v)>c^ell.                              (6)

Indeed v>=ell*R, ell>=55, and positive Pell addition gives `psi_A0(jR)>c^j` for j>=2. For the explicit cutoff here we also have

    ell>=R^2  for all R>=7.                             (7)

To verify (7), use A0>=2^R+1 and u>=3. The elementary inequality `3*2^R>=R^3` holds at R=7, and propagates because `(R+1)^3<2R^3` for R>=7. Therefore `3*(2^R+1)/R>R^2`, whose floor is at least R^2. This induction is the all-index proof; finite checks below are only corroboration.

## 2. Exact 71-value boundary and its bounds

Dependency propagation through every literal83 row, excluding the six supplied ports `delta,rho,i,f,auxiliary_quotient,y_aux`, gives the following disjoint 52-register partition:

| Group | Literal computed registers |
|---|---|
| Five units | `norm_first,norm_main,norm_pair,norm_index,norm_transport` |
| Eight first/root values | `tau_square,R10b,ksn2,first_root_base,first_next,first_product,R10a,hpm1` |
| Eleven main values | `cam2,D1,a4,a4m5,gam,R14,L15,a_square,A,c2,Ac2` |
| Twenty-eight outer values | `repunit,q,Lbig,n2,wn2,sn2,UM,R12,q_minus_F,q_minus_FZ,C_after_alpha,scaled_t,marked_rhs,W,odd_index,index_difference,gap_product,gap,Lm1,rproduct,qMF,mask_factor,mask,r_lhs,kinner,innerC,transport_partial,local_rhs` |

The 19 remaining free ports are exactly

    Jrep,F,alpha,transport_quotient,h,s,w,tau_root,
    eta,zeta,Z,sigma,x,
    Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF.

At every full positive83 zero, each of these 71 values satisfies

    |E_j|<c^4.                                         (8)

Here is the bound with the input and auxiliary dependencies removed, rather than an invocation of the positive84 ordinary-input theorem. Since R>=3,

    c>=psi_A0(3)=4A0^2-1,
    a^2<c/4, Delta<c, H<c, q<X<a<c.

Also k<c, XY<a and `U=XY^2<a^2<c/4`. Consequently `first_root_base=kU<c^2/4`, `first_next=k(U+1)<c^2/2`, `first_product<c^4/8`, and `tau_square=first_product+1<c^4`. The first norm is already one. The remaining first/root entries are smaller still. The main root satisfies `D<A0*c<c^2`; its positive summands `D1` and `gam` are less than D, and explicitly `cam2=a*c<D1<D<c^2`. Thus `L15=D^2<c^4`, `c2=c^2`, `Ac2=Delta*c^2<c^3`; the remaining entries `a4=4a,a4m5=H,a_square=a^2,A=Delta` are below c. Independent gamma<c follows from the dichotomy proof before input recovery.

For the outer group, `F,Z,alpha,2dx,C<q`, `|W|<q`, `C_after_alpha=C+2dx<q`, and `u<R<a`. The gap is `q(q-F)-Z`, between zero and q^2; its product with q^2-1 is below q^4<a. Also `index_difference=R+1<a`. The modified75 recipe, Section1, proves the actual shifted-mask bounds

    0<MC<B-1, 0<MF_native<B-1,
    MF_source=MF_native+B-1<2(B-1).

The source MF port is MF_source. Therefore `qMF<2q^2`, `mask_factor<3q^2`, and `mask<3q^3<a`. The other radix powers and `R12=a` are below c, and the computed R is below a.

Complete78 Section2, equation (8), gives `0<DC,DR<B`. Complete76 Section1 places its optional high correction below the enlarged L and bounds every coefficient below the radix. Modified75 strengthens that radix and preserves the separated supports. Thus the same bounds apply to the corrected compiler, giving

    Kconstant=DC+B*DR<B^2<=q^2.

With `w=X/q` and C<q, the actual rows obey

    kinner=Kconstant+w<q^2+X<a,
    innerC=(Kconstant+w)C<q^3+X<a,
    transport_partial<q^3+X+q<a,
    local_rhs=transport_partial-1<a.

These inequalities use Y>=q^3 and X>=q, and do not require temporal alignment or input typing. Every outer entry is therefore at most a except possibly its sign, with `R12=a` explicitly; the only potentially signed listed marker W has absolute value below q.

For the supplied ports, `Jrep,F,alpha,Z<q`; `eta,zeta<k<c`; `h*XY=k-R-1` gives h<c; s<Y and w<X; `tau_root<c^2`; and `sigma=gamma<c`. The positive transport quotient satisfies `transport_quotient*(q-1)=local_rhs<a`, so it too is below a. The ordinary input has `2dx<q`, hence x<q. Finally the six fixed numerals are `B-1,DC+B*DR,2d,b,MC,MF_source`; b<=d and `2d<B<=q`, while the remaining bounds were just established. This covers every free argument, including the fixed compiler constants.

The earlier85-value exterior absorption theorem includes the input-root cone and uses canonical input to bound it. That application would be circular here. We instead remove all of its delta/rho dependencies, delete the absent `gamma_sum`, retain independent gamma<c, and prove (8) from the preceding pre-input facts. The dependency count is 52+19=71, not85.

## 3. An exact line on the input Pell conic

At a zero satisfying (2), abbreviate its three integer coefficient values by

    alpha0=P(E), beta0=Q(E), chi0=S(E).

These names do not denote the supplied outer slack alpha. Define

    p=alpha0*H-a*Delta*beta0,
    q0=Delta*beta0,
    r=alpha0*H*u+beta0*Delta*W+chi0*H*Delta.              (9)

Substitution of the **literal** roots in (5) proves the all-ring identity

    p*kappa+q0*mu-r
       =H*Delta*(alpha0*delta+beta0*rho-chi0).           (10)

Thus the affine relation becomes `p*kappa+q0*mu=r`. Its restriction to the norm-one conic gives the quadratic equation

    (p^2-Delta*q0^2)*kappa^2
      -2*p*r*kappa+(r^2-q0^2)=0.                       (11)

The leading coefficient in (11) is a nonzero integer. If beta0=0 then alpha0!=0, so q0=0 and p=alpha0*H!=0. If beta0!=0 then q0!=0; vanishing would make Delta the rational square `(p/q0)^2`. An integer rational square is an integer square, whereas `(A0-1)^2<Delta=A0^2-1<A0^2`. This proves nonvanishing even when p=0 or some other coefficients vanish.

No asymptotic comparison of delta with rho is used. Signed coefficients and exact cancellation in the line are allowed. In particular the nonzero quadratic leader is what prevents two very large Pell witnesses from cancelling in a low-height affine relation.

## 4. Height bound and finite exceptional inputs

Put `M=L*c^(4t)`. By (8), each of `|alpha0|,|beta0|,|chi0|` is at most M. Also a,Delta,H,u and |W| are all less than c. Formula (9) gives

    |p|<2M*c^2, |q0|<M*c, |r|<3M*c^2.                 (12)

For a nonzero integer quadratic `az^2+bz+d`, every real root has

    |z|<=1+max(|b|,|d|)/|a|<=1+|b|+|d|.

Indeed beyond `1+max(|b|,|d|)/|a|`, the leading term strictly exceeds the sum of the other terms, by the finite geometric bound. Apply this to (11) and use the integer leader's absolute value at least one:

    kappa<=1+2|pr|+|r^2-q0^2|
          <=1+2|p||r|+r^2+q0^2
          <23M^2*c^4
          =23L^2*c^(8t+4).                            (13)

The constant23 is deliberately conservative; (12) gives at most the terms12,9,1 times M^2*c^4, and the remaining1 is absorbed since c>=2 and M>=1.

Suppose now that the zero is noncanonical. Equations (6)–(7) and (13) imply

    c^(R^2-8t-4)<23L^2.                               (14)

If R^2>=K as defined in (1), the left side is at least `2^ceil(log_2(23L^2))>=23L^2`, a contradiction. This proves (3), including its strict endpoint and the integer square-root bound. Integer bit length computes the logarithmic ceiling exactly; no real-number approximation is needed. Because u=2dx+b<R, (3) bounds ordinary inputs on the fixed compiler slice.

If the coefficients alpha0,beta0 vanish simultaneously, the original relation reduces to chi0=0. At such a point the polynomial (11) is identically zero and the root-height argument is unavailable. This is the exact excluded sector, not a technical genericity assumption that can be dropped.

## 5. What this adds and what it leaves open

The earlier witness-power gap bounds delta and rho **individually** away from the canonical range. It does not by itself control a difference such as `P(E)*delta+Q(E)*rho`, because its two large terms might cancel. The nonsquare Pell eliminant above handles that joint cancellation uniformly over all 71 exterior arguments and over both parity branches of the input index. No order or factorization hypothesis on H is used.

For any proposed retained-source chart that proves a nondegenerate relation of the stated kind, all its sufficiently large-input zeros restore the literal positive parent84 at the same input. This is a soundness implication only. It does not supply positive witnesses for accepted inputs or ensure that the proposed chart has any zeros. Imposing the relation may cost operations or destroy completeness. The exact paid cost and all other source changes require their own proofs.

The noncanonical branch itself is still nonempty above each genuine accepted parent input, by the old CRT extension. This result says such a branch cannot also satisfy a fixed nondegenerate bounded-exterior affine coupling at arbitrarily large ordinary inputs. It does not label all noncanonical completions as false inputs, construct a false input, or prove an upper bound for the full alias period. The source remains unchanged, and83 universality remains unresolved.

## 6. Fresh source binding and bounded evidence

The fresh standard-library helper `complete83_affine_input_coupling.py` authenticates thirteen frozen dependency files as inert bytes. It reconstructs the literal83 source from the actual84 array by deleting only `gamma_sum`, checks topology and full liveness, and verifies47M+36A. Dependency propagation audits all83 rows and all25 free ports, giving exactly52 retained computed values,31 excluded computed values,19 retained free ports and six excluded supplied ports. The receipt records the unchanged full packet hash, the complete71 census, and its own helper-byte hash.

All ten literal input-cone rows, including `norm_input`, are expanded independently at the seven exterior/supplied cuts Delta,a,H,u,W,delta,rho. The helper checks (10) and the formal eliminant identity

    Q(kappa)=line^2-2*q0*mu*line
                +q0^2*(mu^2-Delta*kappa^2-1),

where `line=p*kappa+q0*mu-r` and Q is the left side of (11). The source array is not changed, no arbitrary polynomial P,Q,S compiler is implemented, and no new arithmetic circuit is emitted.

Finite corroboration comprises100 comparisons of independently computed Pell pairs,72 integer line/conic checks with both signs and zero individual coefficients,234 threshold comparisons, and250 floor-growth comparisons. The line examples use freely chosen small Pell parameters; **they are not compiler histories or full83 zeros**. They do not certify the unbounded degree, nonsquare, or exterior-growth arguments by sampling. Sections1–4 supply those proofs.

The thirteen pinned dependencies are listed in the helper and receipt. The central pins are:

| File | SHA-256 |
|---|---|
| complete83_independent_gamma_scout.json | `ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20` |
| complete83_independent_gamma_scout.md | `bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41` |
| complete84_scaled_strong_output.json | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| complete83_input_quotient_dichotomy.md | `46d6457d10d1847cd4241aa1ed6705bf520216fc32cf97891c1f439f6c2c2505` |
| complete83_input_witness_power_gap.md | `30a2b5eb4aa5dda7c08df01acd89fca3c4311b91f62e9df1f767341ed670f4f6` |
| complete84_exterior_auxiliary_absorption.md | `69f8e40bd44dca5bcb2f0f292a2ad842fff5a41b2014007f3f986176cd7bd8de` |

The source-bound proof dependencies additionally pin the actual modified75 compiler, complete76/78 numeral bounds, normalized85 unit/rank review and asymmetric kernel review. The present proof imports those stated pre-input/full-zero facts and does not claim a new audit of every older compiler theorem. Its literal71-value census and the elimination/height argument are new.

Fresh generation and ordinary and optimized exact receipt replays from working directory `/` passed. A root proof read checked the quantified line/conic, height and cutoff arguments; independent source-census verification is separate. No repository or frozen file was edited, and no predecessor program was executed or imported.
