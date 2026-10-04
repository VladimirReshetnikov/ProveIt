# Polynomial exterior absorption has only finitely many nondegenerate inputs

Fix any one valid inherited compiler-numeral slice of the complete84 source, with ordinary input x>0. Let E be its 64 computed registers independent of the four auxiliary witnesses `i,f,auxiliary_quotient,y_aux`, together with all fourteen other supplied witnesses, the ordinary input x and the six fixed numeral ports. Thus E contains 85 named values; its members need not be algebraically independent.

For any fixed integer polynomial G in these named values, consider the literal substitution i=G(E) in the complete84 polynomial, retaining all its other expressions and positive witness domains. Write t=deg G and L=max(1,sum of the absolute integer coefficients of G), after combining like monomials in its chosen 85 formal arguments. Define the computable integer

    C_G=4t+2+ceil(log_2 L).

For G=0 identically the nonzero sector is empty and t may be taken as zero. Every positive substituted zero with G(E) nonzero satisfies

    c<=C_G,             2d*x+b<R<c<=C_G.                 (1)

Consequently that sector has finite ordinary-input projection. In particular, any such chart whose positive zeros all have G(E) nonzero cannot preserve an infinite input language. The coefficients of G may depend on the fixed compiler, but not on the varying input or witnesses. This theorem allows every finite polynomial computation in the specified exterior values; it is not restricted to one-wire aliases or to a gate budget.

If G(E)=0, the exact remaining condition is instead

    G(E)=0, f=1, y_aux=1, P5=1,                         (2)

where P5 is the product of the retained first, main, input, index and transport factors. The positive auxiliary quotient is then unrestricted. No finite-language assertion is made for (2). Thus any unbounded-input behavior of this substituted source must lie entirely in this explicitly identified degenerate sector.

No new circuit, operation saving, lower bound for arbitrary circuits, or resolution of independent-gamma83 is asserted. Replacing a coefficient root by a free witness is outside this theorem: it removes precisely the divisibility that the argument retains.

## 1. Actual source and inherited hypotheses

The source is the unchanged complete84 scaled-strong packet, with84=47M+37A operations, eighteen positive witnesses and degree187. Its literal meanings are

    q=(B-1)Jrep+1, X=w*q, Y=s*q^3, E0=X*Y,
    k=eta+zeta, c=kY+eta, a=Y(X+1), A0=a+2,
    Delta=A0^2-1, H=4a+3, gamma=rho+sigma,
    D=X+a*c+gamma*H,
    C=q-F-Z-alpha-2d*x, W=C-Z, u=2d*x+b,
    kappa=u+delta*Delta, mu=W+a*kappa+rho*H.

The source register `A` is Delta; it is not the mathematical Pell parameter A0. The source `r_lhs` is the computed index R. The source `auxiliary_quotient` is denoted T, distinct from `transport_quotient`. The recipe exports `MF` already shifted by B-1.

At every full positive84 zero, its proved scaling identity P84=Delta*P85 first cancels the positive Delta. The normalized85 proof then establishes the unit signs, auxiliary positivity and rank, without presuming a compiled history. The native theorem subsequently gives

    q>=B>=16, X=2^R, Y>=q^3,
    3q+1<=R, R+2<q^4<=E0<a,
    c=psi_A0(R), D=chi_A0(R),
    norm_first=norm_main=norm_input=norm_aux
      =norm_index=norm_transport=1, norm_strong=Delta.

Here psi and chi are defined by

    (A0+sqrt(A0^2-1))^n=chi_A0(n)+psi_A0(n)*sqrt(A0^2-1).

The actual retained gamma=rho+sigma is greater than rho. The input-quotient dichotomy therefore forces the canonical input Pell index v=u, not an arbitrarily selected input completion. Hence

    0<rho<gamma<c, sigma<gamma<c,
    W=2^u>0, 3<=u<R,
    kappa=psi_A0(u)<c, mu=chi_A0(u)<D,
    delta=(kappa-u)/Delta<c.

These are consequences of every positive parent zero. No canonical auxiliary choice is assumed: the strong index below ranges over every permitted positive completion.

The exact proof dependencies are: current84 Sections1–3 for its positive scaling equivalence; normalized85 mathematical review Sections2–6 for the packing inequalities, unit signs, auxiliary positivity and rank; the input-quotient dichotomy Sections2–5 for the native quantities and canonical input forced by rho<gamma; and the computed-gamma census Sections2–3 for its independently stated actual packing/transport bounds. Their byte hashes are pinned below and in the helper. This is a use of those full-zero theorems, not an assumption that a small diagnostic host is a compiled history.

## 2. The strong coefficient outgrows every fixed exterior polynomial

The retained normalized strong equation is

    f^2-Delta*(i*c^2)^2=1.

Its positive solutions give an index m with f=chi_A0(m) and psi_A0(m)=i*c^2. Strong divisibility first gives R|m. Write m=Rj. Expanding the Pell unit at R gives

    psi_A0(Rj)/c = j*D^(j-1) modulo c.

The left side is divisible by c and gcd(D,c)=1, so c|j. Thus Rc|m. This divisibility is inherited explicitly from the normalized85 proof; it is not claimed as a new discovery.

For A0>=2, chi_A0(n)>psi_A0(n)>0 when n>0. The addition formula therefore yields, for every integer j>=2,

    psi_A0(jR)>c^j.

Indeed psi_A0(2R)=2D*c>c^2, and each succeeding addition of R multiplies the preceding coefficient by D>c and adds a positive term. Since c is a positive integer greater than two,

    i=psi_A0(m)/c^2 >= psi_A0(Rc)/c^2 > c^(c-2).       (3)

This estimate applies to all auxiliary completions of each full positive zero. It is stronger than the earlier direct-gamma obstruction's consequence i>c, which used only m>=3R.

## 3. Every exterior value is below c^4

All bounds here concern full positive parent zeros, after Section1. Since R>=3 and Pell coefficients increase,

    c>=psi_A0(3)=4A0^2-1,
    a^2<c/4, Delta<c, H<c, q<X<a<c.

In fact R is much larger than three, but this weaker estimate suffices. Also k<c, E0<a, Y<a, and U=XY^2<a^2<c/4.

The source's exact auxiliary-free register census is partitioned below. The accompanying receipt verifies this partition against dependency propagation from the four auxiliary ports; the group names are merely proof labels.

| Group | Literal computed registers | Bounds |
|---|---|---|
| Unit values | `norm_first,norm_main,norm_pair,norm_input,norm_triple,norm_index,norm_transport` | All equal1. |
| First/root ratio | `tau_square,R10b,ksn2,first_root_base,first_next,first_product,R10a,hpm1` | k<c, kY<c, c=R10a; first_root_base=kU<c^2/4; first_next=k(U+1)<c^2/2; first_product<c^4/8; tau_square=first_product+1<c^4; hpm1=k-R-1<c. |
| Main root | `cam2,D1,gamma_sum,a4,a4m5,gam,R14,L15,a_square,A,c2,Ac2` | a,Delta,H<c; D<A0*c<c^2; 0<D1<D; gam<D; gamma<c; c2=c^2; Ac2=Delta*c^2<c^3; L15=D^2<c^4. |
| Input root | `index_product,index_rhs,difference_multiple,exponent_partial,modulus_multiple,exponent_rhs,mu2,kappa2,scaled_kappa2` | kappa<c, mu<D<c^2; W>0 and rho>0 bound both positive root summands by mu. index_product=kappa-u<c; scaled_kappa2=mu^2-1<c^4; all listed values are therefore below c^4. |
| Remaining exterior | `repunit,q,Lbig,n2,wn2,sn2,UM,R12,q_minus_F,q_minus_FZ,C_after_alpha,scaled_t,marked_rhs,W,odd_index,index_difference,gap_product,gap,Lm1,rproduct,qMF,mask_factor,mask,r_lhs,kinner,innerC,transport_partial,local_rhs` | The explicit packing and transport bounds below put each at most a, with R12=a; the intermediate bounds below q^2 or3q^3 are also below a. |

For the last group, repunit<q; q^3<=Y<a; X<a; E0<a. The original slack makes F,Z,alpha,2dx,C and W smaller than q. The same bound gives C_after_alpha=C+2dx<q. The intended u is less than R<a. The index difference is R+1<a.

The packing gap is q(q-F)-Z, positive and less than q^2; its product with q^2-1 is less than q^4<a. Each positive summand used to make the gap is less than q^2. Modified75 compiler Section1, equations(2)–(3), gives 0<MF_native<B-1 and MF_source=MF_native+B-1, and hence the true source mask convention gives

    0<MC<B-1, 0<MF_source<2(B-1),
    q*MF_source<2q^2,
    MC+q*MF_source<3q^2,
    (MC+q*MF_source)*Jrep<3q^3<a.

These mask inequalities use the modified75 export, not the unshifted historical MF range. The original DC,DR range is78 Section2, equation(8). Complete76 Section1, steps2–4, places the optional extra monomial at exponent g and enlarges L past g+Emax; its coefficient and all other raw coefficients stay below the strengthened inner radix. Modified75 Section1 strengthens that bound again and keeps the same separated layout. Thus 0<DC,DR<B remains true after the correction. Therefore Kconstant=DC+B*DR<B^2<=q^2. With w=X/q and C<q,

    kinner=Kconstant+w<q^2+X<a,
    innerC=(Kconstant+w)C<q^3+X<a,
    transport_partial<q^3+X+q<a,
    local_rhs=transport_partial-1<a.

The inequalities on the right use Y>=q^3, X>=q and q>=16. No temporal-alignment or small-quotient assumption is inserted here.

The fourteen exterior supplied witnesses are exactly

    Jrep,F,alpha,transport_quotient,h,s,w,tau_root,
    eta,zeta,Z,delta,rho,sigma.

Jrep,F,alpha,Z<q; eta,zeta<k<c; h*E0=k-R-1 gives h<c; s<Y and w<X; tau_root^2=tau_square<c^4; delta,rho,sigma<c by canonical input recovery. The positive transport quotient satisfies t*(q-1)=local_rhs<a, hence t<a. Thus all fourteen are below c^4.

The six fixed ports are `Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF`. Respectively these are B-1, DC+B*DR, 2d, b, MC and MF_source. Complete76 Section1 defines d=bL with positive integer L; modified75 Section1 retains it. Thus b<=d. Also B=2^d>=16, so d>=4 and 2d<B<=q. The other bounds were just proved; in particular the shifted MF is below2q<c. Finally 2d*x<q gives x<q<c. This covers every exterior supplied value and fixed coefficient, rather than only the internal registers.

## 4. Effective finite-input bound and the signed substitution

Let z be the vector of the 85 exterior values. At every positive parent zero, each |z_j|<c^4. Every monomial of total degree at most t therefore has absolute value at most c^(4t), and

    |G(z)|<=L*c^(4t).

If i=G(z)>0, combine this with(3). More generally the literal source depends on i only through the square of `aux_coefficient_root=i*Ac2`. Thus P84 is even in i. Every positive substituted zero with G(z) nonzero maps to a positive parent zero by setting i=|G(z)|, keeping every other supplied coordinate unchanged. The exterior expressions are independent of i, so their values do not change under this map. This proves the same inequality without a global positivity assumption on G.

If c>=4t+3+ceil(log_2 L), then

    c^(c-2-4t)>=2^(1+ceil(log_2 L))>L,

contradicting(3). Therefore c<=C_G. The parent input inequalities u=2dx+b<R<c give(1). For example the conservative finite search domain 1<=x<C_G suffices; the sharper literal bound 2dx+b<C_G is also available. The logarithmic ceiling is computable by integer bit length, without real-number approximation.

This argument permits repeated or algebraically dependent exterior arguments and program-dependent fixed coefficients of G. It does not treat an exponent depending on x or witnesses as a fixed polynomial. A finite family of such polynomial substitutions likewise has only finitely many nonzero-sector inputs on a fixed compiler slice.

## 5. The exact zero-value boundary

Before imposing any native equation the actual auxiliary cut is

    S=Delta*i*c^2, Q=S^2,
    V=c*(T*f-1)-R*f^2,
    Na=Q*(V^2-y_aux^2)+y_aux^2,
    Ns_scaled=Delta*f^2-Q,
    P84=P5*Na*Ns_scaled-Delta.

At i=0 this becomes the all-ring identity

    P84|_(i=0)=Delta*(P5*f^2*y_aux^2-1).               (4)

Delta>0 already follows from the exterior positive supplied domain. At a positive substituted zero with G(z)=0, the integer product P5*f^2*y_aux^2 is one. Since f,y_aux are positive integers, f=y_aux=1 and P5=1. Conversely these values and G(z)=0 make the literal full polynomial zero for every positive T. This proves exactly(2), not merely a necessary subsystem condition.

No native rank or input decoding is inferred in this degenerate sector. Its G=0 condition is an additional polynomial condition on the actual exterior fields; it must be analyzed separately before claiming either a collapse or a useful representation. Positivity or nonvanishing restrictions needed by a proposed chart must be justified or paid, rather than supplied by this theorem for free.

## 6. Ancestry and intended next step

The normalized85 rank proof already supplies Rc|m. The direct supplied-gamma obstruction already deduces i>c. The 72 computed-gamma census concerns a different edit, replacing gamma=rho+sigma, and does not prove the quantified exterior-polynomial absorption theorem here. The auxiliary-product83 collapse deletes the condition f|U and admits all inputs while allowing i to grow freely. The free-coefficient83 chart deletes the c^2 divisibility itself. Neither lies in this theorem's retained-parent substitution class.

The new result is the exponential-versus-polynomial obstruction, its full 85-value actual-source boundary, an explicit coefficient/degree threshold, and the exact degenerate sector. It directs further source work toward an auxiliary-dependent coordinate, a changed constraint with a genuinely new zero-set proof, or a separate analysis of G=0. It supplies no saving and no minimum for the complete84 circuit. The closed independent ten-gate auxiliary theorem is not used or restated as a global bound.

## 7. Fresh evidence, pins and scope

The new standalone standard-library helper reads all predecessors only as authenticated text or JSON. It authenticates the complete84 packet, visits every one of its84 literal rows, verifies31 explicit source-boundary rows, and computes the auxiliary dependency cone. Its exact exterior partition has7 unit,8 first/root-ratio,12 main-root,9 input-root and28 remaining exterior registers. The complete unchanged parent array is included as inert evidence; no new candidate circuit is emitted.

Two complementary symbolic checks are saved. A17-term independent factor expansion proves evenness and the zero-i contraction. Separately, the checker interprets all84 actual rows three times, with i,-i,0, cutting only values already proved auxiliary-independent. It leaves the actual norm_pair and norm_triple products expanded, processes the entire finalizer, and verifies the same whole-source identities, including the two-term zero-i output. This authenticates(4) through the actual dependency graph rather than only through a handwritten factor formula.

Ten small exact Pell components check square divisibility and the strict power bound,360 components check the rank-quotient congruence and its divisibility equivalence, and234 coefficient-norm/degree examples check the stated threshold. These are fresh arithmetic diagnostics, not compiler histories or complete polynomial zeros. They neither prove all exterior inequalities by sampling nor materialize the enormous native witnesses. Sections1–5 supply the quantified arguments.

The twelve dependency pins are:

| File, relative to the native-stream-queue directory | SHA-256 |
|---|---|
| complete84_scaled_strong_output.py | `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737` |
| complete84_scaled_strong_output.json | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| complete84_scaled_strong_output.md | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |
| review_complete85_auxiliary_bezout_math.md | `77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d` |
| complete83_input_quotient_dichotomy.md | `46d6457d10d1847cd4241aa1ed6705bf520216fc32cf97891c1f439f6c2c2505` |
| complete83_computed_gamma_obstruction.md | `02b55f39ea585c76563897fcb0040f75d4257c410ffc3c27d5f3686822632d04` |
| complete75_half_binomial_compiler.md | `68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117` |
| complete83_direct_gamma_witness_obstruction.md | `c1f7a146ba85020ea1ed436e64de9a9163f9c5c7ac8d013d46d719ccef92d3f4` |
| complete83_auxiliary_product_collapse.md | `a224d930f94a3888b4208147dc54d90127999342313120a5239e40408e948d50` |
| complete83_free_coefficient_scout.md | `867e277a2ca09af392e81cf7e54f6eaa7677a939ea3717448cd89053b5690b31` |
| ../../1980/FIXED_RAW_UNIVERSAL_78_PROOF.md | `b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39` |
| ../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md | `75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87` |

The fresh helper SHA-256 is `46e42d8947c1e5cbed62a4473fa83d96115a80b334656ea45ad1f31796bde0a9`; its receipt SHA-256 is `ec0b2a298d4382867ca0d638e3b52b18be3ad38a64ea7c4efb96d1ad985d692b`. The receipt includes its own source binding, dependency hashes, unchanged full source, exact census, coefficient identities and component records.

Fresh normal and optimized exact receipt replays from working directory `/` both pass. No predecessor program or builder was executed or imported, and no repository or frozen predecessor was edited. The CLI rejects duplicate keys and noninteger numeric JSON fields; explicit checks remain active under optimized Python. Generation uses exclusive creation, and replay compares canonical, type-distinguishing JSON encodings.

```sh
absorption_wip=/absolute/path/to/native-stream-queue
python3 "$absorption_wip/complete84_exterior_auxiliary_absorption.py" \
  --root "$absorption_wip" --expect "$absorption_wip/complete84_exterior_auxiliary_absorption.json"
python3 -O "$absorption_wip/complete84_exterior_auxiliary_absorption.py" \
  --root "$absorption_wip" --expect "$absorption_wip/complete84_exterior_auxiliary_absorption.json"
```

Use mutually exclusive `--output PATH` to generate a new receipt. This is a bounded source/proof artifact, not a general compiler API or an implementation of arbitrary polynomial substitutions G.
