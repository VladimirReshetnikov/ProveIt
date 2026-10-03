# An auxiliary quotient gives a complete universal polynomial in 85 operations

The [complete source](complete85_auxiliary_bezout_projection.py) and [receipt](complete85_auxiliary_bezout_projection.json) replace two auxiliary coordinates of the normalized [transport-shear86 source](complete86_transport_quotient_shear.md) by one positive quotient. The complete polynomial costs **85=48M+37A**, has **18 positive witnesses**, and has **exact degree175** on every admissible fixed-program slice. The ordinary positive input and the entire fixed-program numeral recipe are preserved. The comparison-system bound remains74.

There is a bijection of the full supplied positive integer zero sets. Its proof establishes integrality, positivity, and the remaining index sign before invoking the parent universal theorem. Off zeros, the polynomials obey the explicit correction below; they are not asserted to be equal. This packet changes the normalized86 source only. It makes no transfer claim for the ordinary-strong87 source.

## 1. Actual source and paid change

Use the parent's literal registers and meanings:

    q=(B−1)J+1, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    A=a+2, Delta=A²−1=a²+4a+3,
    D=X+ac+(rho+sigma)(4a+3),
    R=r_lhs, K=index_difference=k−hE,
    Ns=f²−Delta*i²*c⁴,
    Kaux=Delta²*i²*c⁴.

In the code `A` denotes Delta, while this note uses A for its Pell parameter a+2. All these quantities are computed and paid. The old auxiliary argument and coupled linear factor are

    V=of−c,
    Na=Kaux*(V²−y²)+y²,
    Nlinear=V−jc+K.

The old index factor is `Nk=K−R`. The other factors are the first, main and input norms and the transport factor. Supply one positive coordinate **T**, named `auxiliary_quotient`, in place of positive o and j. Define

    Vnew=c*(T*f−1)−R*f².                              (1)

The five literal new instructions are

    auxiliary_Tf           = T*f
    auxiliary_Tf_minus_one = auxiliary_Tf−1
    auxiliary_c_Tf         = c*auxiliary_Tf_minus_one
    auxiliary_R_f2         = R*f²
    aux_u_rhs              = auxiliary_c_Tf−auxiliary_R_f2.

The f-square is the existing paid `L16`, still needed by the strong norm. The old `of` and `aux_u_rhs` cost two gates. The deleted `jc`, `linear_difference`, `norm_linear`, and last multiplication by that factor cost another four. Their only supplied-coordinate consumers are checked literally. Thus five new gates replace six old ones; the final subtraction of1 now uses `seven_units`. The first/main/input/auxiliary/index/transport/strong factor product remains fully paid. All85 gates and all retained supplied coordinates are live. There is no free division or exponentiation in the child circuit.

The new five-gate block has3M+2A; the deleted block has3M+3A. Every other old instruction remains literal, apart from the final output operand. There are79 unchanged old gates, five new gates, and the updated final subtraction. The complete costs are therefore85=48M+37A, with18 witnesses rather than19.

## 2. Exact off-zero correction and the candidate maps

For an arbitrary signed child tuple, define polynomial restored coordinates

    o=cT−Rf,
    j=Tf−R*Delta*i²*c³−1.                             (2)

All other supplied coordinates are unchanged. The first identity is unconditional:

    of−c=c(Tf−1)−Rf²=Vnew.

The restored linear factor is

    Vnew−jc+K = Nk+R*(1−Ns).                          (3)

The other seven factors are identical under (2). Consequently the complete polynomials satisfy the exact all-value identity

    Fparent(restored)+1
      =(Fchild+1)*(Nk+R*(1−Ns)).                      (4)

The helper expands the local coefficient identities and checks all seven complete factor expressions plus both full finalizers. Equation(4), rather than same-polynomial equality, is the off-zero statement. The restoration is polynomial over the integers, but it is not positive on the whole positive orthant.

The forward map on parent positive zeros will be

    T=(o+Rf)/c.                                       (5)

Its integrality is proved below. The quotient in(5) belongs to the mathematical map; the emitted child evaluates(1) with a supplied positive T and pays no division.

## 3. Positivity before any rank or compiler theorem

At a positive child zero, the seven integer factors have product1 and hence are units. The first norm is+1 by the same consecutive-product negative-Pell descent as the [first-root parent](complete86_factored_first_root.md). The main, input, and normalized strong norms cannot be−1 modulo4, because Delta is0 or3 modulo4. The auxiliary factor cannot be−1 either, because Kaux is an integer square and hence0 or1 modulo4. Therefore all five norm factors are+1. Write the remaining index and transport signs as epsilon and nu, each in `{−1,1}`.

The current transport factor is `(Kconstant+w)C+(q−F)−t(q−1)`. Positive F,t imply

    (q−F)−t(q−1)=1−F−(t−1)(q−1)≤0.

Its coefficient of C is at least2. Either unit sign therefore forces C≥0. Since `C=q−F−Z−alpha−2dx`, all supplied slacks are positive and F+Z<q. The actual fixed compiler mask bounds then give

    (2q−1)(q²−1)<R<q⁴−q³,
    3q+1<R−2<R+2<q⁴.                                (6)

These are the existing pretyping packing inequalities, using the paid shifted MF convention, not arbitrary mask numerals. In the current asymmetric source

    E=wsq⁴≥q⁴>R+2,
    a=E+Y≥q⁴+q³>R+2.                                (7)

No dyadic conclusion about q has been assumed.

The strong norm gives

    f²=1+Delta*i²*c⁴.

In particular c>2 and f>c²>2c, without any rank theorem. Moreover R<a<Delta, so

    Kaux−(Rf²+c)
      =(Delta−R)f²−Delta−c
      ≥f²−Delta−c
      =1+Delta*(i²*c⁴−1)−c >0.                       (8)

To prove Vnew>0, use only the auxiliary equation

    Kaux*Vnew²−(Kaux−1)*y²=1.

It excludes Vnew=0. Put v=|Vnew|. If v>1 then

    v²−1=(Kaux−1)(y²−v²)>0.

As y is positive, y≥v+1. Hence `v²−1≥(Kaux−1)(2v+1)`, which forces

    v≥2Kaux−1.                                       (9)

Indeed for `1<v≤2Kaux−2`, the difference between the two sides is
`v*(v−2Kaux+2)−Kaux<0`. This elementary gap needs no Pell classification.

Because T>0, (1) gives `Vnew>−Rf²−c`. Combining(8) and(9) excludes every negative Vnew with |Vnew|>1. The two cases Vnew=±1 are excluded by

    Vnew=−c modulo f,

since c>2 and f>2c make neither c−1 nor c+1 a nonzero multiple of f. Thus **Vnew>0**.

The restored o in(2) is an integer and `of=Vnew+c>0`, so o>0. At Ns=1, (3) also gives

    jc=Vnew+R>0,

so the restored integer j is positive. This establishes both missing positive coordinates before a native rank argument, and without assuming that the restored parent polynomial vanishes.

## 4. The index sign is positive before invoking the parent theorem

At a child zero, the restored linear factor in(3) equals epsilon, the index sign. Set lambda=epsilon. The local rank and ratio argument from [coupled88 Sections3–4](complete75_coupled_index_linear88.md#3-outer-positivity-and-the-displaced-auxiliary-target) can now be applied with these individual unit equations. Its later product-sign/compiler argument is not being assumed. Here are the necessary steps with the actual weaker asymmetric bound(7).

Put `P=2XY²+1`. The positive first norm classifies its root and k as

    tau=chi_P(n), k=2psi_P(n), n≥1.

Since P≡1 modulo E and `k=R+epsilon+hE`,

    2n=R+epsilon modulo E.

As `0<R+epsilon<E`, it follows that `n≥(R−1)/2≥24`. The main root D is unconditionally positive. Its norm gives `D=chi_A(p)`, `c=psi_A(p)` with p≥1. Since P>A and c>k, monotonicity gives p>n. Thus

    c>A*Delta², c>2p, c>2R.                          (10)

The last bound follows already from h≥1, E>R+2, k=R+epsilon+hE and c>kY. The first follows from p≥25 and the usual lower bound `(2A−1)^(p−1)`.

For the [generic strong-rank lemma](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md), use the positive ordinary coefficient `i*=Delta*i`. The normalized strong equation then gives

    (i*c²*Delta)²=Delta*(f²−1),
    f=chi_A(m), c divides m, m≥c>2p.

This is exactly the ordinary strong premise, obtained by multiplication; no discarded divisibility condition is needed. The auxiliary argument is now positive and obeys

    Vnew=of−c=jc−R.

The signed auxiliary step-down proof from [reversed auxiliary89](complete75_reversed_auxiliary89.md), together with(10), identifies its target as

    p=R.                                             (11)

Equivalently, the general coupled target is `R+epsilon−lambda=R`. Its hypotheses use the individual unit equations and the restored positive o,j, not the full parent product being1.

Write `2n=R+epsilon+vE`. The least positive residue gives v≥0. If v≥1, then E>R+2 implies2n>2R, contradicting n<p=R. Thus

    2n=R+epsilon.

If epsilon=−1, then p=2n+1. Let `Q=chi_A(2)=2A²−1`; one has Q>P and A>Y+1. Pell duplication and monotonicity give

    psi_A(2n)=2A*psi_Q(n)≥2A*psi_P(n)=A*k,
    c=psi_A(2n+1)>A*k>k(Y+1).

This contradicts the unchanged strict ratio `kY<c<k(Y+1)`. Hence **epsilon=lambda=1**. The remaining transport factor is then1 because the child product is1.

Now, and only now, equation(4) proves that(2) is a full positive zero of the exact selected normalized transport-shear86 parent. Its unchanged universal ordinary-input theorem applies. This argument uses E>R+2; it does not import the older symmetric claim E>2R.

## 5. Completeness and the full zero-set bijection

At a parent positive zero, its already proved unit recovery gives Ns=Nk=Nlinear=1. In particular

    of+R=c(j+1), f²≡1 modulo c.

Multiplying the first congruence by f proves `c|(o+Rf)`. Thus(5) is a positive integer. Substituting it in(1) recovers the old V exactly. All seven child factors coincide with the parent factors, and the omitted factor is1, so this produces a child zero at the same ordinary input and every other retained coordinate.

Conversely Section3–4 restores a positive parent zero from every child positive zero. Formula(5) recovers T from(2) identically. Starting with a parent zero, the restored o is its original o; and `jc=V+R`, c>0 uniquely restores its original j. Therefore these maps are inverse on the **full supplied positive zero sets**, not merely on canonical Pell witnesses or at a refreshed height. The proof is conditional on the same valid fixed-program numeral recipe as the parent.

## 6. Uniform exact degree175

Fixed compiler numerals have degree zero. Put

    Q=(B−1)J, k0=eta+zeta, gamma0=rho+sigma,
    C1=Q−F−Z−alpha−2dx,
    Ttransport=w*C1−transport_quotient*Q.

The six other retained factors inherit their parent exact degrees and leading forms. In(1), c has degree5 with leader `k0*s*Q³`, while R has degree4. Therefore the unique degree7 part of Vnew is

    c_top*T*f.

Its square raises the auxiliary degree from56 to60 and multiplies its old leader by `(T*f)²`. The deleted linear factor had degree7 and leading form `−h*w*s*Q⁴`. The new complete factor degrees are

    22,18,32,60,7,2,34,

which sum to175. The full leading homogeneous form is

    +32 Q^103 h gamma0 delta² i⁴ k0^13 w^16 s^29
        *Ttransport*T²*f².                          (12)

It is a nonzero polynomial on every admissible fixed-program slice: B−1>0, and Ttransport has the nonzero coefficient `−(B−1)` at `transport_quotient*J`. Thus175 is uniform exact degree, not merely a sampled or syntactic bound. The final subtraction of1 cannot affect it.

The naive gate degree upper bound is185 because it does not cancel the main and input norm leaders. Two complete dense univariate coefficient expansions in the receipt attain175 and the specialization of(12); they supplement the uniform proof.

## 7. Executable scope and replay

The standalone standard-library helper authenticates the parent trio and the pinned proof notes before every canonical public entry; it imports no ancestor Python or historical suite. The saved packet contains all85 instructions, every supplied port, all18 witness names, the fixed-numeral ports, the complete finalizer and the exact-versus-syntactic degree distinction. It checks the two removed supplied coordinates' complete consumer sets, all79 unchanged old instructions, seven complete factor expressions, the local polynomial restoration and the full correction(4). It additionally checks32 whole signed/rational corrections, including8 rational cases. These are algebra fixtures, not complete halting witnesses.

The small public surface is `canonical_parent(root)`, `build(root=...)`, `checked(packet,root=...)`, `evaluate(packet,values,root=...,signed=False)`, `integer_restore(packet,values,root=...)`, `restore_zero(packet,values,root=...)` and `project_parent_zero(values,root=...)`. Packet comparisons and value types are exact, including rejection of Boolean integers. Every call authenticates current bytes. Returned dictionaries are independent. Existing wrong-pin files are rejected rather than bypassed by a fallback. Warmed pin mutations, malformed packet/assignment rejection, and returned-copy isolation are tested.

`integer_restore` returns the signed polynomial map(2), and does not claim positivity off zeros. The two zero-map APIs require a full positive zero and check the resulting full zero. Evaluators accept integer fixed-numeral values for arithmetic; they do not certify that arbitrary numeral values implement a valid program. The universal theorem and positive-zero bijection retain the inherited valid compiler recipe. No full astronomical Pell zero is materialized.

Run from any working directory:

    python3 complete85_auxiliary_bezout_projection.py --root /absolute/path/native-stream-queue --expect /absolute/path/complete85_auxiliary_bezout_projection.json

`--output` writes the deterministic receipt. Exact typed replay and optimized-Python rejection are enforced. The writer and fresh exact typed receipt replay from `/` passed. All12 parent/proof pins were checked again, including the immediate parent’s exact first-root provenance. Optimized execution was separately confirmed to reject before verification. The source, receipt and this note are frozen for independent review.
