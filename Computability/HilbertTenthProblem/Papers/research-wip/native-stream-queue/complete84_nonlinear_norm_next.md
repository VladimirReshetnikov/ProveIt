# Nonlinear two-norm refactorizations and a rational-chart obstruction

No operation saving results. Two bounded conclusions sharpen the next search boundary. First, an exact polynomial re-factorization of the independent main/input norm product into two norms has only the separate affine possibilities or a classical composed norm with a constant companion pair. This permits arbitrary polynomial degrees and does not assume invertibility. Second, a specific nonlinear rational chart built from the actual paid input coordinate preserves the main norm and is positive, but fails integrality at **every** parent positive zero. Clearing its denominator gives a valid larger evaluator, not a saving.

The parent is the actual `complete84_scaled_strong_output.json`: 84=47M+37A, eighteen positive witnesses, ordinary positive input, and six fixed compiler numerals. Its universal theorem and degree187 are inherited. No global arithmetic lower bound, new universal bound, or new witness projection is asserted.

## 1. Prior coverage and actual coordinates

The earlier main/input scout already tested direct quadratic-norm composition and composition after cancelling the shared center. The strong-norm scout tested composition with the strong factor. The joint-root and actual-modulus notes charge the shared `rho*H` producer and retain the auxiliary consumers of `c²` and `Delta*c²`. The new affine rigidity and multiplication-only cross-block theorems have narrower, explicitly declared models. None of their helpers was run or imported here; this note does not repeat those searches.

The saved84 rows15–29 and37–47 give

    a=R12=Y(X+1), H=a4m5=4a+3, Delta=A=(a+1)(a+3),
    c=R10a=kY+eta, k=R10b=eta+zeta,
    u=odd_index=twice_cell_bits*x+inner_bits,
    kappa=index_rhs=u+delta*Delta,
    D=R14=a*c+X+(rho+sigma)*H,
    mu=exponent_rhs=W+a*kappa+rho*H,
    Nm=D²−Delta*c², Ni=mu²−Delta*kappa².

Rows27–28 compute `c2=c²` and `Ac2=Delta*c²`; row74 still needs `Ac2` for `aux_coefficient_root=i*Ac2`. Row45 already computes `kappa2=kappa²`. Thus neither square/coefficient may be declared an unpaid supplied quantity or deleted merely because a norm is rewritten.

For the polynomial theorem, use exactly the independent rational cut established in the affine note:

    K=Q(q,X,Y,k,u,W,F,Z,transport_quotient,f,h,i,
        auxiliary_quotient,tau_root,y_aux).

Fix the valid compiler numerals. The remaining source coordinates `eta,delta,rho,sigma` can be replaced birationally by `D,c,mu,kappa`, with inverse

    eta=c−kY,
    delta=(kappa−u)/Delta,
    rho=(mu−W−a*kappa)/H,
    sigma=(D−X−a*c)/H−rho.

The exterior cut also recovers `J=(q−1)/Bm1`, `w=X/q`, `s=Y/q³`, `x=(u−inner_bits)/twice_cell_bits`, `zeta=k−eta`, and `alpha=q−F−2Z−(u−inner_bits)−W`. These are rational-coordinate proofs of independence, not integer witness substitutions or free source arithmetic. Over K, Delta is nonsquare: its two distinct linear factors in the independent variable Y each have odd multiplicity. The actual relation H=4a+3 is retained.

## 2. Classification beyond the affine ansatz

**Proposition.** Let K have characteristic zero, let Delta be nonsquare in K, and write `N(z,t)=z²−Delta*t²`. Suppose four arbitrary polynomials P,Q,U,V in `K[D,c,mu,kappa]` satisfy

    N(P,Q) N(U,V) = N(D,c) N(mu,kappa).                 (1)

Put L=K(sqrt(Delta)). Up to exchanging the two output pairs and the two input pairs, exactly the following types occur. The scalars alpha,beta belong to `L*`, their field norms satisfy `N(alpha)N(beta)=1`, and epsilon,eta are independent signs.

1. **Separate type:**

       P+sqrt(Delta)Q = alpha*(D+epsilon*sqrt(Delta)c),
       U+sqrt(Delta)V = beta*(mu+eta*sqrt(Delta)kappa).

   Both pairs are homogeneous linear, and each is a separate norm similitude. There is no translation or cross-pair mixing.

2. **Collapsed composition type:**

       P+sqrt(Delta)Q
          = alpha*(D+epsilon*sqrt(Delta)c)
                  *(mu+eta*sqrt(Delta)kappa),
       U+sqrt(Delta)V = beta.

   The nonconstant pair is a homogeneous quadratic composition, followed by a constant norm similitude; the other pair is constant.

The conjugate equations determine the minus forms in both cases. Conversely every displayed choice satisfies (1).

**Proof.** In the polynomial UFD over L, the right side of (1) is the product of four distinct linear prime factors

    l1=D+sqrt(Delta)c, l1bar=D−sqrt(Delta)c,
    l2=mu+sqrt(Delta)kappa, l2bar=mu−sqrt(Delta)kappa.

The four nonzero factors on the left are `P±sqrt(Delta)Q` and `U±sqrt(Delta)V`. Their product is squarefree. Consequently each is a nonzero scalar times a product of a subset of those four primes, and the four subsets are disjoint and exhaust them. The subset for the conjugate of a form is the conjugate subset, because P,Q,U,V have coefficients in K. No subset can contain both members of an old conjugate pair: its conjugate subset would then share those primes, contradicting squarefreeness.

Thus a plus form contains zero, one, or two primes, at most one from each old pair. The conjugate has the same number. If the two output plus forms have respective subset sizes d1,d2, then `2d1+2d2=4`, so their sizes are `(1,1)`, `(2,0)`, or `(0,2)`. In the first case the old conjugate pairs must be allocated separately. In the latter cases the nonconstant form takes one prime from each old pair. Multiplying all scalar units gives the stated reciprocal norm condition. This proves the list, including the absence of hidden lower-degree corrections. The converse follows by multiplying conjugates. ∎

In particular, **every polynomial birational change of these four coordinates that preserves this exact two-norm product is already of the separate affine type**. The collapsed type has two constant output coordinates and cannot generate a rational function field of transcendence degree four. The conclusion does not assume in advance that the map is affine, and it does not merely bound its degree.

This classifies re-factorizations with the same two-norm interface, not circuits computing the quartic product. A cheaper direct evaluation of that product, a change in Delta, coefficients depending rationally on the four coordinates, an alteration of other factors, or equivalence only on positive zeros remains outside the result. In the collapsed case the known composition identity is forced algebraically, but its optimal paid implementation is not established by this proposition.

## 3. A nonlinear rational chart that is positive but never integral on parent zeros

The polynomial restriction is substantial. Let `v=kappa`, and use the actual paid `kappa2=v²`. Define

    d0=v²−Delta, p=v²+Delta, b0=2v,
    Dnum=pD+Delta*b0*c,
    cnum=b0*D+p*c,
    D'=Dnum/d0, c'=cnum/d0.                          (2)

The rational change fixes mu and kappa. It is birational, with inverse obtained by replacing b0 by −b0. Direct expansion gives

    p²−Delta*b0²=d0²,
    Dnum²−Delta*cnum²=d0²*Nm,
    N(D',c')=Nm.                                    (3)

So it preserves the product Nm*Ni as a rational identity and genuinely lies beyond the polynomial classification.

On the actual complete positive supplied domain, the valid fixed numerals and positive input give u>0. Since delta is a positive integer,

    a>=1, Delta=(a+1)(a+3)>=8,
    v=u+delta*Delta>Delta.

Also c,D>0 directly from their producer definitions. Hence d0>0, and both coordinates in (2) are positive rational numbers. This positivity is available before imposing any norm or output equation.

**But (2) cannot give two integers at any parent positive zero.** The accepted parent theorem gives Nm=1. In the quadratic algebra, the element `z=D+c sqrt(Delta)` is therefore an integral unit, with integral inverse `D−c sqrt(Delta)`. Equation (2) multiplies it by

    w=(v+sqrt(Delta))/(v−sqrt(Delta))
      =p/d0+(2v/d0)*sqrt(Delta).

If D',c' were integers, then `w=(D'+c' sqrt(Delta))(D−c sqrt(Delta))` would have integral coefficients. Its second coefficient would have to be an integer. However Delta<=v−1 and v>=9 imply

    d0=v²−Delta >= v²−v+1 > 2v,
    0 < 2v/d0 < 1,

a contradiction. Equivalently, multiplying the coordinates explicitly gives the impossible integer equality

    D*c'−c*D' = 2v/d0.

This is uniform on the entire inherited positive zero set, not a diagnostic example or an assumption about selected Pell indices. The proof needs the accepted main-unit equation but no main/input index ordering or divisibility conjecture. It does not rule out encoding rational coordinates by additional integer numerators/denominators, changing other constraints, or using a different multiplier whose coefficients become integral on the old units.

## 4. Full paid accounting for this route

At the actually paid ports `D,c,kappa,Delta,kappa²`, the literal rational numerator/denominator schedule is

    d0=kappa²−Delta; p=kappa²+Delta; b0=kappa+kappa;
    pD=p*D; bc=b0*c; Dbc=Delta*bc; Dnum=pD+Dbc;
    pc=p*c; bD=b0*D; cnum=pc+bD.

It has5M+5A before two divisions. Division is not in the allowed source model. The integrality obstruction prevents treating its positive rational outputs as free positive integer coordinates.

There is a legitimate polynomial denominator clearing on the **unchanged** supplied coordinates. Let Pother denote the six unchanged factors, including the actual scaled strong factor. The parent output is `F84=Pother*Nm−Delta`. Substituting the numerator norm and replacing the final target by Delta*d0² yields

    Fnum=Pother*(Dnum²−Delta*cnum²)−Delta*d0²
        =d0²*F84.                                    (4)

The displayed numerator construction costs10 rows. Its norm adds3M+1A, and d0² and Delta*d0² add2M. Removing only the old private `L15=D²` and `norm_main=L15−Ac2` removes1M+1A; `c2` and `Ac2` remain needed by the auxiliary coefficient. All other81 nonremoved/nonfinal old rows are literal; the final subtraction changes its second operand. The fresh full source therefore has

    84−2+16=98 =56M+42A.

Every row and all25 supplied ports are live, including the original eighteen positive witnesses and ordinary input. Since d0>0 before equations on the valid positive domain, (4) preserves its entire positive zero set. Off that domain it is an all-ring multiplier identity, with no unrestricted zero-set equivalence when d0=0.

**The98-row schedule is not a minimum even for (4).** The same polynomial is computed by the original84 rows, then

    d0=kappa²−Delta; d02=d0*d0; output=d02*F84.

This has87=49M+38A operations and retains every old row and supplied port. Both schedules are saved to expose all charges. Neither improves84, and no lower bound for arbitrary evaluation or alternative normalization is inferred from their failure.

## 5. Evidence, pins, and next boundary

The new standard-library helper `complete84_nonlinear_norm_next_checks.py` reads only the pinned84 JSON and Markdown, checks literal producers/consumers, emits both complete arrays, and verifies the numerator norm and complete factor-level identity by exact sparse integer coefficients. It does not execute the old source or any old helper. The polynomial classification and the impossibility of integral positive chart values are mathematical proofs above, not finite-search conclusions. No numerical full Pell zero or compiled computation is materialized.

Fresh normal and `-O` writer runs from `/` produce byte-identical receipts. `--output` is exclusive and does not overwrite an existing receipt. No repository or frozen artifact was edited.

The following prior files in `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/` were read inertly:

| File | SHA-256 |
|---|---|
|`complete84_scaled_strong_output.json`|`8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`|
|`complete84_scaled_strong_output.md`|`01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade`|
|`complete84_affine_norm_pair_rigidity.md`|`eb67b76ac6a5c3150c37cf17c7e062fe6d19eae374adc8c27e8884fdebd58641`|
|`complete87_joint_norm_scout.md`|`681a06e6f280b9b17a723ab9046012f66ffcdeb963930e33d745b47ff044d1bf`|
|`complete87_strong_norm_composition_scout.md`|`34984de9b84c51673be3daf3b56c650ce4ba6ceaadfb15d68c4fe1b5b30255bb`|
|`complete84_joint_root_cut.md`|`79cfda9e870ad63a848fb454266d1bca98f2117393edc57f99108b4c1cce780c`|
|`complete84_actual_modulus_scout.md`|`068c5efb6d2fc6d011334d4e0cf7384e5d6d048ec64cee1c2161bb126cb173a1`|
|`complete84_aux_strong_joint_cut.md`|`4d67db790448fbfaf16082c904d89143f5f35152913015c55e576597160204e7`|
|`complete84_cross_block_next.md`|`f528326b033473e288c20da5ceb72bfd4cd94198ecfea11bf54f758a0ab3d5d5`|

A useful further rational chart must account for integral invertibility on the full old positive zero set, not only positivity over the rationals. A useful nonlinear evaluator must either evaluate the forced composed form more cheaply using actual donors or leave the exact two-norm product interface. These remain open possibilities; no global optimality statement is made.
