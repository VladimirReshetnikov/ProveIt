# A smaller-degree signed ratio weight in24 unrestricted integers

This is a separate variant of INTEGER24_PROOF.md, with artifacts named `integer24_ratio_*`. It keeps the same24 unrestricted integer variables and coherent coefficient binding. Only the two separating weights change. Its product has168 binary gates and exact degree1936; the three-comparison system has163 gates and maximum residual degree1920; SOS171 gates and degree3840.

## 1. Polynomial changes

Retain all baseline abbreviations through I=i c^2, v=cT, d,e, and the main-root radicand G. Replace the old Bnd by

    W=2*((i I)*(1+5R ac)+v^2).

Use

    L=1+H W, M=2W, S=X+ac+Hr.

The norm is the same finite conjugate product, now with linear expression `S-Lu-HM tau`:

    N=Norm_G,u Norm_A,tau( [d(S-Lu-HM tau)^2-H^2e]^2-H^4 Baux^2D ).

The product, comparison system and SOS finalizers are unchanged. In the JSON evaluator the register named Bnd now holds W; this convention is explicitly recorded in `weight_definition`.

The baseline weak transport and all sign-safe pre-reconstruction bounds remain valid, since they do not involve either weight. In particular R>0, ac>0 (a and c have the same sign), iI=i^2c^2>0, |a|>=q^3>=4096, |c|>1, |H|>6, G>4, and1<b<Q. Therefore W>0 and B=|H|W>8. The new weight is safe even when s,i,T or H are negative and when X=0 or T=0.

## 2. A normalized bound for every auxiliary conjugate

For every auxiliary conjugate y', including complex branches,

    |y'|<2(|v|sqrt(D)+b),

exactly as in the baseline proof. The following estimates are valid before excluding X=0 or negative s.

Since i^2 c^2>1,

    D/G=(1+Delta i^2c^4)/(1+Delta c^2)<i^2c^2,

hence `|v|sqrt(D)/sqrt(G)<=|iT|c^2`, with strict inequality when T is nonzero. Equality at T=0 is allowed; the other bounds below remain strict.

Put t=|a|>=4096. Since Delta=(a+2)^2-1, we have

    sqrt(Delta)>t-3;
    D<(t+2)^2 i^2 c^4;
    (t+2)^2/(t-3)<2t.

The last inequality is equivalent to t^2-10t-4>0 and is true for t>=4096. Also `sqrt(G)>sqrt(Delta)|c|`. Using b=c+RD and ac=t|c|>0 gives

    b/sqrt(G) < 1+2R ac i^2 c^2=1+2R ac iI.

Therefore

    |y'|/sqrt(G)
       <2|iT|c^2+2+4R ac iI
       <=iI+v^2+2+4R ac iI
       <(1+5R ac)iI+v^2=W/2.

Here the last strict step uses R ac iI>2, which follows from the already established integer bounds. No sign of T is assumed; the inequality `2|iT|<=i^2+T^2` explains exactly why iI+v^2 occurs in the inexpensive polynomial bound.

## 3. Main-root separation and the X=0 boundary

For H>0, L=1+B; for H<0, L=1-B. As B>8,

    |L|>B/2, hence |L|sqrt(G)>|H||y'|.

This is the first Galois separation used in the baseline proof, now expressed relative to sqrt(G), rather than by an unnormalized absolute bound on y'. At X=0, A=1, so tau is already integral. A sign change of irrational u would contradict this separation; u and then y are rational. The baseline saturation lemma, including its Baux=0 branch, makes y integral, and reduction modulo H (L=1 mod H) makes gamma integral. The main norm modulo H excludes X=0. No tau-separation estimate or positive-s theorem has been used yet.

## 4. First-root separation after X>0

Now X>=16 and Z=|Y|>=q^3>=4096; use only Z>=32. Then

    |a+2|/(XZ) <=1+1/16+2/(16*32)=273/256,
    |c|/(kZ) <1+1/32=33/32.

Thus

    sqrt(G)<(9009/8192)ell<(9/8)sqrt(A).

Also |L|<=B+1<(9/8)B. Together with the bound from Section2,

    |L|sqrt(G)+|H||y'|
       <(9/8+1/2)B sqrt(G)
       <(13/8)(9/8)B sqrt(A)
       =(117/64)B sqrt(A)
       <2B sqrt(A)=|HM|sqrt(A).

This forces tau rational by the same Galois sign-flip argument. Then the first separation forces u rational; saturation yields integral y and gamma, the interval1<b<Q excludes T=0, and f is recovered as an integral root. All conclusions of baseline Sections5--6 now follow. Only after these restorations is package23's negative-s exclusion invoked. Thus the variant has the same signed soundness and the same genuine blank computation endpoint.

## 5. Completeness

Use the simultaneous odd i, odd s, square w canonical witnesses established in the baseline proof and its source theorem. Define

    r=gamma+W u+M tau+y.

Then S=Lu+HM tau+Hy, so one coherent factor of the polynomial norm vanishes. All variables are within the same24-integer parametrization. No new source restriction or altered Pell index is required.

## 6. Exact arithmetic and tied leading terms

The weight uses seven gates, reusing I,ac,v^2 and R: compute iI, Rac,5Rac,1+5Rac, their product with iI, add v^2, multiply by2. The old Bnd used three gates. Replacing HL by HM=2HW adds one further gate, as in the split2 variant. Thus the product costs163+4+1=168 gates. The direct norm comparison saves its final subtraction, giving163 gates; the computed-norm system164; fully explicit residual system166; SOS171.

Under the same variable weights as the baseline,

    deg(W)=48, deg(L)=deg(HM)=59, deg(S)=20,
    deg(d)=82, deg(H)=11, deg(b)=68, deg(ell)=20.

Unlike the previous split2 variant, H^2e now has degree240 and TIES d times the squared dominant linear term. It must not be discarded. The exact leading identities are

    A_top=G_top=ell_top^2;
    e_top=d_top b_top^2;
    W_top ell_top=10 b_top.

The four leading linear combinations `-L u-HM tau` have coefficients -3,-1,+1,+3 times10H_top b_top. After subtracting H^2e, their coefficients are899,99,99,899 times d_top H_top^2 b_top^2. The f-dependent term H^2 Baux f has strictly smaller degree212 (the displayed squared-norm subtractand H^4 Baux^2D has degree424, below480). Hence

    N_top=(99*899)^4 d_top^8 H_top^16 b_top^16,

which is nonzero uniformly for every authentic beta>0. Its exact degree is

    8*82+16*11+16*68=1920.

Multiplying the nonzero degree12 and degree4 index and transport leaders gives product degree1936. The SOS has degree3840. The generator explicitly verifies this tied-leading-form certificate, rather than importing the earlier3^8 certificate, which would be wrong here.

As elsewhere, exact finite circuit checks supplement the universal mathematical proof and inherited compiler theorem, not an end-to-end kernel-checked formalization or a decision of Con(ZFC).
