# Independent review: unsmoothed second term for the complete native fiber

Date: 2026-10-03. Verdict: **PASS**, conditional only on the existing native-fiber parametrization and exact coordinate-height law. The stronger count has an elementary, pointwise hyperbola proof with remainder O((log H)^(1/3)). No smoothing, averaging, equidistribution, or unproved cancellation of floor phases is needed.

This review was derived independently from the earlier THEOREM.md and COUNT-REVIEW.md. It does not edit or replace either earlier report. It separately checks exact boundary rectangles and tied-height quantile inversion.

## 1. Reviewed conclusion

Keep A, p, and M fixed, with A≥3, p≥3, and M≥c>2p as in the native parametrization. Put

    Δ=A²−1, λ=log(A+√Δ), m_l=Ml,
    R_m=√Δ sinh(mλ), β_m=arcosh R_m,
    T=log H,
    κ=1/[M(p−1)λ]+Σ_(l≥1)1/[2Ml β_(Ml)].

Assume the permitted index pairs are precisely

    m=Ml, l≥1;
    n=p, or n=4mk−p, 4mk+p, k≥1,

and their height is ψ_(R_m)(n). Then, pointwise as H→∞,

    N(H)=κT+d√T+O_(A,p,M)(T^(1/3)),
    d=ζ(1/2)/(M√λ).                                  (1)

In particular d<0. The coefficient κ is exactly the previous whole-fiber coefficient, not the coefficient obtained by replacing β_(Ml) with Mlλ. The √T coefficient is independent of the bounded offset in β_m and of the fixed residue parameter p, except through the permitted spacing M.

The asymptotic is for fixed parameters. Its onset and implicit constants need not be uniform as A, p, or M vary.

## 2. Exact energies and useful uniform bounds

For integer n≥1,

    log ψ_(R_m)(n)=(n−1)β_m+θ_(m,n),
    θ_(m,n)=log(1−e^(−2nβ_m))−log(1−e^(−2β_m)).       (2)

Consequently, with b=(log Δ)/2 and d_*=-log(1−e^(−2Mλ)),

    mλ≤β_m≤mλ+b,
    0≤θ_(m,n)≤d_*.                                   (3)

All constants here are fixed. The previously proved stronger expansion β_m=mλ+b+O(e^(−2mλ)) is valid but unnecessary for (1).

For σ∈{−1,+1}, define the nonbaseline energy

    Eσ(l,k)=log ψ_(R_(Ml))(4Ml k+σp),
    a0=4λM²,
    g_l=4Ml β_(Ml).

Equations (2)–(3) give the exact decomposition

    Eσ(l,k)=g_l k+(σp−1)β_(Ml)+θ_(Ml,4Ml k+σp),        (4)

and the uniform comparison

    |Eσ(l,k)−a0kl²|≤Ckl   (l,k≥1),                    (5)

where one admissible constant is

    C=4Mb+(p+1)Mλ+(p+1)b+d_*.

Indeed, after subtracting a0kl² the three terms are bounded by 4Mbkl, (p+1)(Mλl+b), and d_*, and k,l≥1 absorb the latter bounds into Ckl.

The energy increases strictly in each positive integer variable. For fixed k, both R_(Ml) and the positive integer index 4Ml k+σp increase with l. The Pell polynomial ψ_R(n) increases with R for n≥2 and with n for R>1. The assumptions ensure all indices here exceed 1. Finiteness also follows from

    Eσ(l,k)≥(4Ml k−p−1)Mlλ≥3λM²kl².                  (6)

Thus every row and column below a fixed threshold is an initial finite segment of positive integers.

## 3. Exact row estimates retain the complete leading coefficient

Let qσ(T,l) be the number of k≥1 with Eσ(l,k)≤T. The exact Pell inverse is

    t_l(e^T)=asinh(e^T sinh β_(Ml))/β_(Ml),
    qσ(T,l)=max(0,floor((t_l(e^T)−σp)/(4Ml))).          (7)

For T≥0, the earlier uniform inverse estimate gives

    0≤t_l(e^T)−T/β_(Ml)≤1.

Since M>2p, equation (7) therefore implies the genuinely uniform estimate

    qσ(T,l)=T/g_l+O(1).                               (8)

This does not discard floor phases: each individual floor discrepancy is bounded and will only be summed over a short range of rows. Clipping the floor at zero changes the same estimate by at most another bounded amount.

The slope tail satisfies

    S:=Σ_(l≥1)1/g_l<∞,
    Σ_(l>L)1/g_l=1/(a0L)+O(L^(−2)),                  (9)

because g_l=a0l²+O(l), and hence 1/g_l=1/(a0l²)+O(l^(−3)). The coefficient S remains the exact series. The O(l) perturbation in g_l is used only in the tail estimate, where its aggregate effect is small enough.

## 4. Uniform inverse-column estimate, without any floor-phase claim

Let rσ(T,k) be the number of l≥1 with Eσ(l,k)≤T. Put

    x=√(T/(a0k)), B=C/a0.

From (5),

    l²−Bl≤Eσ(l,k)/(a0k)≤l²+Bl.

For every integer l≤x−B, the upper inequality implies Eσ(l,k)≤T, since l²+Bl≤(l+B)²≤x². Conversely Eσ(l,k)≤T implies l²−Bl≤x² and therefore l≤x+B (the positive quadratic root is at most x+B). Including the integer endpoint error yields

    rσ(T,k)=√(T/(a0k))+O(1),                          (10)

uniformly in T≥0 and k≥1. If x−B<0, the lower count is simply zero, and the same estimate holds. Thus all column floors cost at most O(number of columns); there is no appeal to their average value.

## 5. Exact hyperbola decomposition and its boundary rectangle

For T sufficiently large set

    L=floor(T^(1/3)),
    Kσ=qσ(T,L).

By (8) and g_L=a0L²+O(L),

    Kσ=T/(a0L²)+O(T/L³+1)
       =T/(a0L²)+O(1),
    Kσ≍T^(1/3).                                     (11)

The constants in the comparison can depend on a0, as allowed.

Write Qσ(T) for the total nonbaseline count on sign σ. There is an exact identity

    Qσ(T)=Σ_(l≤L)qσ(T,l)+Σ_(k≤Kσ)rσ(T,k)−LKσ.        (12)

The boundary justification is important:

- Every point in the rectangle 1≤l≤L, 1≤k≤Kσ is counted: monotonicity gives Eσ(l,k)≤Eσ(L,Kσ)≤T
- No point with both l>L and k>Kσ can be counted: already Eσ(L,Kσ+1)>T, and energy increases with l and k
- Therefore the two strips cover the region and intersect in exactly the complete rectangle of size LKσ

This remains valid when the threshold equals an energy, because Kσ is the exact weak-threshold row count. The two signs may have different Kσ; each decomposition is used separately. There is no unexamined common rectangle, discarded corner, or tie assumption.

Substitute (8)–(10) into (12), with u=√(T/a0):

    Qσ(T)=ST−T/(a0L)
             +u Σ_(k≤Kσ)k^(−1/2)−LKσ
             +O(L+T/L²+Kσ).                         (13)

The classical one-variable sum, directly obtainable by Euler summation, is

    Σ_(k=1)^K k^(−1/2)=2√K+ζ(1/2)+O(K^(−1/2)).       (14)

The constant in (14) can equivalently be defined as the convergent limit of the left side minus 2√K; Euler summation identifies it with the analytic continuation of ζ(s) at s=1/2. Thus no oscillatory input is being imported into the argument.

The possible mismatch between the exact cutoff Kσ and the model hyperbola cancels quadratically:

    −T/(a0L)+2u√Kσ−LKσ
       =−L(√Kσ−u/L)².                               (15)

By (11), |Kσ−u²/L²|=O(1), so

    |√Kσ−u/L|=O(T^(−1/6)),
    L(√Kσ−u/L)²=O(1).

The Euler-sum error contributes u/√Kσ=O(T^(1/3)). Every other error in (13) is also O(T^(1/3)). Hence, separately for each sign,

    Qσ(T)=ST+[ζ(1/2)/(2M√λ)]√T+O(T^(1/3)).           (16)

This proves the proposed nonbaseline second term with no logarithmic loss.

## 6. Baseline and full count

The baseline energy obeys

    log ψ_(R_(Ml))(p)=(p−1)Mlλ+O(1)

uniformly in l, and is strictly increasing. It follows that

    B(T)=T/[M(p−1)λ]+O(1).                           (17)

Adding B(T), Q−(T), and Q+(T) gives (1), because 2S=Σ_l 1/[2Ml β_(Ml)]. The baseline does not contribute a √T term.

The previous O(√T) theorem was correct but did not preclude a universal second term. Its warning about staircase floors was an evidence boundary, not an obstruction: the exact hyperbola partition now confines all such discrepancies to O(T^(1/3)) rows and columns.

## 7. Tied-height quantile inversion

List the witnesses in nondecreasing height with multiplicity, allowing arbitrary ordering within ties. Let H_v denote the height of the v-th witness and T_v=log H_v. Define F(T)=N(e^T). Since all heights counted at T_v−1 are strictly below H_v,

    F(T_v−1)<v≤F(T_v).                               (18)

No uniqueness of a witness at a height is assumed. Since T_v→∞, applying (1) at both arguments in (18) gives

    v=κT_v+d√T_v+O(T_v^(1/3)).                       (19)

Indeed the main terms at T_v and T_v−1 differ by O(1), while their remainder bounds are both O(T_v^(1/3)). First (19) yields T_v∼v/κ, then T_v−v/κ=O(√v). Consequently √T_v=√(v/κ)+O(1), and substitution gives

    T_v=v/κ−[d/κ^(3/2)]√v+O(v^(1/3)),               (20)

or explicitly

    log H_v=v/κ−ζ(1/2)/[M√λ κ^(3/2)]√v+O(v^(1/3)).

The square-root correction in (20) is positive, since ζ(1/2)<0. After exponentiating, the correct conclusion is an exponential with O(v^(1/3)) in its exponent; that error is not a relative 1+o(1) estimate for H_v. Ties are completely compatible with (20).

## 8. Scope and remaining obligations

The review establishes the stronger analytic count and its inversion for the stipulated pair family. It does not independently reprove native soundness, completeness, the exact spacing M, or maximum-coordinate domination; those remain the dependencies recorded in the earlier theorem.

No numerical experiment is required by this proof. No smoothing or averaging is used, and no external source or author code was executed. The essential ingredients are the exact Pell inverse in short rows, a uniform quadratic comparison in short columns, exact boundary bookkeeping, and the elementary partial sum of k^(−1/2).

## 9. Final-artifact verification

The completed companion THEOREM.md was inspected after this independent derivation. **PASS as written:** its deterministic-cutoff proof, equations (8)–(18), correctly controls positive-part row clipping, the O(1) possible boundary columns beyond K, the case where the effective column cutoff lies below K, and the quadratic cancellation. Its ranked-height inversion, equations (21)–(23), correctly allows arbitrary ties. The cited partial-sum identity and sign justification agree with [NIST DLMF 25.2.8](https://dlmf.nist.gov/25.2.E8) and [25.2.3](https://dlmf.nist.gov/25.2.E3), inspected directly. No additional assumption or correction is required. This final-artifact verification concerns the analytical proof; it does not independently certify the reported test counts or checker implementation.
