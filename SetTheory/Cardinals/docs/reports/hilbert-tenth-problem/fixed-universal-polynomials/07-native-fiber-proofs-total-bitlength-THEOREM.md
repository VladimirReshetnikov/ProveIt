# Sum of all twenty-two coordinate bitlengths

Date: 2026-10-03. A bounded companion to the entire-native-fiber classification and its unsmoothed two-term count. Earlier reports and frozen packets are unchanged.

## 1. Result

Use the fixed valid native ports and all notation of `../entire-fiber/THEOREM.md`. In particular

    Δ=A²−1, α=A+√Δ, λ=log α,
    p≡3 (mod 4), p≥3, c=ψ_A(p),
    M=M0=pc/gcd(c,Δ)≥c>2p,
    m=Ml, l≥1;    n=p or n=4mk±p, k≥1,
    R_m=Δψ_A(m), β_m=arcosh R_m.

The classification already proves a bijection between these pairs and complete positive twenty-two-coordinate native witnesses. Exactly seventeen coordinates are fixed. The other five are

    f=χ_A(m), i=R_m/c², U=χ_(R_m)(n)/R_m,
    j=(U+p)/c, o=(U+c)/f, y=ψ_(R_m)(n).

Here U is a derived quantity, not an additional supplied coordinate. All five displayed supplied coordinates, as well as the seventeen fixed ones, are positive integers by the prerequisite classification.

For a positive integer x define its binary bitlength by

    b(x)=floor(log_2 x)+1.

For a full tuple w, let S(w) be the SUM of b(x) over its twenty-two supplied coordinates. This is the total unsigned coordinate-bit budget; no delimiters, signs, encoding metadata, or derived quantities are included. Let N_sum(B) count distinct complete tuples with S(w)≤B, for a real budget B. Define

    κ_s = 1/[M(3p−2)λ] + Σ_(l≥1) 1/[6Ml β_(Ml)],
    d_s = ζ(1/2)/[M√(3λ)].

Then, as B→∞ through arbitrary real values,

    N_sum(B) = κ_s (log 2) B
                 + d_s √(log 2) √B + O(B^(1/3)).             (1)

The constants in O(·) may depend on the fixed ports and scale. The coefficient uses the exact β_(Ml), not its linear approximation. All logarithms other than log_2 are natural. No smoothing or generic-position hypothesis is used; (1) includes integer bitlength jump boundaries and all ties.

If κ is the maximum-coordinate-height coefficient in the prerequisite packet, then

    κ_s = κ/3 − 1/[Mλ(3p−2)(3p−3)].                         (2)

Thus the total-bit coefficient is not simply one third of the maximum-bit coefficient. The baseline n=p has a different relative correction.

## 2. Exact product and uniform logarithmic energy

Multiplying exactly, without an asymptotic substitution, gives

    f i j o y = R_m y (U+p)(U+c)/c³.                        (3)

The factor f cancels. Put E(m,n)=log(f i j o y), q=Mλ, and ε=exp β_m. The elementary closed forms give

    log R_m = β_m−log 2+r_m,
    log y = (n−1)β_m+θ_(m,n),
    log U = (n−1)β_m+u_(m,n),

where, for every allowed m,n,

    0≤r_m=log(1+exp(−2β_m))≤r_*:=log(1+exp(−2q)),
    0≤θ_(m,n)≤d_*:=−log(1−exp(−2q)),
    −r_*≤u_(m,n)=log(1+exp(−2nβ_m))−r_m≤0.

These inequalities use β_m≥mλ≥q and n≥p≥3. Also U≥1, since χ_R(n)≥χ_R(1)=R for n≥1. Consequently

    E(m,n)=(3n−2)β_m+ρ_(m,n),                             (4)
    ρ=−log 2−3log c+r_m+θ+2u
                         +log(1+p/U)+log(1+c/U),
    |ρ_(m,n)|≤C_E
       :=log 2+3log c+3r_*+d_*+log(1+p)+log(1+c).          (5)

This deliberately loose bound is finite and uniform over the ENTIRE admissible two-index set, including n=p and all nonbaseline branches. In particular, no supposedly small error is inserted into a floor without a bound.

The prerequisite bound is

    mλ≤β_m≤mλ+b,       b=(log Δ)/2.                        (6)

Let F(T)=#{(m,n) admissible : E(m,n)≤T}. We will prove

    F(T)=κ_s T+d_s√T+O(T^(1/3)).                           (7)

The count is finite for each finite T by (4)–(6): the baseline has a linear energy lower bound in l, while either nonbaseline branch has a quadratic one. It is unbounded because the baseline is infinite. Equal products count different pairs separately.

## 3. Baseline and hyperbola proof

For n=p, (4)–(6) imply, uniformly in l,

    E(Ml,p)=(3p−2)Mλl+O(1).

Sandwiching the admissible l between two linear cutoffs therefore proves

    F_baseline(T)=T/[M(3p−2)λ]+O(1).                       (8)

For σ∈{−1,+1}, put

    E_σ(l,k)=E(Ml,4Mlk+σp),
    a_l=12Ml β_(Ml),       a=12λM².

Equations (4)–(6) give

    E_σ(l,k)=a_l k+(3σp−2)β_(Ml)+ρ_σ(l,k),
    a_l=a l²+O(l),
    1/a_l=1/(a l²)+O(l^(−3)).                             (9)

For k,l≥1, an explicit constant

    C=12Mb+(3p+2)(q+b)+C_E

satisfies |E_σ(l,k)−a k l²|≤Ckl. The product defining E is positive integral and greater than one, so E_σ>0. Hence

    |√(E_σ(l,k)/(ak))−l|≤D:=C/a.                         (10)

There are two uniform counting consequences. For a fixed row l, the exact count r_σ(l,T) of positive k with E_σ(l,k)≤T is bounded below and above by

    max(0,floor((T−(3σp−2)β_(Ml)∓C_E)/a_l)).

The minus sign gives the lower bound and the plus sign the upper bound. Because |(3σp−2)β_(Ml)/a_l|≤(3p+2)/(12M) and a_l≥a, these bounds show

    r_σ(l,T)=T/a_l+O(1)                                  (11)

uniformly in l≥1,T≥0. The positive-part clipping does not spoil this bound: its argument differs from the nonnegative T/a_l by a bounded quantity.

For a fixed column k, (10) shows that the number of admitted l>L, with integer L≥0, is

    (√(T/(ak))−L)_+ + O(1).                              (12)

Indeed all positive integers l≤√(T/(ak))−D are admitted, and none above √(T/(ak))+D are admitted. This does not assume monotonicity of the error or stability of a floor.

For large T take

    L=floor(T^(1/3)), X=T/a, K=floor(X/L²).

Both L and K are comparable to T^(1/3). Rows l≤L contribute

    T Σ_(l≤L)1/a_l+O(L).

For rows l>L there can be no admitted column beyond X/(L+1−D)², by (10). This cutoff differs from X/L² by O(X/L³)=O(1). The possible O(1) extra columns above K each contain O(1) admitted rows, since √(X/k)<L there. For k≤K the positive part in (12) is unclipped. Thus, including every boundary column,

    Q_σ(T)=T Σ_(l≤L)1/a_l
                 +√X Σ_(k≤K)k^(−1/2)−LK+O(L+K+1).       (13)

The reciprocal-slope tail and the classical zeta partial-sum formula are

    Σ_(l>L)1/a_l=1/(aL)+O(L^(−2)),
    Σ_(k≤K)k^(−1/2)=2√K+ζ(1/2)+O(K^(−1/2)).              (14)

The second identity is the Euler–Maclaurin/zeta formula used in the earlier second-term packet; see NIST DLMF 25.2.8, https://dlmf.nist.gov/25.2.E8. Substitution into (13) leaves the cancellation

    2√(XK)−LK−X/L=−L(√K−√X/L)²=O(1).

All remaining errors are O(T^(1/3)). Therefore each sign contributes

    Q_σ(T)=T Σ_(l≥1)1/[12Ml β_(Ml)]
                +ζ(1/2)/[2M√(3λ)] √T+O(T^(1/3)).         (15)

The two signs are disjoint because 0<p<2m; neither meets n=p because 4m−p>p. Adding (8) and both copies of (15) proves (7).

The exact infinite sum is extracted before approximating its tail. Replacing β_(Ml) by Mlλ throughout that sum would generally change the leading coefficient. Its tail after K≥1 terms is at most 1/(6λM²K), and the entire nonbaseline coefficient is at most π²/(36λM²).

## 4. From products to the exact total-bit staircase

Let C_bits be the sum of the bitlengths of the seventeen fixed supplied coordinates. It is a fixed integer. For each of the five positive varying coordinates,

    log_2 x < b(x) ≤ log_2 x+1.

Writing b_var=b(f)+b(i)+b(j)+b(o)+b(y), we obtain

    E(m,n)/log 2 < b_var ≤ E(m,n)/log 2+5,
    S(w)=C_bits+b_var.

Consequently, for every real B,

    F((B−C_bits−5)log 2) ≤ N_sum(B)
                             ≤ F((B−C_bits)log 2).       (16)

For large B both arguments are positive. Applying (7) to both ends of (16) proves (1): a fixed shift changes the linear term by O(1), the square-root term by O(B^(−1/2)), and preserves the O(B^(1/3)) error. This is a global sandwich, so it also covers all bit-rounding phases, powers of two, exact cutoffs, and tied tuples. The fixed coordinates can be enormous, but their total cost is constant when the native ports and scale are fixed.

## 5. Ranking by total bits, with ties

List all complete tuples in nondecreasing S(w), with multiplicity and any order within a tie, and let B_v be the integer total bitlength of tuple v. Set

    a_s=κ_s log 2,       e_s=d_s√(log 2).

Then

    B_v=v/a_s−e_s a_s^(−3/2)√v+O(v^(1/3)).               (17)

Indeed N_sum(B_v−1)<v≤N_sum(B_v). Applying (1) on both sides gives v=a_sB_v+e_s√B_v+O(B_v^(1/3)); first B_v~v/a_s, then B_v−v/a_s=O(√v), and substitution proves (17). Since ζ(1/2)<0, the displayed square-root correction to ranked total bits is positive. No bound on tie multiplicity and no unique-height hypothesis is needed.

## 6. Scope and evidence

This theorem counts SUMS of all twenty-two supplied positive-coordinate bitlengths. It is not a maximum-coordinate-height or maximum-bitbudget formula, nor an arbitrary serialization-length formula. It inherits the native bijection and positivity from the frozen classification; it does not reprove the source Pell rank or congruence results, materialize a native tuple, simplify the circuit, or establish finite-foldness.

The product identity, its uniform energy control, the separate 3p−2 baseline, and the global rounding sandwich are the new bounded companion argument. The analytic method is the same classical hyperbola/Euler–Maclaurin method as the frozen second-term packet. Finite auxiliary checks are supporting evidence only, not proofs of the classification or asymptotic law.

Independent review and exact small auxiliary checks are recorded separately in this directory. The small Pell parameters used there do not claim to be complete padded native instances. No upstream source code is imported or executed and no public action is performed.
