# The entire positive native fiber: two indices and an exact height law

Date: 2026-10-03. Research continuation of Report 22. All earlier reports and frozen source packets are unchanged. The classification below concerns the complete twenty-two-coordinate positive witness fiber of the prescribed-scale native AND component. It is conditional on the pinned source's proved soundness and positive completeness, not on a canonical choice of auxiliary Pell index.

## 1. Statement

Fix valid ports (P,Hhat,Mhat,Zhat), so P is a power of two, H=Hhat−1, Mport=Mhat−1, Z=Zhat−1 satisfy 0≤H,Mport<P and Z=H AND Mport. Set q=16P. The fixed source has twenty-two positive supplied coordinates

    F0,F1,F2,a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y_aux,odd_half,bound_beta.

Exactly seventeen coordinates are forced by these relation arguments. Only f,i,j,o,y_aux vary. The forced values are listed in §2.

Write

    A=a+2, Δ=A²−1, p=2r+1, c=ψ_A(p),
    α=A+√Δ, λ=log α,
    g=gcd(c,Δ)=gcd(p,Δ), M0=pc/g.

Here χ_B(v)+ψ_B(v)√(B²−1)=(B+√(B²−1))^v. The pinned native soundness gives p≡3 (mod 4), c>2p, A≥3; also M0≥c>2p.

The entire positive fiber is in bijection with the following two-index set:

    m=M0 l,                    l=1,2,3,...,
    n=p, or n=4mk−p, 4mk+p,    k=1,2,3,... .             (1)

For these indices put

    f_m=χ_A(m), R_m=Δψ_A(m), i_m=R_m/c²,
    U_(m,n)=χ_(R_m)(n)/R_m,
    j_(m,n)=(U_(m,n)+p)/c,
    o_(m,n)=(U_(m,n)+c)/f_m,
    y_(m,n)=ψ_(R_m)(n).                                (2)

All values in (2) are positive integers; adjoining the seventeen forced coordinates gives precisely every positive native witness, without duplication. In particular n=p is present for every allowed m, including the minimal noncanonical choice m=M0. No canonical m=2cp assumption remains.

The maximum supplied-coordinate height is exactly

    height(m,n)=ψ_(R_m)(n).                            (3)

In fact every forced supplied coordinate is strictly below c², while R_m=ic²≥c² and y_(m,n)>R_m. There is no initial fixed-coordinate plateau in an actual native fiber.

For each m let D_m=R_m²−1, ε_m=R_m+√D_m, and

    t_m(H)=asinh(H√D_m)/log ε_m,
    T_m(H)=floor(t_m(H)).

Define L_H to be the largest l≥1 with ψ_(R_(M0 l))(p)≤H, or zero if there is none. It is finite. For every real H≥1 the exact count is

    N(H)=Σ_(l=1)^(L_H) [ floor((T_m(H)+4m−p)/(4m))
                         +floor((T_m(H)+p)/(4m)) ],
                  where m=M0 l.                       (4)

For H<1, N(H)=0. Either occurrence of T_m(H) in (4) may be replaced by t_m(H). Thus (4) is an effective finite expression, not an infinite formal sum.

If an explicit upper summation bound is preferred, L_H may be replaced by

    K0(H)=floor(log H/[M0(p−1)λ]),                     (4a)

because all added summands are zero. Section 6 proves the uniform lower bound log ψ_(R_m)(p)≥(p−1)mλ that justifies this cutoff. The exact Pell inverse must still be retained inside the summands.

As H→∞, with the valid ports and scale fixed,

    N(H)=κ log H+O(√log H),                            (5)
    κ=1/[M0(p−1)λ]
        +Σ_(l≥1) 1/[2M0 l log ε_(M0 l)].               (6)

The series converges absolutely. Its first term outside the sum comes from the exceptional baseline n=p across varying m. It cannot be recovered by summing the fixed-slice leading coefficients alone. All logarithms are natural; constants in the remainder may depend on the fixed ports and scale.

## 2. The seventeen forced coordinates

The literal padded ports and checksum force

    F3=16Z+8                      (computed, not supplied),
    F1=16(H−Z)+4,
    F2=16(Mport−Z)+2,
    F0=16(P−H−Mport+Z)−15,
    r=F0+qF1+q²F2+q³F3.

Pinned selector soundness, §§2–3, proves for every positive witness, before any canonical converse is chosen,

    X=2^(2r+1), Y=floor((X+1)^(2r)/X^r),
    w=X/q, s=Y/q, a=Y(X+1),
    c=ψ_A(p), d=χ_A(p), p=2r+1,
    B=2XY²+1, k=ψ_B(r+1).

Here X,Y,B are computed or mathematical parameters, not supplied coordinates. The remaining forced supplied coordinates are

    h=(k−r−1)/(XY),
    eta=c−Yk, zeta=(Y+1)k−c,
    tau=(χ_B(r+1)−1)/2,
    ga=(d−X−ac)/(4a+3),
    odd_half=(s−1)/2, bound_beta=X−r.

These are exactly seventeen names: F0,F1,F2,r,w,s,a,c,d,k,h,eta,zeta,tau,ga,odd_half,bound_beta. The selector's positive converse gives at least one positive witness for every valid input; uniqueness then ensures these values are positive integers and satisfy all thirteen comparisons not involving the five varying coordinates. Alternatively their integrality and positivity are the individual conclusions of that converse.

The independent literal DAG audit is in DEPENDENCY-AUDIT.md. Exactly three of sixteen comparisons depend on the varying five-coordinate set:

    (ic²)²=Δ(f²−1),
    (ic²)²(U²−y_aux²)=1−y_aux²,
    U=jc−p=of−c.                                      (7)

Thus there is no omitted comparison or operation that could restrict the variation after (7) is verified. The five-coordinate audit leaves thirteen comparisons unchanged; the earlier three-coordinate slice left fourteen unchanged.

## 3. Exact classification of the main auxiliary index

The source's large-main-index bootstrap gives c>AΔ² before using the relaxed auxiliary norm. The pinned relaxed-auxiliary proof establishes from the first equation of (7), for every positive solution,

    f=χ_A(m), R=ic²=Δψ_A(m), p|m.                      (8)

This is stronger than the abbreviated c|m displayed in the selector note. It excludes the extra rational Pell solutions that the isolated relaxed norm could otherwise have. The proof works for A≥2 and c>AΔ², independently of its historical notation A=a+4; the native source explicitly verifies the same hypotheses at A=a+2. No new integrality result is claimed here.

Write m=pk. Expansion of (d+c√Δ)^k gives

    ψ_A(pk)/c ≡ k d^(k−1) (mod c).                    (9)

All terms after the linear term contain c², and gcd(d,c)=1 by the main Pell norm. Consequently

    c² | Δψ_A(pk)
       ⇔ c | Δk d^(k−1)
       ⇔ c | Δk
       ⇔ c/g | k,             g=gcd(c,Δ).             (10)

This is an equivalence, so it proves sufficiency as well as necessity of m∈M0·Z_(>0). The main recurrence or binomial expansion modulo Δ gives

    c=ψ_A(p)≡p A^(p−1) (mod Δ),

and gcd(A,Δ)=1; hence g=gcd(p,Δ), so g|p and M0=pc/g is a multiple of c. In particular every allowed m satisfies m≥c>2p. For such m, (2) gives a positive integral i and the first equation of (7) exactly.

## 4. Exact classification of the normalized auxiliary index

Fix any m=M0l. Then c|m, R_m is a positive multiple of c², and f_m>2c. Also R_m²=Δ(f_m²−1). The earlier native-slice theorem, an explicit corollary of the repository's fixed-minus parity proof, applies to these algebraic hypotheses without requiring the fixed five-tuple to have come from a canonical witness.

For completeness, set D_m=R_m²−1. Positivity gives U=jc−p≥c−p>0. The second equation of (7) is

    (R_m U)²−D_m y_aux²=1.

The integer-coefficient Pell classification gives R_m U=χ_(R_m)(n), y_aux=ψ_(R_m)(n), n≥1. Reduction modulo R_m forces n odd. For n=2h+1, the standard polynomial identity χ_X(2h+1)=XQ_h(X²) yields

    U≡(−1)^h n (mod c),
    U≡(−1)^h ψ_A(n) (mod f_m).

The two fixed-minus congruences are U≡−p (mod c), U≡−c (mod f_m). The repository's plus-sign chi step-down with comparison index 2p<m gives n=e p+2mt, e∈{±1}. Keeping both signs forces t even and p≡3 (mod 4); hence n≡±p (mod 4m). Conversely those two residues, together with p≡3 (mod 4) and c|m, give both fixed-minus congruences. This is precisely the proof already recorded in the slice theorem §§2–4 and the pinned parity proof §§2–3.

Thus (1) is necessary and sufficient. In particular, n=p gives both congruences for every m=M0l, so the baseline is genuine for all noncanonical main indices. Reconstruction gives positive integral j,o,y and both remaining equations of (7). The unchanged thirteen equations now show that every listed pair gives a full native witness. Strict increase of χ_A(m) and, for fixed m, ψ_(R_m)(n), proves injectivity.

## 5. Exact maximum height and finite counting

We first bound the seventeen forced supplied coordinates. The source bounds give q<r<X<a<A<c. Thus F0,F1,F2,r,w,s,a,odd_half,bound_beta<c; c itself is of course less than c². Also k<c/Y<c, h<k, eta<c, zeta<k. The main norm gives d/c=√(Δ+1/c²)<A, so d<Ac<c². Since 4a+3>A, the positive exponent quotient obeys ga<d/(4a+3)<c. Finally, with E=XY<a,

    tau²<tau(tau+1)=(E²+X)(Yk)²<(E+1)²(Yk)²,

because X<2E+1. Therefore

    tau<(E+1)Yk<(E+1)c<Ac<c².

This accounts for all seventeen forced coordinates and bounds each strictly below c².

First R_m>f_m: R_m²=Δ(f_m²−1)>f_m² for Δ≥3, f_m≥2. Also i_m=R_m/c²≤R_m. Since n≥p≥3,

    y_(m,n)≥ψ_(R_m)(3)=4R_m²−1>R_m,

so y dominates f and i. The normalized norm gives 0<U≤y. With c>p and f>c,

    U+p≤y+c−1≤cy, U+c≤y+f−1≤fy,

so j,o≤y as well. As R_m=ic²≥c², y also strictly dominates the seventeen forced coordinates. This proves (3) for the complete twenty-two-coordinate tuple.

Clarification relative to the earlier fixed-slice discussion: its formula max(C,y) is correct, but when C is the maximum of the actual nineteen fixed native coordinates, a native plateau cannot occur. The same inequalities also give f,i≤R<ψ_R(p)≤y. A plateau is possible only after adding an independently imposed cutoff C, for example further fixed coordinates not proved smaller. Earlier frozen artifacts are preserved; this is the explicit stronger conclusion.

For fixed m the closed form

    ψ_(R_m)(n)=sinh(n log ε_m)/√D_m

is strictly increasing in n. It gives n≤T_m(H) exactly. The smallest admissible n is p, proving that only m=M0l with l≤L_H contribute. The sequence R_(M0l) and the polynomial ψ_R(p) are strictly increasing, and both tend to infinity; therefore L_H is finite and may be located by exact integer comparisons. Counting the residues p and 4m−p yields (4). No astronomical tuple needs to be materialized in order for this mathematical expression to be well-defined; ordinary exact evaluation is possible but has its unavoidable output-size costs.

## 6. Uniform whole-fiber asymptotics

Put L=log H and β_m=log ε_m. Split N(H)=B(H)+Q(H), where B counts just n=p for varying m and Q counts n=4mk±p, k≥1. This split is essential because B is supported on O(L) main-index slices, while Q is supported only on O(√L) slices.

For the baseline, R_m=(√Δ/2)α^m(1−α^(−2m)), so log R_m=mλ+O(1). For fixed p, ψ_R(p) has degree p−1 and positive leading coefficient 2^(p−1), and for R≥2 it lies between R^(p−1) and (2R)^(p−1). Consequently

    log ψ_(R_m)(p)=(p−1)mλ+O(1),
    B(H)=L/[M0(p−1)λ]+O(1).                          (11)

For Q, its least admissible normalized index at m is 4m−p. Since m≥c>2p, 4m−p−1≥3m. Since R_m>f_m=χ_A(m), monotonicity of arcosh gives β_m=arcosh R_m>mλ. The exact geometric-sum formula gives ψ_(R_m)(n)≥ε_m^(n−1). Therefore

    log ψ_(R_m)(4m−p)≥3λm².                          (12)

Hence Q is zero at m>J(L)=√(L/(3λ)).

Uniformly for m≥M0 and H≥1,

    0≤t_m(H)−L/β_m≤1.                               (13)

Indeed asinh(H√D_m)≥log H, while asinh(H√D_m)≤log H+asinh√D_m=log H+β_m: the latter follows by differentiating the difference in H≥1, which is nonincreasing and equals β_m at H=1. The two-residue floor formula then gives for the total slice count

    N_m(H)=L/(2mβ_m)+O(1),                           (14)

with an absolute uniform error bound. Subtracting the slice's baseline indicator 1_(t_m(H)≥p) preserves that O(1) bound. Summing only over multiples m=M0l≤J(L) thus yields

    Q(H)=L Σ_(M0l≤J(L)) 1/[2M0l β_(M0l)] +O(√L).

Since β_m>mλ, the coefficient tail is bounded by a constant times 1/J(L):

    Σ_(M0l>J(L)) 1/[2M0l β_(M0l)]
       ≤(1/(2λM0²)) Σ_(l>J(L)/M0) l^(−2)=O(L^(−1/2)).

Extending the sum to infinity costs O(√L), which, with (11), proves (5)–(6). This does not sum fixed-slice O(1) terms over the O(L) baseline range. It also accounts for the growing D_m in the inverse-height formula; dropping that dependence would give the wrong baseline exponent p rather than p−1.

More quantitatively, writing κ_nonbaseline for the series in (6), its tail after K≥1 terms is at most 1/(2λM0²K), and 0<κ_nonbaseline≤π²/(12λM0²). One may therefore evaluate the coefficient with a certified truncation bound. Replacing log ε_m by mλ in the coefficient itself changes κ and is not an exact leading-term computation.

No all-orders expansion or definite coefficient of √log H is asserted. The staircase floors can carry secondary oscillations, and proving more requires a separate uniform summation analysis. For maximum bit length b, H=2^b−1 gives N_bits(b)=κ(log 2)b+O(√b).

## 7. Provenance, novelty boundary, and evidence

The main-index recovery and relaxed-norm rank proof belong to the pinned repository. The fixed-minus congruence analysis and n≡±p (mod 4m) necessity also belong to it; the earlier local slice theorem made their converse and fixed-slice count explicit. Classical Pell generation and its fixed-base logarithmic height growth are standard.

The present compiler-specific extraction is the reduction of this entire twenty-two-coordinate native fiber to exactly two indices, the exact progression M0Z_(>0) for m, the five-coordinate height domination, and the uniform whole-fiber coefficient (6), including its separately counted baseline. This is not a literature-wide novelty claim, an arithmetic circuit simplification, a finite-fold construction, or a full tuple materialization.

Pinned primary sources (commit ad634b2d10ad666260f9fdff04ec94b75169ee4b):

- Native selector soundness: https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_binary_selector56.md
- Prescribed-scale interface: https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_binary_masked_selection63.md
- Relaxed auxiliary proof: https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md
- Fixed-minus proof: https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md
- Odd-index construction: https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_ODD_INDEX_PELL_SIGNS.md

Earlier local result: the earlier fixed-slice theorem (historical context; the required argument is restated in the entire-fiber theorem §4). Frozen literal DAG data are copied read-only into source/native_blocks.json. The source code was not imported or executed; no full clone or public action was performed. Finite checks are secondary evidence only; universal conclusions rest on the arguments above and the explicitly credited pinned results.

Independent local exact checks pass in both normal and optimized Python modes: 2,725 modular divisibility checks over 55 parameter pairs; thirteen materialized auxiliary tuples, including a large-main-index case satisfying the rank hypothesis; 1,200 exhaustively tested normalized-index residues; eighteen count tests immediately below, at, and above six Pell-height jump boundaries. Small examples are explicitly auxiliary examples, not claims that small parameters satisfy the complete padded native source. The literal-DAG audit separately checks all sixteen residuals on four fixtures, with three negative mutation tests. Both mathematical reviews pass; see CLASSIFICATION-REVIEW.md and COUNT-REVIEW.md.

## Subsequent refinement

The separate second-term theorem supplied in this release sharpens the first-order remainder stated here. The no-secondary-coefficient sentence above records the scope of this first-order proof, not a limitation of the later addendum. All delivered paths are release-root-relative unless explicitly linked.
