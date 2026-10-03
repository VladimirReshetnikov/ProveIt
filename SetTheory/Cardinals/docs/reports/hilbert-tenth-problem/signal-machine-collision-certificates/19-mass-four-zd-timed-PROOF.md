# Timed finite dimensional four mass orbits and quartic certificates

Research corollary, 3 October 2026. This packet is conditional on the effective orbit normal form in the separately audited higher-dimensional decision proof. It does not repair or independently establish that dynamical theorem. It extends the already existing one-dimensional fixed-input conclusion of Report 13; the algebraic compiler is inherited, with its proof restated for precision. No novelty or priority claim is made.

## 1. Exact conditional statement

Let d≥1 be finite. Fix a deterministic translation-equivariant finite-range cellular automaton F on Z^d over a finite alphabet A. Assume a unique zero-weight vacuum 0, positive integer weights on other symbols, conservation of finite total mass, and at most one weight-one symbol. Fix one finite initial configuration c of mass at most four. Throughout N={0,1,2,…}.

**Dynamical hypothesis NF.** The algorithm and normal-form assertions in §§1–9 and §11 of the supplied higher-dimensional PROOF.md are valid and effective, retaining the complete intermediate phase configurations and exact times. Specifically they produce a finite prefix and one of: synchronized independent finite-phase objects; a complete configuration periodic up to translation; or an expanding finite-control shuttle with one increasing additive gap, affine vector anchor updates, fixed finite scattering prefixes, and exact first-contact flight cutoffs.

**Theorem 1 (finite disjoint quadratic charts, conditional on NF).** One can effectively construct a finite family of charts describing the complete timed orbit {(t,F^t(c)):t∈N} in the original frame. Each chart has at most two natural parameters, an integer-affine domain, fixed occupied-site labels, and rational-polynomial time and vector coordinates of total degree at most two, integer-valued on its domain. Occupied sites are in strict lexicographic order. The disjoint union of chart domains maps bijectively to the timed orbit. In particular, every exact time has exactly one chart and one parameter tuple, regardless of recurrence of the configuration.

**Theorem 2 (ordinary quartic, conditional on NF).** For every fixed ordered tuple a=(a_1,…,a_m) of nonzero symbols, 0≤m≤4, there is an effectively obtained integer-coefficient polynomial C_a(t,X_1,…,X_m;w), of ordinary total degree at most four, for signed external X_v∈Z^d and t∈N, whose natural witness fiber has size one exactly if the complete configuration F^t(c) has occupied sites X_1<lex⋯<lex X_m and corresponding labels a, and has size zero otherwise. Its number of witnesses and coefficients may depend on F,c,d,a but not on t or the external coordinates. An optional padded representation gives one such polynomial for the entire orbit including variable site counts and labels.

If there are B retained charts, K total private parameter slots, M domain inequalities and H domain equalities, the baseline certificate has exactly

    N = B + K + M ≤ 3B + M

natural witnesses, and is a sum of

    1 + M + H + Q + B

squares of integer polynomials of degree at most two, where Q=1+dm for a fixed label tuple. Empty chart families use the constant polynomial 1 with no witnesses.

**Corollary 3 (fixed observations at an exact time).** Each fixed anchored finite pattern, including prescribed zeros, has an empty-or-singleton natural-witness quartic in external time t. The same is true of a fixed translated finite pattern after finite deterministic tie-breaking among successful placements. These claims are fixed-pattern statements; the construction and counts may depend on the whole finite pattern and its number of sites. They do not assert a uniform compiler or arity bound with an arbitrary pattern supplied as one externally encoded input.

Theorems 1–2 concern a special explicit chart interface, not a deduction from mere decidability. They assert no general finite-fold or single-fold MRDP result, no general bound uniform over c, and no generic rational- or real-witness exactness.

## 2. Canonical half open time phases

### Finite prefix and synchronized tails

Let T_0 be the effective start of the eventual profile. Materialize every complete configuration at times 0≤t<T_0 as a parameter-free chart. T_0 can be extremely large; no efficiency claim depends on it being small.

For a translated-periodic tail, choose its period p>0. At residue r, 0≤r<p, use n∈N and time t=T_0+r+pn. Every coordinate is affine in n and the phase labels are fixed. For an independent terminal tail, first extend the finite prefix past all individual transients and use one common multiple p of the individual periods. There is one global clock n, not independent existential clocks for the separate objects. Division of t−T_0 by p gives unique r,n. The vacuum uses a stationary one-clock tail with no occupied coordinates.

If there is no weight-one symbol, NF gives one of these same affine tails directly in the original frame; put δ=0 in the algebra below. If a unique unit symbol is present, use the normalized frame G=τ_(−δ)F of the source proof, so F^t=τ_(δt)G^t.

### Expanding shuttle

Let n∈N index complete repetitions of the eventual control cycle. At corresponding sections the gap and vector anchor are x_n=x_0+nΔ and L_n=L_0+nE, with Δ>0. The residue information already belongs to the control mode. For each of the finitely many cycle transitions ℓ, the first-contact flight duration is

    h_ℓ(n)=a_ℓ n+b_ℓ,

and the subsequent local seed prefix has a fixed length q_ℓ≥0. Each h_ℓ(n) is positive and integral for every n∈N along the repeated itinerary. Its coefficients are integers: b_ℓ=h_ℓ(0) and a_ℓ=h_ℓ(1)−h_ℓ(0). The source flight coefficient is positive and Δ>0, so a_ℓ>0. The cycle duration is An+C with integers A>0,C>0. Its start is

    T(n)=T_0+A n(n−1)/2+C n.

The half-open intervals [T(n),T(n+1)) partition every integer time from T_0 onward, since their lengths are An+C>0. Transition ℓ starts at

    S_ℓ(n)=T(n)+sum_{h<ℓ}(h_h(n)+q_h),

an integer-valued quadratic. Its owned interval is [S_ℓ(n),S_ℓ(n)+h_ℓ(n)+q_ℓ).

Suppose the free-flight packet has period p_ℓ. For each r∈{0,…,p_ℓ−1}, introduce n,j∈N with

    h_ℓ(n)−r−p_ℓ j−1 ≥ 0,
    t=S_ℓ(n)+r+p_ℓ j.

This flight chart owns exactly the integer times strictly before first contact. It has one affine inequality. The contact configuration belongs to the first local-prefix chart, if there is one. For each fixed s∈{0,…,q_ℓ−1}, use only n with

    t=S_ℓ(n)+h_ℓ(n)+s.

If q_ℓ=0, first contact is already the next checkpoint and belongs to the next transition. The next launch is never counted in the preceding transition. The formulas retain actual phase supports and labels, rather than convex hulls or particle identities. In a flight every stationary-frame support coordinate is affine in (n,j); in a local phase it is affine in n. Even when the phase has an empty domain it causes no accepted chart points and may be retained syntactically.

Uniqueness follows in this order: the half-open cycle interval determines n; the transition interval determines ℓ; flight versus prefix is disjoint; then Euclidean division selects r,j, or the fixed prefix index s. Thus every integer time occurs once. This argument, not injectivity of the spatial trajectory, establishes canonicity.

### Raw phase count

Let J be the number of raw charts before spatial ordering or label filtering. The literal construction gives

    J = T_0+p                         for an affine tail,
    J = T_0+sum_ℓ(p_ℓ+q_ℓ)          for a shuttle tail.

The finite prefix includes any adjustment of T_0 required above. Every raw chart has ≤2 parameters, ≤1 inequality and no domain equalities. These are finite input-dependent counts, not practical preprocessing bounds.

## 3. Vector coordinates and lexicographic sorting

For a raw chart, let g_v(z)∈Q^d be its stationary-frame occupied coordinate and let t(z) be its time polynomial. The original coordinate is

    P_v(z)=g_v(z)+δ t(z).

It has degree ≤2. However P_v−P_w=g_v−g_w remains affine. Therefore ordering introduces only affine constraints, even with nonzero drift.

A phase indexes actual occupied sites, whose number m is at most four. These indices describe positions and their labels inside the phase; they do not assert persistent physical identities through an interaction. For each permutation π of {1,…,m} and each tuple (k_1,…,k_(m−1))∈{1,…,d}^(m−1), add the conditions, for each neighboring pair v=π(a),w=π(a+1),

    g_{w,h}−g_{v,h}=0                 for 1≤h<k_a,
    g_{w,k_a}−g_{v,k_a}−1 ≥ 0.

The k_a coordinate is the unique first differing coordinate of the two sites. At a valid raw chart point all occupied sites are distinct, so exactly one permutation and exactly one tuple of first-difference coordinates are admitted. No factor for repeated labels occurs: labels follow the sites, and strict coordinate order is unique regardless of coincident symbol values. If coefficients are rational, clear each positive common denominator before interpreting inequalities or introducing integer slacks.

The number of sorting subcharts per raw phase is

    s_d(m)=1 for m=0 or 1,
    s_d(m)=m! d^(m−1) for 2≤m≤4.

Consequently B_all≤24d^3 J, before optional filtering by a fixed label tuple. Each retained sorted chart has ≤4 inequalities and ≤3(d−1) equalities. Hence

    K≤2B,  M≤4B,  H≤3(d−1)B,
    N≤7B≤168d^3 J.

The last bound is deliberately coarse. It neither removes the dependence of J on c nor asserts that J is uniformly bounded over inputs. Proved constant order permits omission of unnecessary sorting refinements.

For a fixed label tuple, retain only matching sorted charts. The domain-to-timed-output bijection is preserved. Labels of incompatible total mass give no charts. The empty tuple describes the vacuum only; conservation handles the nonzero-mass case immediately.

## 4. Explicit quartic compiler and its canonical witnesses

This elementary construction is Report 13's constant-term lifting compiler. For later observation corollaries it is useful to state the slightly more general form in which domain polynomials may have degree two rather than being affine.

A chart i has private natural parameter vector z_i, inequalities A_ir(z_i)≥0, equalities H_is(z_i)=0, and output P_i(z_i)∈Q^Q. All forms have degree ≤2, integer-valued outputs on valid domains, and all domain forms have integer coefficients after their own positive denominator clearing. Assume the disjoint chart domains map injectively to the external outputs of interest. The compiler itself does not prove this semantic injectivity.

Introduce natural selector e_i, the private parameters z_i, and natural slack u_ir for every inequality. Put E=sum_i e_i and Z_i=sum_j z_ij+sum_r u_ir. For a polynomial f belonging to branch i, put

    Lift_i(f)=f(z_i)−f(0)+f(0)e_i.

Only its literal constant term is multiplied by the selector. In particular no quadratic monomial is selector-gated. Let L_q be one common positive denominator for the pooled qth output coordinate across every branch. Define integer residuals

    R_0=E−1,
    R_ir=Lift_i(A_ir)−u_ir,
    U_is=Lift_i(H_is),
    V_q=L_q(y_q−sum_i Lift_i(P_iq)),
    G_i=(1−e_i)Z_i.

Then

    C(y;w)=R_0²+sum_ir R_ir²+sum_is U_is²+sum_q V_q²+sum_i G_i²

is an ordinary integer-coefficient polynomial of total degree ≤4. Each displayed residual has degree ≤2 in ALL external and witness variables. Pooled denominator clearing is important: independently rescaled branches cannot simply be added without restoring a common output scale.

At a natural zero, E=1 forces exactly one e_i=1. Every inactive gate forces Z_i=0, and naturalness forces each private parameter and slack in that branch to vanish individually. Its lifted forms then vanish. In the selected branch the equations say precisely that its parameters are admissible, each slack equals its fixed integer A_ir(z_i), and its output equals y. Conversely each admissible chart point has exactly that zero, with all inactive coordinates zero. Thus natural zeros are in bijection with admissible chart points over y. Disjoint half-open timed charts give empty-or-singleton fibers.

There are exactly B+K+M natural witnesses and 1+M+H+Q+B squared residual slots, before deleting identically zero residuals. For B=0 use C=1 and no witnesses. A known Report 13 optimization eliminates one selector in the SOS form: set e_B=1−sum_(i<B)e_i and replace R_0 by E_*(E_*−1), where E_*=sum_(i<B)e_i. The resulting N−1 bound is valid for B≥1, but is not needed for the stated baseline.

The SOS is nonnegative on all real arguments. This does not make its real or rational witness zeros exact. Private natural variables must not be replaced by unconstrained signed difference pairs: cancellations would invalidate inactive-zero and uniqueness arguments.

### Keeping external time in spatial residuals

For a fixed label tuple one may instead use the equivalent residuals

    X_(v,h)−δ_h t−sum_i Lift_i(g_(i,v,h))

with positive denominator clearing. They are affine in (external t,X, selectors, private parameters). The pooled quadratic time residual still enforces t=sum_i Lift_i(t_i). On zeros this is identical to substituting the quadratic time polynomial into every spatial output. Either implementation has degree ≤4 and the same witnesses. The latter explicit chart-output form also works unchanged for variable site counts and observation refinements.

## 5. One polynomial for the full orbit and signed positions

The family over fixed label tuples already describes the whole orbit. If a single polynomial is desired, fix distinct positive integer codes for nonzero symbols and code 0 for vacuum. Encode each configuration by

    (t, m, a_1,…,a_4, X_1,…,X_4),

where its m occupied sites are lexicographically sorted, slots beyond m have symbol code zero and vector coordinate zero, and every occupied symbol code is positive. Here Q=6+4d. Append these constant labels, m, and zero padding to each sorted chart's polynomial output. The same compiler gives one empty-or-singleton natural fiber for this full encoding, still with N≤7B. In padded slots, coordinates are literally zero: do not add δt to them.

Signed external coordinates are legitimate integer arguments of an ordinary Diophantine polynomial. To make every external argument natural, replace each scalar X by external inputs (X⁺,X⁻)∈N², substitute X⁺−X⁻ in its output equation, and add (X⁺X⁻)². The accepted pair is uniquely (max(X,0),max(−X,0)). These are external input slots, not extra witnesses. For a fixed m-site tuple this adds dm squared residuals and changes the external input count to 1+2dm; for the padded encoding it adds 4d residuals and gives 6+8d external slots. Total degree remains ≤4.

An external canonical translation vector may be handled in the same way. If instead signed coordinates are existential witnesses in a different construction, their positive/negative pairs and complementarity equations must be counted as witness slots and constraints; there is no free unique signed encoding by two unconstrained naturals.

## 6. Anchored versus translated complete configurations

The exact-coordinate relation above is anchored in the original lattice frame. For equality up to translation, normalize every nonempty configuration by its lexicographically first occupied site. Its relative output coordinates are

    P_v−P_1=g_v−g_1.

The common drift cancels; these spatial outputs are affine even though time remains quadratic. Use the output (t,P_2−P_1,…,P_m−P_1), together with the fixed label tuple. This has Q=1+d(m−1), no free translation witness, and the same exact-time uniqueness. Alternatively retain the first zero vector explicitly and validate it by its output equation.

A supplied target is normalized in the same way before testing. This is equality of entire finite configurations up to one common translation, not independent translation of different sites or components. For an empty target, only the mass-zero orbit qualifies. One must not introduce an arbitrary translation witness for the vacuum, since infinitely many such witnesses would encode the same fact.

## 7. Fixed finite patterns including zeros

Let a pattern P prescribe labels, possibly zero, on a fixed finite set W⊂Z^d of s sites. Its sites and values are constants for the following construction. Begin with ALL sorted charts, including their actual labels and variable m≤4; no a-tuple filter is necessary. A pattern is an observation rather than a complete configuration, so occupied sites outside W are permitted.

### A finite disjoint comparison refinement

For two integer vectors v,w there are exactly 2d+1 disjoint comparison alternatives:

- v=w, specified by all d coordinate equalities
- for some first differing coordinate k, earlier coordinates agree and v_k−w_k−1≥0
- for some first differing coordinate k, earlier coordinates agree and w_k−v_k−1≥0

This is a complete disjoint partition, including ties in some coordinates. If v,w are polynomial chart outputs of degree ≤2, every new condition has degree ≤2. Each comparison alternative contributes ≤d equalities and ≤1 inequality, so the generalized compiler in §4 applies.

### Anchored occurrence

Refine each sorted chart by all comparisons P_v(z) versus w, for v=1,…,m and w∈W. There are at most (2d+1)^(ms) subcharts. For each sign matrix, it is now a finite Boolean check whether every nonzero prescribed site equals an occupied site of the right label and every prescribed zero site equals no occupied site. Retain precisely the successful matrices. The comparisons are a partition, so one parameter point is never duplicated, even when several symbol labels are equal. Original-frame coordinate tests can be quadratic because of δt; degree ≤2 is sufficient.

Output only t. At any fixed t the orbit determines exactly one raw chart and parameter point, and its complete comparison matrix is unique. Therefore the retained chart-to-time map is injective. The quartic has exactly one natural witness when P occurs at the anchored window at t, and none otherwise.

With B denoting the sorted full-orbit chart count before observation refinement, one may use the uniform bounds

    B_anch ≤ B (2d+1)^(4s),
    K_anch≤2B_anch,
    M_anch≤(4+4s)B_anch,
    H_anch≤[3(d−1)+4ds]B_anch,
    N_anch≤(7+4s)B_anch.

There are 2+M_anch+H_anch+B_anch SOS slots since Q=1. These intentionally loose counts depend on the fixed pattern size s.

### Translated occurrence with a nonzero prescribed symbol

Choose once and for all a distinguished prescribed nonzero site w_*∈W. In a chart with m occupied sites, every successful translation b must send w_* to some occupied site P_i carrying its label. Hence its candidate translation is b_i=P_i−w_*. There are at most m≤4 candidates, and distinct occupied sites give distinct translations. There may nevertheless be several successful candidates.

For every i,v∈{1,…,m} and w∈W, compare

    P_v−P_i     with     w−w_*.

Equivalently compare g_v−g_i with the fixed offset: δt cancels. Refine by the complete matrix of these at most m²s comparisons, with the 2d+1 alternatives above. Every new domain condition is affine. The matrix and the fixed labels decide the success of every candidate, including every prescribed zero. Retain precisely the matrices for which at least one candidate succeeds. No existential placement variable or extra multiplicity is introduced.

If an actual placement is to be output, choose the smallest occupied-site index i whose candidate succeeds, which is determined by the matrix. Because sites are lexicographically sorted, this is the lexicographically first successful translation among the finite candidates. Append b_i=P_i−w_* to that subchart's output. The time-and-selected-placement relation is again canonical. The unselected successful placements are deliberately not additional witnesses.

For occurrence in external time alone, valid bounds are

    B_trans ≤ B (2d+1)^(16s),
    K_trans≤2B_trans,
    M_trans≤(4+16s)B_trans,
    H_trans≤[3(d−1)+16ds]B_trans,
    N_trans≤(7+16s)B_trans.

These describe a finite refinement, not a fast implementation. Keeping all candidate comparisons ensures disjointness without converting an overlapping disjunction of successful candidates into multiple witnesses.

### All zero and empty patterns

If a fixed translated pattern prescribes only zeros, some translate occurs in every finite-support configuration at every time: move its finite window far past the support in one coordinate. The empty window is vacuously satisfied. For existence in external t∈N, the zero polynomial in no witness variables has the one empty witness tuple at every t. This does not assert a lexicographically least translation, which need not exist.

If an explicit canonical placement is desired, choose a concrete rule instead: for nonempty support put b=(max_v P_(v,1)+1−min_(w∈W) w_1,0,…,0). All translated window sites then have first coordinate beyond the support. Lex sorting makes the maximum first coordinate equal to that of the last occupied site. For vacuum choose b=0. This rule has polynomial outputs of degree ≤2 within each sorted chart; it is a chosen placement, not a claimed minimum among all successful translations. A nonempty all-zero window is assumed in this formula; for the empty window choose b=0.

## 8. Recurrence and limits of the witness statement

Time is an external input throughout the single-fold assertions. A stationary configuration may appear at every t∈N; periodic configurations or pattern hits may also recur infinitely. If time is made an additional existential natural witness, the very same construction has one zero for EACH occurrence time. Its fiber is then finite or infinite according to the time set; there is no general finite-fold conclusion for the untimed projection. A constant nonempty stationary orbit is already an infinite-fiber example.

Likewise, a raw translated-pattern certificate that existentially includes every successful placement may have several witnesses at one exact time. The finite first-success construction above removes this placement multiplicity, but not multiplicity over different times. Complete configurations normalized by their first site avoid placement witnesses altogether.

The bounded site count gives explicit costs in terms of J,B,d and fixed pattern size. It does not bound J or the materialized prefix length uniformly over input c, does not establish an arity bound for arbitrary externally encoded inputs, and supplies no uniform unbounded finite-fold MRDP representation. Report 13 already proved the one-dimensional fixed-input quartic conclusion and its baseline compiler; the present conditional extension uses the higher-dimensional normal form and first-differing-coordinate refinement.

## 9. Provenance and verification scope

The dynamical normal-form source is *Four mass units in every finite spatial dimension*, research proof dated 3 October 2026, SHA-256 3e8eb41fe43b5b4b61d0e0a5b4bece3b01cf628f834a820ecc369f4da427b30a.

The one-dimensional compiler source is Report 13, *Canonical quartic certificates for timed four mass orbits*, 3 October 2026, source SHA-256 fecc0ae2f226b366cc184950419fa98b49707b975d72e369e25ad47a6d73de9b. Its preceding Report 12, *Four mass units and exact reachability*, supplies the original one-dimensional dynamical setting.

All theorems in this corollary remain explicitly conditional on NF. The local arithmetic checks test sorting partitions, exact phase boundaries, drift restoration, and witness plumbing on finite fixtures; they do not prove NF or instantiate a general rule-to-chart compiler. The prior releases have not been modified.
