# Original-frame canonical first-hit quartics for complete configurations

Exploratory successor proof, 3 October 2026. This is a new, local sibling packet. It does not modify Report29, Report30, any earlier research packet, or any publication. The theorem is conditional on the reviewed effective orbit normal form and original-frame timed certificate theorem in Report29. Its additional dynamical argument is elementary and is proved below. No generic single-fold MRDP theorem is used.

## 1. Statement and exact scope

Fix a finite dimension d, a deterministic translation-equivariant finite-radius cellular automaton F on Z^d with a finite alphabet, positive integer nonvacuum weights, a unique quiescent weight-zero vacuum, conserved finite total mass, and at most one weight-one symbol. Fix a finite input c of mass at most four. Write N={0,1,2,...}.

A **complete target** specifies every occupied site and its nonzero label; there may be no additional occupied sites. Targets are positioned in the original F frame. They are not a query about one visited site, one pattern, or equality only up to translation.

For each fixed nonzero label tuple a=(a_1,...,a_m), 0≤m≤4, there is an effectively constructible ordinary integer polynomial

    P_a(X_1,...,X_m; w),       X_i∈Z^d, w∈N^W,

of total degree at most four in external inputs and witnesses together, such that its natural witness fiber is a singleton exactly when the strictly lexicographically ordered labeled target is a complete configuration F^t(c) for some t≥0, and is empty otherwise. The unique witness can include the first such absolute time t. Invalid orderings are rejected.

One polynomial can instead accept the canonical padded target encoding

    z=(m,a_1,...,a_4,X_1,...,X_4),

where 0≤m≤4, labels in occupied slots are nonzero codes, occupied sites are strictly lexicographically increasing, and every unused label and coordinate slot is zero. Invalid encodings are rejected. Coefficients and arities depend on the entire fixed CA and input. This is not a uniform-over-input arity theorem.

The stationary-frame restriction can therefore be removed for **complete configuration targets**. It is not removed for individual visited sites or arbitrary patterns by this proof. Complete targets can occur infinitely often on a periodic orbit; the first-hit construction explicitly handles that case.

If d=0 is admitted, the lattice has one site and the finite alphabet gives a finite-state orbit; the affine/finite argument below applies. The displayed d-dependent chart estimates are stated only for d≥1.

## 2. Input from the reviewed normal form

If the unique possible unit symbol exists, let δ be its isolated displacement and G=τ_{−δ}F, so

    F^t(c)=τ_{tδ}G^t(c).

If it does not exist, take δ=0 and use the no-unit normal form. The reviewed classification effectively returns a finite prefix and one of:

1. Independent finite-phase objects
2. A whole configuration periodic up to translation
3. An expanding shuttle

For the first two alternatives, after a finite prefix and common period, all occupied coordinates and absolute time are affine in a natural period parameter. This remains true after restoring δt. The no-unit and all mass-below-four cases are covered by these affine alternatives.

For an expanding shuttle, choose the eventual repeated emission section. Its data include a fixed primitive nonzero vector ν∈Z^d, a positive integer Δ, a fixed transverse vector z, and two actual occupied residual unit sites satisfying

    L_n=L_0+nE,
    R_n−L_n=(x_0+nΔ)ν+z,                  n∈N.                 (2.1)

The finite control mode has repeated, including its transverse offset. Thus z is fixed at these corresponding sections. Section times are

    T_n=T_0+A n(n−1)/2+Cn,                 A,C∈Z_{>0}.          (2.2)

Both residual units in (2.1) are present at every emission section. The remaining mass-two packet may be a weight-two singleton or two unit sites. Their labels need not distinguish geometric roles.

Report29's timed theorem supplies original-frame, strictly sorted complete-configuration charts and an integer polynomial

    C_a(t,X;v)

of degree at most four, with exactly one v∈N^{W_0} when t∈N and X is the complete configuration at time t, and no v otherwise. The same theorem supplies a padded variable-site-count/label version. The whole finite prefix is included. Sorting is refined phase by phase; it is not assumed constant in time.

## 3. The key injectivity argument

### Lemma 3.1: exact recurrence implies bounded future diameter

For any deterministic map F on configurations, if

    F^{s}(c)=F^{t}(c),                 0≤s<t,

then for every k≥0,

    F^{s+k}(c)=F^{t+k}(c).

This follows by applying F^k to the equality. The orbit from time s is exactly periodic with period t−s, hence takes only finitely many configuration values. For finite configurations their diameters are bounded. Adding the finite earlier prefix does not change boundedness.

No reversibility or injectivity of F is required. The repeat is exact equality of positioned, labeled configurations; equality up to translation is not enough for this lemma's conclusion.

### Lemma 3.2: every expanding shuttle has unbounded original-frame diameter

Select a coordinate k with ν_k≠0. At its section times, the two occupied sites in (2.1) give

    diam(G^{T_n}(c)) ≥ |(x_0+nΔ)ν_k+z_k| → ∞.

A common translation does not change any site difference or diameter. Therefore

    diam(F^{T_n}(c))=diam(G^{T_n}(c)) → ∞.                  (3.1)

The argument is unaffected by weighted singleton packets, two-unit packets, label coincidences, local-prefix splitting or fusion, or any changes in support size away from the selected emission sections. Only the two genuine occupied unit sites at the sections are used. Expanding shuttles only arise in the mass-four/unit case; there is no missing no-unit expanding case.

### Proposition 3.3: the complete positioned orbit of an expanding shuttle is injective in time

If two times anywhere in the orbit, including its finite prefix, had the same complete configuration, Lemma 3.1 would make the entire orbit's diameters bounded. Equation (3.1) contradicts that. Thus

    F^s(c)=F^t(c) implies s=t,             s,t∈N.           (3.2)

In particular, every complete target that occurs has precisely one occurrence time. That time is automatically its first occurrence. This proves a stronger fact than uniqueness merely inside one raw phase.

## 4. Expanding-case certificate: move time into the witness tuple

For an expanding input, define

    P_a(X; t,v)=C_a(t,X;v),                (t,v)∈N^{1+W_0}.

The polynomial expression is unchanged; an argument is merely reclassified from external natural time to a natural witness. Its ordinary total degree remains at most four.

For each target X and each t, the timed theorem says that the v-fiber is either empty or singleton, and is singleton precisely at an actual occurrence. Proposition 3.3 says that at most one such t exists. Hence the full (t,v)-fiber is empty or singleton. If nonempty, its first coordinate is the first absolute hit time.

This step does **not** infer single-foldness from decidability, or generally infer untimed uniqueness from timed uniqueness. It combines the timed theorem with the newly proved orbit injectivity. Report29's warning about simply forgetting time remains valid for stationary/periodic orbits, and for observations less informative than complete configurations.

All details about full support, fixed or variable labels, lexicographic sorting, half-open phase ownership, changing numbers of occupied sites, rational denominator clearing, inactive witnesses, and weighted phase shapes are inherited exactly from the timed complete-configuration theorem. Turning t into a witness does not change any domain or consistency constraint. In particular, zero-padded coordinates do not receive the restored drift.

### 4.1 Literal and coarse counts

Use Report29's notation, scoped to the selected fixed input and target-label interface:

- J = T_0 + Σ_ℓ(p_ℓ+q_ℓ), the raw chart count, with the finite prefix materialized
- B_ch = retained sorted chart count
- K = total private natural chart parameters
- M = total domain inequality occurrences
- H = total domain equality occurrences
- Q = number of external outputs in the original timed chart compiler

For a nonempty chart family, the untimed certificate with first time included has exactly

    W_exp = B_ch+K+M+1,
    R_exp = 1+M+H+Q+B_ch

natural witnesses and squared residual slots. R_exp is unchanged from the timed construction. For d≥1,

    B_ch≤24d³J,        K≤2B_ch,        M≤4B_ch,
    H≤3(d−1)B_ch,
    W_exp≤7B_ch+1≤168d³J+1.

For a fixed m-site label tuple, Q=1+dm, hence

    R_exp≤2+dm+(3d+2)B_ch.

For the padded all-count/all-label interface, Q=6+4d, hence

    R_exp≤7+4d+(3d+2)B_ch.

Counts are literal before removing identities. If no compatible charts remain, use P=1 with no witnesses. These are potentially enormous input-dependent counts, not uniform bounds over all finite inputs.

An external-first-time version is simply Report29's original C; under expanding injectivity it already accepts only first times. Membership together with canonically reconstructed first time uses the same internal-time construction, whose t coordinate explicitly supplies that reconstruction.

## 5. Affine, translated-periodic, independent, finite, and no-unit alternatives

These alternatives may repeat complete configurations, so §4 cannot be used without an additional argument. Instead their original-frame timed configuration relation is Presburger.

After the effective finite prefix, take a common phase period. Each phase has a finite list of fixed labels and occupied coordinates affine in n≥0, with

    t=T_0+r+pn.

Restoring δt adds an affine vector to each occupied site. For complete targets, impose exact equality of support and labels by the finite disjunction over assignments of the finitely many occupied sites to target slots, together with strict sorting and padding where applicable. Include each finite-prefix time. This produces a Presburger formula Occ(z,t) for exactly the canonical complete target z at time t. No assumption that coordinate order is constant is used.

Define

    First(z,t) := Occ(z,t) and t≥0
                  and not exists s (0≤s<t and Occ(z,s)).      (5.1)

It is Presburger, and is the graph of a partial function f(z)∈N on the reachable complete targets. It handles prefix-versus-tail overlaps, independent objects with common phase periods, zero drift, repeated whole configurations, and infinite repetition.

For completeness, an effective semilinear decomposition of this functional graph gives a finite cover on which f is rational affine. On a linear-set graph component, write generators as (v_j,w_j), separating target coordinates and time. Every integer relation Σ a_jv_j=0 forces Σ a_jw_j=0: separate a into its nonnegative positive and negative parts, giving two graph points with the same target, and use functionality. Thus v_j↦w_j extends to a rational linear map on their span, and the base point supplies an affine constant. Effective rational linear algebra finds an extension to the ambient target coordinates. The projected component domain is semilinear. Standard effective Presburger elimination then provides a finite disjoint sign/residue refinement of the domains.

The following explicit compiler records both its exactness and counts. On pairwise disjoint branches i=1,...,B, write the domain as

    A_ir(z)≥0,      H_is(z)=0,      L_ik(z)≡r_ik mod m_ik,

with integer affine forms, positive fixed moduli, and rational affine first-time functions f_i(z). Let I,H,C be the total inequality, equality, and congruence occurrences over branches. Choose a single positive D with F_i=Df_i integer affine for every branch. Introduce natural selectors e_i, inequality slacks u_ir, and canonical signed quotient pairs q_ik^+,q_ik^−. Sum the squares of

    Σ_i e_i−1,
    e_i A_ir(z)−u_ir,
    e_i H_is(z),
    e_i(L_ik(z)−r_ik)−m_ik(q_ik^+−q_ik^−),
    q_ik^+q_ik^−,
    Dt−Σ_i e_i F_i(z).

Every residual has degree at most two, so their sum of squares is an ordinary integer quartic. The selector equation picks exactly one branch. Inactive slacks and quotient pairs are uniquely zero. Active slacks are their forced nonnegative values; an active integer quotient q has the unique pair (max(q,0),max(−q,0)). Disjointness fixes the branch, and the last equation fixes t=f_i(z). Conversely these canonical values satisfy every residual for a first hit.

With t external, the exact counts are

    W_aff,ext = B+I+2C,
    R_aff = 2+I+H+2C.

With first time made one additional natural witness, they are

    W_aff,int = B+I+2C+1,
    R_aff,int = R_aff.

Without time, omit the last residual and t witness. The unique selector canonically reconstructs f(z)=Σ_i e_if_i(z). No square-lift witness is needed because f_i is affine. If the first-hit domain is empty, use P=1. A finite orbit can equivalently be treated by finite singleton target cells with their earliest times.

## 6. Empty targets, encodings, and boundary cases

The unique zero-weight vacuum and positive nonvacuum weights imply that a mass-zero finite configuration is exactly vacuum. Conservation implies:

- If c has mass zero, its only complete target is the empty configuration; first hit is t=0
- If c has positive mass, the empty complete target is never reached

For the fixed m=0 interface, use t² with t as one natural witness in the vacuum case, and P=1 otherwise. For the padded interface, in the vacuum case sum the squares of m, every label slot, every signed coordinate slot, and t. This rejects all nonempty or noncanonically padded targets and has one witness t=0. Equivalently the generic affine compiler applies.

For positive mass, target label tuples of incompatible total mass retain no charts. Symbols of weight greater than four cannot occur. Equal labels do not identify equal sites: strict spatial order and complete-support equality remain required.

If all external slots must be natural, replace each signed coordinate x by x^+−x^− and add the squared residual (x^+x^−)². The accepted external pair is uniquely (max(x,0),max(−x,0)); these are external slots, not extra witnesses. Affine substitution and the quadratic extra residual preserve ordinary degree at most four. For fixed m this adds dm residual slots, and for four padded coordinate slots it adds 4d.

No conclusion is asserted about rational or real witness fibers, and no mere difference-of-two-naturals representation without the product condition is used to assert uniqueness.

## 7. Why this does not solve site or pattern first hits in the original frame

A complete target determines an entire state of the deterministic system. Repetition therefore restarts exactly the same future. A repeated visited site, a repeated finite pattern, or a repeated translated observation does not determine the full state and does not force periodicity.

Likewise the inverse-chart ranks use two residual marker sites plus a packet site, or a remote unit plus a local mass-three site. A single-site query omits this relative configuration data. The present proof makes no original-frame single-site first-hit claim and does not repair one by substituting y−δt into a stationary first-visit certificate.

## 8. Provenance and verification status

Read-only dependencies and SHA-256 hashes at the start of this investigation:

- Report29 `report29.tex`: `1e4b9cb159801ce06d283a851ce2c47925610a27f7914d0ed8c8e3902874cedc`
- Report29 timed companion `scientific/timed/PROOF.md`: `103fe38f7c6d941995e579d7d73dd42ab3836a012666ba16858b158ff698d4c5`
- Sparse orbit geometry `PROOF.md`: `3f05b484cd3c0035422df431f571bb2b56c85a31d5f49ae681033ffb2ca6e4fa`
- Canonical first-visit compiler `PROOF.md`: `3247951ca7afa4d65bd3eb90d99bfb48fcb43dbf0eaa067c3e9380cdfbcebbda`

The primary argument in §§3–4 is an independent elementary deduction from these assumptions. The affine-time compiler in §5 is stated explicitly rather than invoking a generic Diophantine representation theorem. This packet neither reproves the entire mass-four classification nor claims novelty for the standard deterministic recurrence or Presburger ingredients. The independent conditional adversarial review is supplied in `REVIEW.md`. The separate exploratory inverse-phase companion is not a dependency of this proof or review. Finite checks, if supplied, are sanity checks and do not replace the proof.
