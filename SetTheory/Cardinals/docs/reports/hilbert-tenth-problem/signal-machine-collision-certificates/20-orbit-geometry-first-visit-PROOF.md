# Canonical first-visit quartics from disjoint Presburger cells

Research note, 3 October 2026. This is a new sibling packet. Existing research packets, releases, and publication files are unchanged. The dynamical application is conditional on the reviewed mass-at-most-four normal form and its effective affine phase-time data. No generic finite-fold or single-fold MRDP theorem is used.

## Application theorem at a glance

Conditional on the reviewed normal form, for every fixed promised CA and mass-at-most-four input, the stationary-frame set of visited sites has an effective ordinary integer polynomial of degree at most four with exactly one natural witness tuple per visited external integer site and no witness otherwise. Its unique witness canonically determines the site's first-arrival time. This covers expanding, affine, finite, and empty alternatives.

For an expanding tail, the first-arrival time may itself be external with only **one shared natural cycle counter** beyond the membership witnesses, or may be included as one additional canonical natural witness. If the final disjoint Presburger partition has B branches and I,H,C inequality, equality, and congruence occurrences, then for nonempty S:

- Membership: W=B+I+2C witnesses; R=1+I+H+2C squared residuals
- External first time, expanding tail: W=B+I+2C+1; R=3+I+H+2C
- Internal first time, expanding tail: W=B+I+2C+2; same R
- External first time, affine tail: W=B+I+2C; R=2+I+H+2C

Finite-prefix first visits are included. These are input-dependent counts, not a uniform arity theorem. The shared-counter specialization is proved in §6.4. Section 6.5 extends it to fixed Presburger observation schemas, including complete stationary-frame configuration targets and anchors of a fixed finite pattern. The general elementary compiler and a separate arbitrary piecewise-quadratic output construction are developed first for clarity.

## 1. Elementary compiler theorem

Let S be an effectively Presburger-definable subset of Z^d. Suppose, when a time output is wanted, that a specified function f:S→N has an effective finite cover by semilinear sets on each of which f equals a rational polynomial of degree at most two. Here N={0,1,2,...}. The cover need not initially be disjoint.

Then one can effectively produce an ordinary integer polynomial P(y;w), of total degree at most four in external coordinates and witnesses together, with

    #{w∈N^W : P(y;w)=0} = 1 if y∈S, and 0 otherwise,

for every signed external y∈Z^d. At its unique witness, f(y) can be reconstructed canonically from the unique selected cell. If desired, one can instead produce an ordinary integer quartic P_time(y,t;w) whose natural witness fiber is a singleton exactly when y∈S and t=f(y), and empty otherwise. Time may also be moved from the external arguments to one additional natural witness; the resulting polynomial still has exactly one natural witness tuple per y∈S.

The coefficients, witness arity, and finite cell decomposition depend on the supplied set/function descriptions. The result is a direct construction for Presburger sets with this polynomial output data. It is not a statement about arbitrary decidable sets or arbitrary Diophantine representations.

## 2. A genuinely disjoint finite clause partition

Use effective Presburger quantifier elimination to obtain quantifier-free membership formulas for the supplied semilinear cells. They are Boolean combinations of integer affine comparisons and congruences modulo fixed positive integers. Integer coefficients are obtained by positive denominator clearing where necessary.

Collect the integer affine forms occurring in comparisons as ℓ_1,...,ℓ_a, and the modular expressions as g_1 modulo m_1,...,g_c modulo m_c, with m_k>0. Enumerate every full outcome:

- for each ℓ_j, exactly one of ℓ_j<0, ℓ_j=0, ℓ_j>0;
- for each g_k, exactly one residue 0,...,m_k−1.

These outcomes partition all of Z^d. Each outcome determines the truth of every original cell formula. Retain it if at least one original cell contains it, and assign it the polynomial of the least such cell. All assigned polynomials agree with f on their assigned points; their values outside those points are irrelevant. Unsatisfiable outcomes can be deleted using Presburger decision, but need not be.

Rewrite ℓ>0 as ℓ−1≥0 and ℓ<0 as −ℓ−1≥0. A retained branch i is now a conjunction

    A_ir(y)≥0,     H_is(y)=0,     L_ik(y)≡r_ik (mod m_ik),

with all displayed forms integer affine, m_ik≥1 and 0≤r_ik<m_ik. The branches are pairwise disjoint. This is a partition of the spatial domain, not a parameterization by semilinear generators. In particular, no uniqueness of coefficients in a linear-set generating family is presumed.

Let B be the final number of retained branches, I the total number of inequality occurrences, H the total number of equality occurrences, and C the total number of congruence occurrences. These are literal occurrence counts over all final branches. The full-outcome construction gives

    B ≤ 3^a ∏_(k=1)^c m_k,
    I+H = aB,     C = cB,

before removing redundant atoms. The empty product is 1. This is a finite, effective, potentially very large bound, with no complexity claim about quantifier elimination.

## 3. The compact membership polynomial

For each branch i introduce a natural selector e_i. Introduce one natural slack u_ir for each inequality, and two natural variables q_ik^+,q_ik^- for each congruence. The latter form a canonical signed quotient pair; unrestricted difference pairs would not suffice.

The residuals are

    R_0 = Σ_i e_i − 1,
    R_ir = e_i A_ir(y) − u_ir,
    S_is = e_i H_is(y),
    Q_ik = e_i (L_ik(y)−r_ik) − m_ik(q_ik^+−q_ik^-),
    K_ik = q_ik^+ q_ik^-.

Define P as the sum of the squares of all these residuals. Every residual has integer coefficients and total degree at most two, even with the signed external coordinates included in total degree. Thus P∈Z[y,w] has ordinary total degree at most four. There is no variable exponent, exponential encoding, or parameter-dependent degree.

At a natural zero, R_0=0 forces exactly one selector e_i to be 1 and all others to be 0. In an inactive branch, R_ir=0 forces u_ir=0. Its congruence equations force q_ik^+=q_ik^-, and K_ik=0 then forces both to be 0. Consequently every inactive auxiliary is uniquely zero, without an additional gate or branch-coordinate copy.

In the active branch, R_ir=0 forces A_ir(y)=u_ir≥0 and determines the slack uniquely; S_is=0 imposes its equalities. The congruence balance determines the signed integer

    q = (L_ik(y)−r_ik)/m_ik.

The equation K_ik=0 forces its unique natural pair

    (q_ik^+,q_ik^-)=(max(q,0),max(−q,0)).

This handles negative quotients as well as positive ones and zero. Hence an active branch exists exactly when y lies in that branch. Pairwise disjointness determines the selector uniquely, and every other witness has just been shown unique. Conversely the described canonical witnesses make every residual zero whenever y belongs to a branch. A sum of real squares vanishes only when each residual vanishes, so the equivalence follows.

For B>0 the literal counts are

    W_mem = B + I + 2C,
    R_mem = 1 + I + H + 2C,

where R counts squared residual slots before omitting identities. For the full-outcome construction these give

    W_mem ≤ (1+a+2c)B,
    R_mem = 1+(a+2c)B.

For B=0 use P=1 and no witnesses. Its zero set is empty. If d=0, Z^0 and N^0 each consist of their single empty tuple and the same conventions apply.

## 4. Canonical function reconstruction and optional first-time output

### 4.1 No additional witness for reconstruction

Let f_i∈Q[y] be the assigned degree-at-most-two polynomial of branch i. At the unique membership witness, the selected branch is known. Therefore

    f(y)=Σ_i e_i f_i(y)

is a fixed rational polynomial expression in the external site and its canonical witness. It is integer-valued and nonnegative at every accepted natural witness. This reconstruction expression may have total degree three; that does not change the degree-four membership certificate. The next construction enforces the time value while preserving degree four.

### 4.2 Shared canonical square lifts

Introduce the following M=d(d+1)/2 natural variables:

    U_j  for 1≤j≤d,
    U_jk for 1≤j<k≤d.

Add the quadratic residuals

    J_j = U_j − y_j²,
    J_jk = U_jk − (y_j+y_k)².

For every signed integer y these residuals have exactly one natural solution. All lifted values are nonnegative even if coordinates or mixed products are negative. Since

    y_j y_k = (U_jk−U_j−U_k)/2,

each rational quadratic f_i(y) has an explicitly computed rational affine expression f_i^lin(y,U) agreeing with it at the square lifts. Choose one positive integer D clearing every coefficient denominator across all these affine expressions, including the halves introduced by polarization, and write

    f_i^lin(y,U)=F_i(y,U)/D,

with every F_i an integer affine polynomial. For an external t add the single residual

    T = D t − Σ_i e_i F_i(y,U).

This residual has integer coefficients and total degree at most two: F_i is affine, so multiplication by e_i does not produce a cubic monomial. Let P_time=P+ΣJ²+T². It is an ordinary degree-at-most-four integer polynomial. The unique active selector forces t=f_i(y)=f(y), and the other summands vanish. All shared square witnesses are canonical independently of branch choice. No inactive square variables are left undetermined.

The common denominator is essential for this pooled residual. Separately scaled branch numerators cannot be summed against an unrelated time scale. One could instead keep B separately gated time equations with separate denominators; the pooled version saves B−1 residual slots.

The exact literal counts are

    W_time = B+I+2C+M,
    R_time = 2+I+H+2C+M.

Unused square lifts may be omitted after choosing an explicit sufficient set, lowering M. For an affine or constant function on every branch one can take M=0. The displayed M is a universal sufficient bound for arbitrary quadratic cell polynomials in dimension d, not an assertion of optimality.

For t external one may take t∈N, or allow t∈Z: an accepted t automatically equals the nonnegative f(y). If the desired polynomial has y alone external, make t an additional natural witness. Then

    W_internal_time = B+I+2C+M+1,
    R_internal_time = R_time.

Each visited site still has exactly one witness tuple, which now includes its first-arrival time. The degree does not change when a variable is reclassified from external to existential. Empty S is again handled by P=1 with no witnesses or lifts.

## 5. Signed external sites versus all-natural external slots

The preceding theorem uses y∈Z^d as external polynomial inputs and w∈N^W as witnesses. Signed inputs cause no problem: natural slacks encode only valid inequalities, and congruence quotients have the canonical signed-pair construction above.

If every external slot is required to be natural, use external coordinates (Y_j^+,Y_j^-)∈N², substitute

    y_j=Y_j^+−Y_j^-,

everywhere and add the squared residual (Y_j^+Y_j^-)² for each j. The accepted encoding is precisely

    (Y_j^+,Y_j^-)=(max(y_j,0),max(−y_j,0)).

This replaces d signed external slots by 2d natural external slots, adds d squared residual slots, and adds no witnesses. Substitution is affine, so all pre-existing residuals remain degree at most two; the additional product residuals are also degree two. Thus the final ordinary polynomial still has degree at most four. Noncanonical external pairs are deliberately rejected. Inactive branch witnesses remain unique exactly as before.

## 6. First-arrival application to the assumed orbit normal form

Fix a CA F and finite input c satisfying the mass-at-most-four classification's hypotheses. When a unit symbol exists, let δ be its isolated displacement and let G=τ_(−δ)F; otherwise use G=F and δ=0. The queried site set is

    S_G = ⋃_(t≥0) supp(G^t(c)),
    τ_G(y)=min{t≥0 : y∈supp(G^t(c))}.

The output τ_G is actual absolute elapsed discrete time from the input, not a cycle index or a within-cycle time. The word 'stationary' describes its queried spatial coordinates, not a modified clock.

### 6.1 Expanding shuttle tail

The supplied phase normal form gives a Presburger relation Occ(y,n,h) describing occurrences at site y in cycle n and within-cycle offset h. All positions and offsets within a fixed phase are affine in the phase parameters, with affine/congruence domains. Cycles are half-open and have exact start times

    T_n=T_0+c n²+b n,     c>0.

First handle the finitely many sites visited before T_0, assigning each its earliest prefix time and removing these sites from the tail domain. On the remaining visited sites, select the least n having an occurrence and then the least h in that cycle. The graph of the pair (n_*(y),h_*(y)) is Presburger: assert an occurrence and the nonexistence of an occurrence with a lexicographically smaller (n,h). This is a legitimate Presburger formula, since no quadratic clock occurs in that selection relation.

A Presburger function on an integer lattice is effectively rational affine on a finite semilinear cover. An elementary justification suffices here. Decompose its graph into finitely many linear sets with generators (v_j,w_j), where v_j are input vectors and w_j output vectors. Any integer relation among the v_j must hold among the w_j: separate positive and negative coefficient parts to form two points of the same graph with identical input, and use functionality. Thus v_j↦w_j extends to a rational linear map on their rational span, and then to the ambient input space. The base point supplies an affine constant. Gaussian elimination computes these affine maps. The projected domains remain semilinear, and the common outcome refinement of §2 makes them disjoint without introducing generator witnesses.

Consequently

    τ_G(y)=T_0+c n_*(y)²+b n_*(y)+h_*(y)

is rational quadratic on an effective finite semilinear partition of the tail domain. Prefix singleton cells have constant outputs. The compiler therefore applies to the entire stationary-frame visited set, including the finite prefix. Choosing a canonical first occurrence is the essential additional dynamical step: merely existentially forgetting time in a certificate for all visits can leave infinitely many witnesses per site.

### 6.2 Affine, periodic, independent, finite and empty alternatives

The other normal-form alternatives give finitely many prefix occurrences and finitely many eventual phase rays

    y=p_i+n v_i,     t=a_i+P_i n,     n∈N,

with fixed integer data and P_i>0; the zero-velocity and vacuum cases are included. Thus the timed occurrence relation Occ(y,t) is Presburger. Its first-time graph is defined by

    Occ(y,t) and no t'∈N with t'<t and Occ(y,t').

The same graph argument makes τ_G piecewise rational affine on an effective semilinear partition. Overlaps between rays, repeated visits to stationary sites, and prefix-versus-tail overlaps are removed by first-time selection. The compiler applies with M=0. If the visited set is finite it also has a direct finite singleton-cell description. If the input is vacuum and S_G is empty, use P=1.

### 6.3 Precisely what frame restoration permits

If δ=0 these are certificates for F's ordinary site set and first visits. For affine/periodic/independent tails, restoring y_F=y_G+δt preserves the affine phase-ray form, so the original-frame occurrence relation is still Presburger and the same affine first-time argument applies.

For an expanding tail with arbitrary δ≠0, the original-frame visited set need not be semilinear. This packet claims no general original-frame single-witness corollary. Substituting y−δt into a stationary first-visit certificate is not a proof: a later repeat of a stationary site may create a new original-frame site, and it is omitted by stationary first-visit selection. In particular, the supplied stationary first-arrival theorem must not be relabeled as an original-frame theorem.

### 6.4 One shared cycle witness is enough in the expanding application

The general quadratic-output theorem in §4 uses up to d(d+1)/2 shared square witnesses. The actual expanding first-arrival function has additional structure that reduces this overhead to **one** natural witness.

Retain on each final disjoint tail cell the rational affine functions

    n_i(y)=n_*(y),     k_i(y)=T_0+h_*(y).

For a prefix first-visit singleton, instead set n_i(y)=0 and k_i(y) equal to that prefix first-arrival time. Both functions are integer-valued and nonnegative on their cells. All branches now share the identity

    τ_G(y)=c n_i(y)²+b n_i(y)+k_i(y),

with the same c,b. The prefix identity holds because n_i=0; no negative offset or extra tail selector is needed.

Introduce one shared N∈N. Choose a positive integer A clearing every coefficient denominator of all n_i, and let a_i=A n_i be integer affine. Choose a positive integer D clearing c,b and every coefficient denominator of all k_i, and let K_i=D k_i be integer affine. Add to the membership polynomial the squares of precisely these two residuals:

    U = A N − Σ_i e_i a_i(y),
    V = D t − Dc N² − Db N − Σ_i e_i K_i(y).

Both residuals have integer coefficients and total degree at most two. The unique selected branch fixes N=n_i(y); V then fixes t=τ_G(y). Conversely these values are natural and make the equations vanish. All inactive membership auxiliaries are already fixed to zero, and there are no branch-private clock auxiliaries. Thus one obtains the sharper literal counts

    W_expanding_time = B+I+2C+1,
    R_expanding_time = 3+I+H+2C.

Making t another natural witness adds exactly one to W and leaves R unchanged. First arrival may also be reconstructed from the membership witness alone as in §4.1, needing no additional clock variable. Affine-tail external-time certificates continue to use the even smaller §4 construction with M=0.

Only the clock overhead is dimension-independent here. The clause and atom counts, and hence the full polynomial's arity and coefficients, continue to depend on the entire fixed CA and input. The general piecewise-quadratic output theorem without this shared-clock structure still uses its separate square-lift bound.

### 6.5 Fixed Presburger observation schemas: configurations and patterns

The same argument applies to a fixed observation schema, not only one occupied site. Let z∈Z^q be a fixed finite tuple of observation parameters. Suppose the predicate saying that observation z holds of a stationary-frame finite configuration is Presburger in z and the configuration's finite occupied-site/label data. The rule, input, schema, and q are all fixed.

The phase description has a finite list of labels and affine occupied-site coordinates on each phase. Substitute these into the observation predicate and quantify the phase parameters. This gives an effective Presburger occurrence relation Occ(z,n,h) within the half-open expanding cycles. It permits overlaps and many occurrence witnesses: only its Boolean truth is used. For affine tails one obtains a Presburger Occ(z,t) directly.

A finite prefix can satisfy infinitely many parameter values z, so its treatment must differ from the site-only singleton shortcut. At every prefix time t let P_t(z) be the Presburger observation predicate evaluated on the actual configuration at t. Assign time t to the disjoint Presburger domain

    P_t(z) and not P_s(z) for every 0≤s<t.

These finitely many sets contain all parameter values with a prefix hit. Exclude their union before minimizing (n,h) on the tail. The resulting first-cycle and first-offset functions are again Presburger and therefore rational affine on effective semilinear cells. On prefix cells set n_i=0,k_i=t; on tail cells use n_i=n_*(z),k_i=T_0+h_*(z). The shared-counter compiler in §6.4 now gives a single natural witness exactly when observation z ever holds, with its first absolute hit time canonically reconstructed, external, or included as one further natural witness. The same clause/atom counts apply with the external tuple z in place of y. For affine tails the affine-time version applies.

Two concrete schemas meet these conditions:

1. **Complete finite-configuration targets.** Use external site count m≤4, fixed nonzero label codes, and at most four signed site-coordinate slots, strictly lexicographically sorted and padded with zero labels/coordinates beyond m. A finite Boolean formula checks cardinality, labels, coordinate equality with all phase support sites, ordering, and padding. All these conditions are Presburger. Thus exact untimed stationary-frame configuration reachability has a quartic with an empty or singleton natural witness fiber for each canonical target, with the first reachability time recoverable. This is a first-hit construction; simply dropping external time from Report29's all-occurrence certificate would not establish it.

2. **Anchors of a fixed finite pattern.** Fix the finite pattern's offsets and prescribed symbols, including any zeros; let z be its anchor. For each nonzero pattern entry require one of the finitely many occupied sites with the matching label at z+offset; for a zero entry require no occupied site there. The finite Boolean combination is Presburger. Hence the set of anchors at which this fixed pattern ever occurs has the same canonical first-hit quartic. The pattern is fixed when the polynomial is compiled, rather than supplied as an arbitrary unbounded encoded external pattern.

This extension makes **no quadratic spatial growth claim** for the first-hit time as a function of z. For example, a wholly zero fixed pattern can hold at infinitely many distant anchors already at time zero. The theorem concerns semilinear first-hit domains, piecewise-quadratic first-hit functions, and canonical certificates. The expanding-tail result continues to concern stationary-frame configurations only; arbitrary original-frame restoration is not asserted.

## 7. Relation to Report29 and scope

Report29's constant-term-lifting compiler already converts disjoint quadratic parameter charts with canonical natural variables into quartic sums of squares. One valid alternative proof is to copy signed site coordinates canonically into every branch, add canonical congruence quotient pairs, and invoke that compiler. The present external-input affine gating avoids those branch-coordinate copies; shared square lifts handle the optional quadratic output. Both are elementary algebraic constructions.

The new application is the canonical selection of a first visited occurrence from the reviewed sparse orbit normal form. The general Presburger quantifier-elimination ingredient is standard, and the quartic sum-of-squares mechanism is explicit. No claim of novelty or priority is made for these ingredients.

All dynamical data, cell formulas, coefficients, B,I,H,C and hence witness arities are effective for the fixed CA and fixed input under the normal-form hypotheses. There is no uniform-over-input arity bound here, no generic single-fold MRDP theorem, no finite-foldness inference from bare decidability, no real/rational-witness exactness assertion, and no efficiency claim. A constant-degree polynomial may still have enormous coefficients and many variables.

## 8. Sources and provenance

The local inputs were read only:

- `../sparse-orbit-geometry-research-20261003/PROOF.md`, especially §§1–5; SHA-256 `3f05b484cd3c0035422df431f571bb2b56c85a31d5f49ae681033ffb2ca6e4fa`
- `../sparse-orbit-geometry-research-20261003/counting-review.md`, especially §8; SHA-256 `27a50b857d4a26ce21e24cac27694ff4a2addef049d027c9ccce52c20b49bf39`
- `../dimension-independent-threshold-release-20261003/report29.tex`, Appendix 'Canonical timed quartic certificates'; SHA-256 `1e4b9cb159801ce06d283a851ce2c47925610a27f7914d0ed8c8e3902874cedc`

For the standard Presburger elimination/semilinear background: Kevin Woods, *Presburger arithmetic, rational generating functions, and quasi-polynomials*, Journal of Symbolic Logic 80 (2015), 433–449, Theorem 3.2 and §4.1, primary full text https://arxiv.org/pdf/1211.0020 (checked 3 October 2026). The present coefficient and witness constructions and their uniqueness proofs are provided in full above; they do not depend on a Diophantine finite-fold theorem.
