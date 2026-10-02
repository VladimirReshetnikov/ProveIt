# Independent audit: bipartite directed supports at physical-shore order

Audit date: October 1, 2026.

## Verdict

**APPROVED**, with the positive-weight qualification on saturation stated below.
The multivariate support polynomial in the producer's
`BIPARTITE_ORIENTATION_LEMMA.md` is Lorentzian at the cardinality of a physical
bipartition shore. The conclusion permits arbitrary directions, opposite arcs,
physical overlap of tail/head role-cover sets, and independent nonnegative
activities for all tail and head roles. It counts ordered endpoint supports,
not matchings. It does **not** establish normalization by actual matching rank
when that rank is smaller than the chosen shore.

The core merge is exactly an already-proved Lorentzian operator: Brändén--Huh
Lemma 3.3, with the retained variable renamed. The producer's independent
algebraic-symbol justification through Theorem 3.2 is also valid.

## 1. Precise setting and counting object

Let the physical vertex set be the disjoint union `C ∪ I`, with every directed
arc crossing the bipartition. Both directions on an underlying edge are allowed.
There are no loops or arcs internal to either shore. Let `u_v,v_v ≥ 0` be the
activities for using physical vertex `v` as a tail or a head, respectively.

A support is an ordered pair `(S,T)` of disjoint sets, with `|S|=|T|`, admitting
a directed matching from all of `S` onto all of `T`. Its weight is
`∏_{s∈S}u_s ∏_{t∈T}v_t`. Distinct matching witnesses do not increase this weight.

The claimed polynomial is

    F_C(z,x) = Σ_(feasible S,T) u^S v^T
                ∏_(c∈C\(S∪T)) z_c ∏_(i∈I∩(S∪T)) x_i.

Every matching of size `k` uses exactly `k` vertices of each shore, so every
monomial has total degree `|C|`. The empty support contributes `∏z_c` with
coefficient one, regardless of activities. Different ordered supports may map
to the same displayed monomial; their weights are correctly added.

## 2. Exact support bijection

For the outgoing transversal matroid, give every position `c∈C` its private
dummy `a_c`; the other ground elements are exterior vertices with adjacency
given by arcs `c→i`. All dummies form a basis, hence the rank is exactly `|C|`.
A set consisting of physical exterior subset `R` and dummies `C\U` is a basis
exactly when `|U|=|R|` and `U` can match to `R`. The dummies force their own
positions; the remaining positions are exactly `U`. Thus a basis records one
endpoint pair `(U,R)`, not a choice of bijection.

The incoming matroid similarly records `(L,W)`, where `L⊆I`, `W⊆C`, and the
arcs go from `L` to `W`; its dummy set is `C\W`.

After identifying the two exterior variable copies, multiaffine-part extraction
removes precisely `R∩L≠∅`. The core merge removes precisely `U∩W≠∅`.
Each surviving pair of bases therefore determines

    S = U ∪ L,    T = R ∪ W.

Conversely, a directed matching for a feasible support splits into its `C→I`
and `I→C` edges. Its four endpoint intersections determine `(U,R,L,W)` uniquely,
independently of the matching witness. The two resulting bases exist and are
unique as ground-set subsets. This is a genuine bijection of surviving basis
pairs with ordered supports.

Opposite arcs cause no problem: on a single physical edge they give two
different nonempty supports. A one-directional complete `K_{2,2}` has two
perfect-matching witnesses for its full support, but only one full-support
term. Both cases are explicit tests in the verification program.

## 3. Finite bounded-degree operator audit

Write `r=|C|`, `m=|I|`. The two basis polynomials have degrees `r` and `r`.
After exterior identification their product has coordinate bounds one on all
`2r` dummy variables and two on the `m` exterior variables. Its multiaffine part
is homogeneous of degree `2r`; all coordinates then have bound one. Since the
dummies were already squarefree, taking the full multiaffine part is exactly
the required exterior-only truncation.

At a merge, let `a,b` be the chosen two dummy variables, let `y_1,…,y_q` be all
untouched coordinates, and introduce a fresh `z`. The operator is a linear map
between finite multiaffine spaces

    T: R_(1,…,1)[a,b,y] → R_(1,…,1)[z,y],
    T(ab)=z, T(a)=1, T(b)=1, T(1)=0,

acting coefficientwise in `y`. Every nonzero image of a monomial has input
degree minus one. Zero images are permitted by the definition of homogeneous
operator in the source; they do not violate degree homogeneity. Coefficients
remain nonnegative, although distinct terms can merge and add.

For input dual coordinates `A,B,Y_j`, the full algebraic symbol is exactly

    (z + A + B) ∏_j (y_j + Y_j).

All coordinate bounds are one here, so the binomial factors in the general
symbol definition are all one. The symbol has degree `q+1`, which equals the
sum of the input bounds minus one. It is homogeneous and real stable with
nonnegative coefficients; in particular it is Lorentzian. Theorem 3.2 applies
directly. Alternatively, rename `a=w_1`, `b=w_2`; Lemma 3.3 gives this precise
operator with `ab→b`, followed by the harmless renaming `b→z`.

The input remains multiaffine after each merge, so the same argument can be
iterated. After `r` merges the degree is exactly `r`. The all-dummy term survives
every stage, so no actual intermediate or final output in this construction is
zero. Introducing distinct `z_c` first and only later identifying them avoids
any possible ambiguity about spectator-coordinate bounds.

Theorem 3.4 is also usable, because the full stable symbol certifies stability
preservation on the finite bounded-degree domain and nonnegative-coefficient
preservation is immediate. No hypothesis requires the matroid basis
polynomials themselves to be stable.

## 4. Activities, including zero

The producer's argument for positive activities is exact: scale the outgoing
dummy variable by `1/u_c` and multiply by `∏u_c`; the surviving coefficient is
then weighted by the used core tails, rather than the unused ones. Exterior
head variables receive factors `v_i`. The incoming factor is analogous.
These are positive diagonal substitutions and positive scalar multiples.
Sending positive activities to arbitrary nonnegative values is legitimate:
the final coefficients are explicit finite polynomials in the activities, the
Lorentzian cone is closed, and the coefficient-one empty term survives.

There is also a direct alternative avoiding division and limits. Scale only
the exterior roles in the two factors. At each physical core vertex use

    T_c(ab)=z_c, T_c(a)=v_c, T_c(b)=u_c, T_c(1)=0.

Only `a` means the core tail role is unused and its head role is used, explaining
the factor `v_c`; only `b` explains `u_c`. Its full symbol is

    (z_c + u_c A + v_c B) ∏_j (y_j + Y_j).

It is again a nonnegative stable homogeneous symbol, including when either or
both activities vanish. Its `z_c` coefficient remains one. The same Theorem
3.2 proves the weighted conclusion directly. This alternative independently
confirms the activity bookkeeping.

## 5. Normalization and boundaries

The specialization `z_c=s, x_i=t` is a nonnegative linear substitution. It gives

    H_C(s,t)=Σ_k γ_k s^(r−k)t^k,    r=|C|,

with `γ_k` equal to the stated weighted ordered-support sum. Consequently

    k(r−k) γ_k² ≥ (k+1)(r−k+1) γ_(k−1) γ_(k+1)

for `1≤k<r`, with no internal positive-coefficient gaps. Interchanging the
shores proves the analogous result at order `|I|`, so the smaller shore order
is available.

Actual degree is the maximum matching size in the subrelation whose arcs
`a→b` satisfy `u_a v_b>0`. Therefore actual-degree normalization follows from
this theorem when a **positive-weight** matching saturates the chosen smaller
shore. Saturation in the original unweighted relation is insufficient if zero
activities destroy all such matchings. The producer added this qualification
to the overlap consequence after the audit request; it was already present in
the main theorem.

For a disconnected physical graph, components may be flipped independently.
Choosing each component's smaller shore yields the still-valid order
`Σ_components min(part sizes)`, placing isolated vertices on the other shore.
This remains a shore-order result, not a general matching-rank theorem.

For clarity, cancellation of a homogenizing variable is not a general
Lorentzian operation. The cubic

    s³ + 3s²t + 3st²

is Lorentzian (its binomial-normalized sequence is `1,1,1,0`), whereas division
by `s` gives `s²+3st+3t²`, whose quadratic Hessian has two positive eigenvalues
(determinant `3`). This example is only a warning about the operation; it is not
asserted to arise from the graph construction.

For overlapping role-cover sets `P,Q`, the hypotheses must include that
`C=P∪Q` is physically independent. The role-cover condition forbids arcs
within its complement, so these conditions really do give a physical
bipartition. Beginning with only the necessary role dummies yields initial
degree `|P|+|Q|` and exactly `|P∩Q|` merges, hence final degree `|P∪Q|`.
Internal physical core arcs are outside the theorem.

## 6. Independent finite verification

`audit_bipartition.py` compares a direct directed-matching enumeration,
deduplicated by ordered support, against a separate Hall-condition enumeration
of the two transversal-matroid basis families. It uses exact integer activity
weights, including zero. It also checks symmetric basis exchange for the
multivariate support and uses exact rational congruence elimination to count
positive eigenvalues of every relevant quadratic derivative Hessian.

Results in `verification.json`:

- 5,120 weighted directed-relation cases
- All 4,096 directed subrelations on `K_{2,3}`, plus smaller exhaustive suites
- 700 seeded random cases through `K_{4,4}`
- 100,103 enumerated ordered-support instances
- 13,152 exact quadratic-Hessian inertia checks
- Exact construction equality, shore degree, empty coefficient, exchange,
  binomial-order ULC, and Hessian tests all pass

These checks are sanity tests accompanying the proof, not replacements for it.

## 7. Primary source checked

Petter Brändén and June Huh, *Lorentzian polynomials*, Annals of Mathematics
192 (2020), 821–891, DOI 10.4007/annals.2020.192.3.4.

https://annals.math.princeton.edu/wp-content/uploads/annals-v192-n3-p04-s.pdf

Relevant locations verified in the published primary text: Theorem 2.10
(nonnegative substitutions), Example 2.26 (binary characterization), Corollary
2.32 (products), bounded-coordinate operator and symbol definitions on printed
p. 850, Theorem 3.2 (symbol criterion), Lemma 3.3 on printed p. 851 (the exact
merge), Theorem 3.4 (stable-preserver implication), Corollary 3.5
(multiaffine extraction), and Theorem 3.10 (matroid bases).

No assertion of real-rootedness, arbitrary-edge-weight extension, nonbipartite
extension, or unrestricted actual-rank normalization is approved by this audit.
