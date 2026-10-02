# Independent audit: stable transversal seed with many pendant heads

Date: October 1, 2026.

## Verdict

**APPROVED.** The conditional HPP criterion and its explicit all-rank
singleton/universal-neighborhood subfamily are correct. They prove real
stability of the signed physical monomer polynomial and hence real-rootedness
and Newton inequalities at the support polynomial's **actual surviving degree**,
including degree drops caused by zero activities. Internal physical core arcs,
opposite arcs, arbitrarily many distinct pendant-tail hubs, and physical role
overlap do not invalidate the argument.

This is a separate stronger conclusion under its extra hypotheses. It does not
promote the earlier general bipartite Lorentzian theorem from shore order to
actual rank. The HPP seed assumption and the indegree bound on every head
outside `Q` are essential stated hypotheses and have not been removed.

Audited source: `PENDANT_HEAD_HPP_CRITERION.md`, SHA-256
`2fabfaabf621e2c25bdb24dd1612bfabb24341f4be4b340f618dc25d0e039154`.

## 1. Exact seed identification

Let `Q⊆V`, `q=|Q|`, and split all physical vertices into independent tail and
head copies. The seed has all tail copies and only the head copies in `Q`.
The transversal matroid has positions `Q`, one private dummy `d_j` for each
position, and one ground element for each tail copy. The private dummies make
the rank exactly `q`, even when some or all tails are loops of the matroid.

A ground subset consisting of tail set `S` and dummy set `Q\T` is a basis
exactly when `|S|=|T|` and `S` matches into `T`. The dummies force their own
positions, so the remaining positions are precisely `T`. Each basis occurs
with coefficient one, independently of how many bijections realize it.

At this stage `S` and `T` need not be disjoint as physical label sets: their role
copies are distinct. Disjointness is imposed later by the physical merge.
Prematurely restricting to physically disjoint seed supports would not be the
matroid construction proved here.

For positive activities, the seed identity is exactly

    μ₀(a,b) = (∏_(i∈V) a_i)(∏_(j∈Q) v_j)
                 B_M(x_i=−u_i/a_i, d_j=b_j/v_j).

A basis contributes

    (−1)^|S| u^S v^T ∏_(i∉S) a_i ∏_(j∈Q\T) b_j.

Squarefreeness cancels every denominator in the displayed identity. Thus it is
an ordinary real polynomial, with the required endpoint-product weights and
no matching-witness multiplicity. When all monomer arguments are in the upper
half-plane, so are `−u_i/a_i` and `b_j/v_j`. The assumed stability of `B_M`
therefore proves stability of the seed. The prefactors are nonzero there.

## 2. Pendant insertion at arbitrary hubs

For `j∉Q`, the hypothesis concerns its **incoming degree**, equivalently the
degree of its head copy in the role graph. If that degree is zero, multiply by
its unused-head monomer `b_j`. If its unique parent is `i`, the exact recurrence
is

    μ_new = b_j μ_old − u_i v_j ∂_(a_i) μ_old.

Every support using head `j` must contain the forced edge `i→j`. Removing that
edge leaves a unique old support with unused tail `i`. Conversely, every such
old support extends in exactly one way. The derivative selects terms containing
the unused-tail monomer; it neither chooses nor counts a seed matching witness.

All intermediate role monomer polynomials are multiaffine. Therefore, with
`w=u_i v_j≥0`, the recurrence is identically

    μ_new = b_j μ_old(a_i−w/b_j, other arguments).

For upper-half-plane `b_j`, the quantity `−w/b_j` has nonnegative imaginary part.
The shifted tail argument remains strictly in the upper half-plane, so this
formula proves stability directly. There is no restriction on how many times
the same hub occurs or on how many different hubs occur. A tail used in a prior
insertion no longer has its `a_i` monomer and cannot be used again.

## 3. Physical overlap and merge

After every head copy exists, each physical vertex has two monomer coordinates
`a_i,b_i`. The coefficientwise map

    a_i b_i→z_i,  a_i→1,  b_i→1,  1→0

keeps both-role-unused vertices, suppresses the one unused role of a vertex
used exactly once, and deletes exactly the terms using that physical vertex
in both roles. This works equally for vertices in `P∩Q`, heads that are also
tail hubs, opposite arcs, and cycles.

For a multiaffine polynomial `f=Aab+Ba+Cb+D`, with coefficient polynomials in
the remaining variables, the image is `Az+B+C`. It equals

    [∂_t f(t,t,other variables)]_(t=z/2).

Diagonal identification, differentiation, and positive scaling preserve
stability, allowing an identically zero derivative in general. Here the
all-unused monomial has coefficient one and survives every merge, excluding
zero outputs. This elementary argument proves **real stability**, not merely
Lorentzianity. Equivalently the full finite-domain symbol is
`(z+A*+B*)∏(y_j+Y_j*)`, a stable product of linear factors.

The final role sets are exactly the feasible ordered disjoint physical
supports. The set of heads outside `Q` uniquely fixes its forced pendant tails,
and subtracting these tails leaves the uniquely determined seed endpoint pair.
Consequently the construction counts each final support once. Distinct ordered
supports with the same unused physical set appropriately contribute to the
same monomial; all have the same matching size and sign.

The result is precisely

    μ_D(z)=Σ_(feasible S,T) (−1)^|S| u^S v^T
                               ∏_(i∉S∪T) z_i.

## 4. Explicit arbitrary-rank HPP seed

For `q≥2`, suppose every tail neighborhood in `Q` is empty, a singleton, or all
of `Q`. For each position `j`, form the disjoint singleton parallel class
consisting of `d_j` and the tails whose neighborhood is `{j}`. Let its variable
sum be `r_j`. Keep a separate variable for each universal tail. Empty-neighborhood
tails are matroid loops and never belong to bases.

Then exactly

    B_M = e_q(r_1,…,r_q,g_1,…,g_m).

A `q`-element ground subset is matchable precisely when no two selected
singleton elements come from the same parallel class. The singleton choices
force distinct positions; any selected universal tails then match bijectively
to the remaining positions. Expansion of the elementary symmetric polynomial
chooses classes and elements once, so a basis coefficient is one, even when
the universal elements admit many assignments.

For example, three universal tails matched to three positions have six
witnessing bijections but just one all-tail basis monomial. In a one-directional
`K_{3,3}` the physical support polynomial is `1+9t+9t²+t³`, not the usual matching
enumerator.

If `N=q+m`, differentiating `∏_(j=1)^N(s+y_j)` exactly `N−q` times and setting
`s=0` gives `(N−q)!e_q(y)`. This establishes stability; the positive scalar
factor is divided out and introduces no basis multiplicity. Substituting the
nonnegative class sums preserves stability. The dummy coefficient one in
every class avoids any degenerate zero class.

For `q=1`, nonempty singleton and universal neighborhoods coincide and must
not be listed twice: the seed polynomial is simply linear. For `q=0`, the seed
matroid polynomial is `1`. Both boundaries are handled separately in the
producer's note and in the verifier. In a loopless relation a tail physically
inside `Q` cannot have universal neighborhood `Q`; the statement explicitly
acknowledges this restriction.

## 5. Zero activities and actual-degree normalization

To include zero activities, replace each activity by a positive approximation.
Every final coefficient is a finite polynomial in the activities. Coefficient
convergence is therefore uniform on compact sets, and Hurwitz' theorem gives
a stable limit or the zero polynomial. The surviving all-unused monomial
`∏z_i` has coefficient one, so the limit is never the zero polynomial. This
argument does not substitute into a formula containing `1/v_j` at `v_j=0`.

Let `n=|V|` and let `r` be the actual degree of `Γ_D`. Then

    μ_D(s,…,s) = Σ_(k=0)^r (−1)^k γ_k s^(n−2k).

This is a nonzero monic real-rooted polynomial. Its nonzero roots occur in
opposite pairs, so it factors as

    s^(n−2r) ∏_(j=1)^r (s²−λ_j),    λ_j>0.

It follows by coefficient comparison that

    Γ_D(t)=∏_(j=1)^r (1+λ_j t).

Thus all zeros are strictly negative, and Newton's inequalities use precisely
the actual surviving degree `r`, even after zero activities lower that degree.
For `r=0`, the polynomial is `1` and the root and inequality assertions are
vacuous. No cancellation principle for Lorentzian homogenizations is invoked.

## 6. Independent exact verification

`check_pendant_seed.py` uses two distinct methods:

1. Enumerate directed physical matchings and deduplicate their ordered
   endpoint supports
2. Enumerate seed bases by Hall conditions, apply the pendant differential
   recurrences to sparse role-monomer polynomials, and perform physical merges

The resulting multivariate signed polynomials agree exactly. A separate
elementary-symmetric class expansion matches the Hall basis set. All tested
univariate polynomials pass exact negative-root and actual-degree Newton
checks; higher-degree root tests use rational isolating intervals with
multiplicity. The program additionally samples exact integer Rayleigh
differences of the multiaffine signed physical polynomial.

`verification.json` records:

- 1,884 weighted cases
- All 1,024 eligible loopless relations on four physical vertices with `|Q|=2`
- 860 random cases with `|Q|` ranging from zero through five
- 1,734 cases with zero activities
- 880 cases in which zero activities lower the matching degree
- 53,076 support instances versus 55,327 matching-witness instances
- 70,752 exact Rayleigh evaluations, all nonnegative
- Explicit empty-set, all-zero-activity, rank-zero, rank-one, and universal-tail
  multiplicity boundaries

The producer's non-bipartite overlapping example was independently reproduced:
`V={0,…,8}`, `P={0,1}`, `Q={1,2,3}`, with arcs `0→1,2,3,7`, `1→0,2,8`, and
`4,5,6→1,2,3`, has

    Γ_D(t)=1+16t+47t²+31t³+4t⁴.

It has 99 ordered supports but 163 matching witnesses and contains the
underlying triangle `0,1,2`. This confirms that the new theorem genuinely
includes some internal-core cases outside the bipartite physical theorem.
Finite checks corroborate rather than replace the unbounded proof.

## 7. Source and scope

Primary source checked: Julius Borcea and Petter Brändén, *The Lee–Yang and
Pólya–Schur programs. I. Linear operators preserving stability*, Inventiones
Mathematicae 177 (2009), 541–569.

https://arxiv.org/pdf/0809.0401

The bounded-coordinate symbol convention and sufficient stable-symbol criterion
are in Theorem 1.1; Theorem 1.6 supplies Hurwitz closure; Lemma 1.7 supplies
real specialization, positive scaling, reciprocal change, and diagonal
identification. The insertion and merge identities above give direct proofs
for the operators used here.

Brändén--Huh Lemma 3.3 identifies the same merge as a Lorentzian preserver, but
that fact alone would not establish stability of these nonhomogeneous signed
polynomials. The present proof correctly uses stable operations instead.

The audit does not approve arbitrary non-HPP transversal seeds, uncovered
heads with multiple parents, arbitrary edge-weight substitutions in the seed,
or a general five-role-cover theorem.
