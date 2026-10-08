# Independent mathematical audit of the checkerboard Potts extension

## Arbitrary-order frontier bound

Let D be a connected plane knot shadow, with n>0 crossings. Choose one
checkerboard color. At a crossing prefix P, call a selected-color face mixed
if it is incident with at least one processed and one unprocessed crossing;
count it by f. Let w count shadow edges with exactly one endpoint in P.

Each face has one cyclic boundary dart walk, even if it visits a crossing
multiple times. Write the processed/unprocessed status of its successive
crossing incidences around this walk. A mixed face has at least two status
changes. Every change traverses a cut shadow edge, and every cut shadow edge
belongs to exactly one selected-color face boundary. Therefore 2f<=w.

The argument allows Tait loops, parallel edges, shadow articulation points,
and repeated crossing incidences on a face. A loop shadow edge is never a cut
edge, as it has the same crossing at both endpoints. An edge label occurring
twice at one crossing consequently cancels when the frontier is toggled.

Connectedness is essential: in a disconnected projection a single face can
have several boundary walks, some wholly processed and others wholly
unprocessed. Then it is mixed with no status transition. The public one-knot
diagram precondition avoids this obstruction.

## State-circle identity

For the selected Tait graph G=(V,E), let v=|V| and k(S) count components of the
spanning subgraph (V,S), including isolated vertices. The regular neighborhood
of this plane subgraph has Euler characteristic v-|S| and has k(S) planar
components. Hence its number of boundary circles is

    c(S)=2k(S)-v+|S|.

Those are precisely the smoothing-state circles under the convention that
the omitted crossing smoothing caps the selected-color corners. Loops and
parallel edges cause no problem: the regular neighborhood stays planar.

## Normalization and its parity

Put x=A^4 and delta=-A^2-A^-2=-(x+1)/A^2. Let b_e=A^(s_e), s_e in {+1,-1},
be the omitted smoothing weight; the included weight is a_e=A^(-s_e).
With s=sum s_e and

    v_e=delta*a_e/b_e in {-1-x,-1-x^-1},

the unnormalized bracket with a circle valued at delta is

    bracket = delta^(-v) A^s Z_G(delta^2,{v_e}).

For writhe w and normalized Jones polynomial V(A^-4),

    V(A^-4) = (-1)^(w+v+1) A^E Z_G/(x+1)^(v+1),
    E=s-3w+2(v+1).

For a knot E is divisible by four. One elementary check is as follows. For
any state sigma, write s_sigma for its smoothing-weight exponent and c_sigma
for its circle count. The value

    s_sigma-3w+2(c_sigma-1) modulo 4

is unchanged by flipping one smoothing, because the two changing quantities
are +/-2 and twice +/-1. In the oriented Seifert state s_sigma=w, and
c_sigma-1 has the same parity as w: both have the parity of n. Thus the value
is zero modulo four. For the all-omitted state c_sigma=v, and E differs by 4.
For a link with ell components, the residue instead is 2(ell-1) modulo four.

For each integer q>=5 impose x^2-(q-2)x+1=0, so delta^2=q. This polynomial is
irreducible over Q: its discriminant (q-2)^2-4 lies strictly between the
consecutive squares (q-3)^2 and (q-2)^2. The equal-spin Potts edge weight is

    1+v_e=-x^(-s_e).

Pair arithmetic in Z[x]/(x^2-(q-2)x+1) is exact. Unequal normalized values
certify knottedness; equal values are inconclusive. Exact algebra removes
modular collisions, but not collisions of this polynomial specialization.

## Why quotienting spin names is sound

A state is a restricted-growth word recording equality classes of active
spins. Its coefficient is the SUM over all labelled active assignments with
that equality pattern, together with all assignments to forgotten vertices.
It is not the value per labelled assignment. When introducing a spin, each
already used class has one extension, while a new class has q-k choices if k
classes are currently present. Multiply only the new-class branch by q-k.
After forgetting vertices, canonicalize the remaining pattern and add all
coefficients. This is exactly the pushforward of the labelled-assignment sum.
Even if a new spin happens to use a label once used on a forgotten vertex,
there is no additional constraint: every edge incident with that vertex was
already processed. Hence aggregation does not lose any future dependency.

The number of orbit states on f vertices is sum_(j=0)^q S(f,j), at most q^f.
At one step at most two new Tait vertices are introduced. Thus the temporary
unquotiented state count is at most q^(f+2), and q is fixed in the claimed
2^O(w) bound. For q=6 the width factor is at most 6^(w/2+2).

## Explicit coefficient lengths

For a+bx let norm=|a|+|b|. Multiplication by -x or -x^-1 has induced 1-norm
at most q-1. Every coefficient after i crossing steps is an aggregate of a
subset of the q^I labelled assignments on the I introduced vertices, so

    norm(coefficient) <= q^I (q-1)^i <= q^v (q-1)^n.

This also bounds transient partial sums in the following table: each history
is counted once, and the triangle inequality does not rely on cancellation.
Consequently each magnitude has at most

    floor(v log_2 q + n log_2(q-1))+1

bits. Since a connected n-edge Tait graph has v<=n+1, this is O(n log q),
and for q=6 the simpler bound 5n+4 is valid. The normalization comparison
has norm at most (q-1)^|E/4| q^(v+1), also O(n log q) bits. The exponent obeys
|E/4| <= n+(v+1)/2. Multiplication by the equal-spin edge weight and an
extension multiplicity <=q(q-1) uses only O(n log q)-bit additions and small
integer multiplications for fixed q.

## An infinite blind family at q=5 and its removal at q>=6

Let W_m be the closure of (sigma_1 sigma_2^(-1))^m. Its strand permutation is
a 3-cycle raised to m, so it is a knot exactly when gcd(m,3)=1. The exponent
sum is zero. The classical three-braid Jones/Burau identity gives

    V_(W_m)(t)=t+t^-1+tr(M(t)^m),
    M(t)=[[1-t,-t^-1],[1,-t^-1]],
    det M=1, tr M=1-t-t^-1.

This identity is established literature, not a new result here. A modern
primary source is Alsukaiti--Chbili, "Alexander and Jones polynomials of
weaving 3-braid links and Whitney rank polynomials of Lucas lattice",
Heliyon 10 (2024), e28945, DOI 10.1016/j.heliyon.2024.e28945,
Theorem 3.3 and its m=1 specialization (their variable s=-t):
https://pmc.ncbi.nlm.nih.gov/articles/PMC11004560/.

At the q-state quadratic specialization, t+t^-1=q-2 and tr M=3-q. If q=5,
the characteristic polynomial of M is (lambda+1)^2. Its eigenvalue sum,
or the two-term trace recurrence, gives tr(M^m)=2(-1)^m. Thus

    V_(W_m)=3+2(-1)^m.

Every odd m with m>=5 and gcd(m,3)=1 is a nontrivial knot invisible to this
exact q=5 specialization. This is an exact algebraic collision, not a prime
modulus accident.

If q>=6, put a=q-3>=3 and define

    U_0=2, U_1=a, U_(m+1)=a U_m-U_(m-1).

Then tr(M^m)=(-1)^m U_m, and U_m is strictly increasing for m>=1: U_2=a^2-2>a,
and U_m>U_(m-1)>0 implies U_(m+1)>(a-1)U_m>=2U_m. Hence

    V_(W_m)=a+1+(-1)^m U_m.

For even m>=2 this is greater than one. For odd m>=3, U_m>a and the value
is less than one. Therefore every W_m that is a knot with m>=2 is rejected
by every exact q>=6 specialization. In particular this also proves that the
q=5-blind members above are nontrivial, independently of a classification.
W_1 is the unknot and has value one for all q, as required.

The q>=6 theorem removes this specific infinite blind family. It does not
prove that q=6 detects every knot, nor that finitely many evaluations decide
unknottedness in general. Existing three-braid preprocessing already decides
this family; it is an adversarial filter audit, not an end-to-end speed gain.

## Code audit status

The initial q=5 versions of potts.py and potts_exact.py had correct algebra,
normalization, orbit aggregation, and resource-result semantics. The one
observed small issue was that modular potts.py failed to forward its check
callback into its internal best_scan_order call; this was reported to root.
An independent full-smoothing Laurent-polynomial oracle is provided in
check_potts_independent.py, with its execution record beside it.
