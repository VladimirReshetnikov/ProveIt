# A rank-three Rayleigh proof for all same-orientation three-core relations

Status: structural proof prepared for external audit. This supersedes the unfinished moment-cone approach as the proposed proof of the whole same-orientation branch.

## Theorem

Let a loopless directed relation have a three-vertex set C={0,1,2} and an independent exterior X. Allow arbitrary internal arcs on C, and arbitrary arcs from C to X, but no arcs from X to C. Give every vertex arbitrary positive independent tail/head activities. Then its disjoint-support gamma polynomial is rank-ULC with respect to its actual degree. The order dual has the same conclusion. Transitivity is not required.

The actual degree is at most three. Degree at most two and the first cubic Newton inequality follow from the universal weighted first-gap theorem. We prove gamma_2^2>=3 gamma_1 gamma_3.

## 1. Exterior coefficients and the rank-three matroid input

For the exterior bipartite relation, define:

A_i = sum_(x in N_i) v_x;
B_ij = sum_(distinct exterior head pair admitting a matching from {i,j}) v_x v_y;
C = sum_(exterior head triple admitting a matching from {0,1,2}) v_x v_y v_z.

Each head set is counted once, irrespective of matching multiplicity. We use two inequalities, for distinct i,j,k:

B_ij B_ik >= A_i C,                         (1)
A_k B_ij >= C.                              (2)

For (1), adjoin three private dummy heads d_0,d_1,d_2, where d_i is adjacent only to core vertex i. The transversal matroid on the exterior heads and these dummies has rank exactly three. After substituting the exterior head activities, its basis-generating polynomial in the dummy variables is

M(d)=d_0d_1d_2 + sum_i A_i d_jd_k
                   + sum_(i<j) B_ij d_k + C.

This is a basis polynomial, not a matching-witness polynomial: a basis is counted once. David G. Wagner's Theorem 1.1 in *Rank three matroids are Rayleigh* states that every rank-three matroid is Rayleigh. Applying its inequality to dummy variables d_j,d_k, then setting all three dummy variables to zero by continuity, gives exactly (1). Primary source: https://arxiv.org/pdf/math/0403216, Theorem 1.1, printed page 2. This is an application of that classical theorem, not a new proof or a priority claim.

Inequality (2) is coefficientwise. For every feasible three-head support, choose one matching witness and let x be the head paired with k. Its other two heads form a feasible {i,j} support, so its weight appears in A_k B_ij. Distinct three-head sets give distinct resulting monomials; the product may count a set more than once or contain extra repeated-head monomials, which only helps.

## 2. Restore arbitrary internal core arcs

Write epsilon_ij=1 when i->j is an internal arc, and zero otherwise. For distinct i,j,k define the exterior union mass

H_j = sum_(x in (N_k if epsilon_ij=1) union (N_i if epsilon_kj=1)) v_x.

Thus H_j counts the outside heads that can be used in a degree-two support whose core head is j and whose two core tails are i,k. If both matchings are possible, its outside head is still counted once.

Set

a_i = A_i + epsilon_ij v_j + epsilon_ik v_k,
b_ij = B_ij + v_k H_k.

Every tail lies in C. A degree-two support with tails i,j either has two exterior heads, counted by B_ij, or has core head k and one exterior head, counted by v_k H_k. A degree-three support uses all three core vertices as tails, so its heads are all exterior. Consequently

gamma_1 = sum_i u_i a_i,
gamma_2 = sum_(i<j) u_i u_j b_ij,
gamma_3 = u_0u_1u_2 C.

We claim that the Rayleigh-type inequalities survive the internal arcs:

b_ij b_ik >= a_i C.                         (3)

Expand the difference as

b_ij b_ik-a_i C
 = (B_ij B_ik-A_i C)
 + v_j [B_ij H_j-epsilon_ij C]
 + v_k [B_ik H_k-epsilon_ik C]
 + v_j v_k H_j H_k.

The first term is nonnegative by (1), and the last is nonnegative. If epsilon_ij=0, its bracket is plainly nonnegative. If epsilon_ij=1, then H_j>=A_k, so B_ij H_j>=B_ij A_k>=C by (2). The other bracket is identical with j,k exchanged. This proves (3), for arbitrary internal arcs, including opposite arcs and nontransitive cores.

## 3. The exact three-square decomposition

Put x_01=u_0u_1 b_01, x_02=u_0u_2 b_02, and x_12=u_1u_2 b_12. Direct expansion gives

gamma_2^2-3 gamma_1 gamma_3
 = 1/2 [(x_01-x_02)^2+(x_01-x_12)^2+(x_02-x_12)^2]
   +3u_0u_1u_2 sum_i u_i [b_ij b_ik-a_i C].

Every term is nonnegative by (3). This proves the second cubic Newton inequality and therefore actual-degree rank-ULC.

No real-rootedness assertion is made: the purely bipartite subfamily already contains cubic polynomials with nonreal zeros. Zero activities can be handled by continuity at fixed cubic degree; if the surviving degree drops to two, the universal first-gap theorem supplies its stronger actual-degree normalization.

## Consequence for the GE a=3 branch

The theorem directly covers all nine same-sign three-core templates, including class0, without population bounds or finite positivity certificates. The independently approved mixed-three-core real-rootedness theorem covers the other eight templates. Subject to independent review of this Rayleigh argument, the entire role-weighted a=3 branch is therefore closed.

The earlier `SAME_ORIENTATION_THREE_CORE_ULC.md` moment reduction and its successful incoming-fork certificate are retained as independent exploratory evidence; the present proof does not require the unfinished single-arc cone certificate.
