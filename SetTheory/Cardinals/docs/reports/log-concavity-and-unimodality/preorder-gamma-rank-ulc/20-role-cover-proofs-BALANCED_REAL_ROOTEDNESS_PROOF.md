# Full balanced 2+2 core: multivariate monomer stability and real-rootedness

Status: independently audited and approved (2026-10-01), including arbitrary nonnegative independent role activities, all stability-preserver conventions, both support identities and the zero-activity limit. This strengthens the already audited last-gap inequality. Independent exact weighted Hall-support checks provide additional verification.

## The directed family

There are two source core vertices P={p1,p2}, two sink core vertices Q={q1,q2}, and all four arcs P→Q. Exterior vertices are pairwise nonadjacent. Each exterior vertex x has arbitrary neighbor subsets P(x)⊆P and Q(x)⊆Q, with arcs P(x)→x→Q(x). Either subset may be empty. Assign arbitrary nonnegative independent tail and head activities u_v and v_v. A feasible ordered DISJOINT pair (A,B) contributes the product of tail activities on A and head activities on B, counted once even if multiple matchings realize it.

The claim is that the associated gamma polynomial is real-rooted, with every nonconstant root negative. We prove the stronger statement that its multivariate signed monomer polynomial is real stable.

## 1. A rank-two stable auxiliary quadratic

Let M be any loopless rank-two matroid, with parallel classes having variable sums r1,...,rj. Its basis polynomial and element sum are

B=Σ_{i<k}ri rk=e₂(r1,...,rj),  L=Σ_i ri.

The polynomial

F(s)=s²+√2 Ls+B

is real stable in s and the ground-element variables. Indeed,

F(s)=(s+L/√2)²−(Σ_i ri²)/2.

In the independent coordinates s,r1,...,rj, this real quadratic form has exactly one positive eigenvalue. It has nonnegative coefficients and is positive on the strictly positive orthant. These two facts imply real stability: writing an alleged zero as x+iy, the imaginary part forces x to be orthogonal to y for the quadratic form; since F(y)>0, its one-positive-direction signature gives F(x)≤0, contradicting the real-part equation F(x)=F(y). Substituting the parallel-class sums preserves stability. Loops can be omitted.

## 2. A stable coupling of two rank-two sides

Take two such pairs (B_P,L_P) and (B_Q,L_Q), on disjoint variable sets. Their auxiliary product

(s²+√2 L_P s+B_P)(t²+√2 L_Q t+B_Q)

is real stable. Define a linear operator on polynomials of degree at most two in each of s,t by

T(1)=1,  T(st)=−1/2,  T(s²t²)=1,

and T(s^i t^j)=0 for all other pairs (i,j)∈{0,1,2}². It acts coefficientwise on every untouched variable. Its algebraic symbol in the auxiliary variables is

T[(s+a)²(t+b)²]=a²b²−2ab+1=(ab−1)².

This is real stable: if a is in the upper half-plane, 1/a is in the lower half-plane, so ab=1 is impossible with both a,b in the upper half-plane. For the full operator including untouched variables, the symbol is this factor times products of factors (z+w)^κ, which are also stable. The finite-degree Borcea–Brändén stability-preserver theorem therefore applies to the coefficientwise operation.

Consequently

H=B_P B_Q−L_P L_Q+1                       (2.1)

is real stable. It is not the zero polynomial, since its constant term is1.

The precise symbol criterion is Theorem5.2 in Wagner's author-hosted survey, *Multivariate stable polynomials: theory and applications*, https://www.math.uwaterloo.ca/~dgwagner/ceb_wagner.pdf (printed page15). The theorem is attributed there to Borcea–Brändén, Theorem1.1 of reference[5]. Its plus-sign symbol convention is exactly the one used above.

## 3. Identification with the two-copy monomer polynomial

First split every physical exterior vertex into two separate copies:

- a head copy adjacent from P(x)
- a tail copy adjacent to Q(x)

The two-copy relation is bipartite, with all four P→Q core arcs. Copies with no neighbors are retained as isolated vertices.

For each two-center side, form the rank-two transversal matroid on its exterior copies together with two private dummy elements, one for each center. Its only nontrivial parallel classes are the private-neighborhood copies together with the corresponding dummy. Each common-neighborhood copy is its own parallel class. Thus section1 applies.

Give the private P dummies the monomer variables z_{p1},z_{p2}; give a P-side exterior head copy x the variable −1/z_x. Define B_P and L_P in these substituted variables. Do the same for Q and its exterior tail copies. Every substituted argument lies in the upper half-plane when its monomer variable does, since −1/z maps the upper half-plane to itself.

Let Z be the product of the monomer variables of all exterior copies. Then the signed monomer polynomial of the unweighted two-copy relation is exactly

mu_copy(z)=Z(B_P B_Q−L_P L_Q+1).           (3.1)

Here mu_copy is the sum over ordered tail/head matching supports (A,B) of

(−1)^|A| product_{v outside A∪B} z_v.

To check (3.1), separate supports by the number of P→Q core arcs in a matching. This number is determined by the endpoint support.

- Zero core arcs gives Z B_P B_Q, the product of the two side monomer polynomials
- One core arc gives −Z L_P L_Q. On either side, the unmatched-core monomer term is the sum of the two private dummy variables. If both core vertices on that side are used, the selected exterior singleton contributes once, so the exterior part is the sum of all active copy variables, not its neighbor degree
- Two core arcs uses all four core vertices and no exterior copy, contributing +Z exactly once, not twice

Completeness of the core makes these side conditions sufficient. Thus no matching-witness multiplicity occurs.

The right side of (3.1) is a polynomial: each exterior copy variable occurs at most linearly in H before inversion, and Z cancels its possible denominator. Stability follows directly from section2 and the upper-half-plane substitutions; Z never vanishes there. Isolated copies simply contribute their monomer factors.

Positive activities on the vertices of the two-copy relation preserve monomer stability. If a copy has activity w_i, its weighted monomer polynomial is

(product_i w_i) mu_copy((z_i/w_i)_i).

This weights each used copy by w_i and leaves each unused monomer variable unchanged. Assign u_x to tail copies, v_x to head copies, u_p to P core vertices and v_q to Q core vertices.

## 4. Merging physical copies without double use

For a physical exterior vertex, let a,b be the two copy monomer variables. The polynomial is multiaffine in them. Replace the pair by a single physical monomer variable z using the linear operation

ab→z,  a→1,  b→1,  1→0.                  (4.1)

The cases respectively mean both copies unused, exactly one copy used, or both copies used. The last case is discarded, enforcing disjoint physical tail/head supports. Coefficients for the two different one-used roles are added, exactly as required by the directed-support definition.

The algebraic symbol of (4.1) is

T[(a+r)(b+s)]=z+r+s,

which is real stable. Including untouched variables again only multiplies this symbol by stable (variable+dual-variable) factors. The finite-degree stability-preserver theorem therefore shows that each merge preserves stability. After every physical vertex is merged, the result is precisely the desired weighted directed monomer polynomial

mu_D(z)=Σ_{feasible disjoint (A,B)} (−1)^|A| u^A v^B product_{v outside A∪B}z_v.

It is nonzero because the empty support contributes the product of all physical monomer variables with coefficient1.

Zero activities follow by continuity from positive activities; the leading empty-support monomial remains, so the limit polynomial is nonzero and stable.

## 5. Gamma real-rootedness

Set all N physical monomer variables equal to s. The stable polynomial becomes

mu_D(s,...,s)=Σ_k (−1)^k gamma_k s^(N−2k)=s^N Gamma(−s^(−2)).

It has only real zeros. If Gamma had a nonreal or nonnegative real zero rho, then a solution of s²=−1/rho would be nonreal and would give a nonreal zero of the displayed monomer polynomial. Gamma(0)=1, so rho=0 is impossible. Therefore every zero of Gamma is negative real.

Newton's inequalities imply actual-degree ultra-log-concavity, including all three degree-four gaps when gamma4>0.

## Scope

The argument proves arbitrary nonnegative independent role activities for this full balanced2+2 core with independent exterior vertices. It uses no transitivity assumption. It does not establish the same statement for an incomplete2+2 core or for a1+3 split. In particular it does not conflict with the known nonreal1+3 example.
