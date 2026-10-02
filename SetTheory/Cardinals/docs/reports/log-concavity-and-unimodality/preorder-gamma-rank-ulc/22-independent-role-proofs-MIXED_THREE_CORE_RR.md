# Real-rootedness for every mixed-orientation three-core template

Status: proof and independently checkable finite tests are ready for external review. This note makes no literature-priority claim.

## The directed-relation theorem

Let a directed relation have vertices p,q,h and an arbitrary independent set X. Its possible arcs are:

- p -> x and/or q -> x, for x in X;
- x -> h, for any chosen subset of X;
- p -> h and/or q -> h;
- either or both of the internal arcs p -> q and q -> p.

There are no other arcs. Assign arbitrary positive independent tail/head activities. Then its disjoint-support polynomial has only real negative zeros. The dual relation has the same conclusion, with tail/head activities exchanged. Transitivity is not required.

This covers all eight mixed-sign three-cover preorder classes 1,3,4,6,7,10,12,14 in the established 17-class numbering. The statement is for arbitrarily large heterogeneous exterior populations, although its matching rank is at most three.

## The rank-two base and exact hub decomposition

Delete h. Let Q_0(z) be the support polynomial of the bipartite relation from {p,q} to X, and let a=u_p v_q [p->q]+u_q v_p [q->p]. An internal edge consumes both core vertices, so cannot coexist with another edge. Thus the remaining support polynomial is

Q(z)=Q_0(z)+a z.

For x in X let Q_{-x} be the same polynomial with x deleted. Define the rank-reduced insertion kernel D(z) by adjoining a new head of activity s and neighborhood J={r in {p,q}:r->h}: its support polynomial is Q_0(z)+s z D(z). Thus D has degree at most one. Equivalently, D is the coefficient of an independent marked-head variable w when the old exterior variables are all z and the new head has activity one; that marked polynomial is Q_0(z)+w D(z). The full polynomial is exactly

Gamma(z)=Q(z)+v_h z [D(z)+sum_(x->h) u_x Q_{-x}(z)].

A support omitting h gives Q. If h is paired with p or q, the new-head support kernel is D; an internal p-q edge cannot also occur. Otherwise a selected exterior tail x is paired with h. In the base, exterior vertices occur only as heads, so this exterior tail is unique and its partner h is forced. Deleting h and x leaves exactly a support counted by Q_{-x}. These cases are disjoint at the level of ordered endpoint supports, not merely matching witnesses.

## Stable formula for Q_0

Put U=u_p, V=u_q. Give every exterior vertex x its own variable z_x and include its head activity v_x. Let X_p,X_q,X_b be the private-p, private-q and common neighbor types. Vertices adjacent to neither core vertex are omitted from the formula. Then the multiaffine exterior-support polynomial is

f(z_X)=UV e_2(1/U+sum_(x in X_p) v_x z_x,
              1/V+sum_(x in X_q) v_x z_x,
              (v_x z_x)_(x in X_b)).

Expanding e_2 gives precisely each feasible endpoint support once. In particular, a common singleton has coefficient U+V and a pair of common heads has coefficient UV, rather than twice that coefficient. Setting all z_x=z gives Q_0.

The elementary symmetric polynomial e_2 is real stable. One elementary justification is to differentiate product_i(t+w_i) m-2 times and set t=0: if all Im(w_i)>0, all roots before and after differentiation lie strictly in the lower half-plane, by Gauss–Lucas. Positive affine substitutions preserve stability, with real constants obtained by limits. Thus f is stable.

For a fixed x write f=f_{-x}+z_x g_x. The substitution z_y=z for y!=x and z_x=z+s shows that Q_0(z)+s g_x(z) is stable. Giving a new head of type J activity one and the independent marked variable s instead gives the stable polynomial Q_0(z)+s D(z), since it either adds an affine term to one private argument or appends a common argument. Specializing that marked variable to v_h z recovers the activity-insertion contribution v_h z D(z). The empty type gives D=0.

Consequently every nonzero g_x and D interlaces the negative real roots of Q_0 with the standard positive-residue orientation. For completeness: stability of Q_0(z)+s L(z) implies that L(z)/Q_0(z) has nonpositive imaginary part for Im(z)>0. Its real simple poles therefore have nonnegative residues. Since L has degree at most one and Q_0 degree two, this is equivalent to the single zero of L lying between the two zeros of Q_0. Degenerate cases follow by limits.

## Adding the internal arc preserves the needed interlacing

Work first in the generic case where Q_0 has two distinct negative roots, positive quadratic coefficient, and the nonzero linear kernels have positive leading coefficient. If r is the zero of any kernel L among the g_x and D, then r<=0 and Q_0(r)<=0. Hence

Q(r)=Q_0(r)+a r<=0.

The quadratic Q has nonnegative coefficients and discriminant at least that of Q_0, because only its linear coefficient was increased. Its two roots are negative, and Q(r)<=0 says that r lies between them. Thus L interlaces Q as well. Equivalently, writing the roots of Q as r_1<r_2<0, both residues L(r_i)/Q'(r_i) are nonnegative.

## Residue signs and the final upper-half-plane argument

For D/Q, the polynomial part is zero and all residues are nonnegative. For a deletion polynomial, the exact relation is

Q_{-x}=Q-z g_x.

If g_x/Q=sum_i c_i/(z-r_i), with c_i>=0 and r_i<0, then

Q_{-x}/Q = alpha_x + sum_i (-r_i)c_i/(z-r_i),

where alpha_x is the ratio of the nonnegative leading coefficients of Q_{-x} and Q, hence alpha_x>=0. Thus every ratio D/Q and Q_{-x}/Q has the form alpha+sum_i beta_i/(z-r_i), with alpha,beta_i>=0 and r_i<0. Vertices irrelevant to Q simply give Q_{-x}/Q=1.

Multiplication by z turns this into a function with nonnegative imaginary part in the upper half-plane: Im(z)>0, and

Im(z/(z-r)) = (-r) Im(z)/|z-r|^2 > 0   for r<0.

Therefore

Gamma/Q = 1+v_h z [D/Q+sum_(x->h)u_x Q_{-x}/Q]

is either identically 1 or has strictly positive imaginary part in the upper half-plane. It has no zero there. Q has only real zeros, so Gamma has no upper-half-plane zero; real coefficients exclude lower-half-plane zeros too. Positive coefficients and constant term one make every zero negative. Newton's inequalities now give actual-degree rank-ULC.

The generic assumptions can be removed by adding arbitrarily small common-head activities to the base and perturbing positive parameters, then taking coefficientwise limits. The graph form is preserved under these auxiliary additions. Zero activities are also covered by limits; actual-degree rank-ULC follows from the real-rooted limiting polynomial at its surviving degree.

## Reproduction

Run `python verify_mixed_three_core.py`. This fresh standard-library checker imports no producer and uses Hall's criterion to count supports. The receipt `mixed_three_core_verification.json` reports 1,680 exact support-decomposition and discriminant tests, 6,653 exact linear-kernel interlacing inequalities, 1,655 checks of the e2 formula, and 128 zero-activity cases. These checks supplement the analytic proof. The earlier `probe_mixed_three_core_rr.py` also passed 800 instances of the eight transitive templates. A separate audit should review the residue signs and the distinction between the new-head kernel D and individual matching witnesses.
