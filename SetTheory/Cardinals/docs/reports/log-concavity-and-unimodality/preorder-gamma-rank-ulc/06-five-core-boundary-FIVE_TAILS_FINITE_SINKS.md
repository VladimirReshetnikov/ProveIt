# Last rank-four gap for five core tails and at most four sinks

## Result

For the arbitrary loopless directed five-core with a universal independent sink cloud, independent nonnegative role activities, and at most four positive sink-head activities,

    gamma_3^2 >= (8/3) gamma_2 gamma_4.

No positivity assumption on the five tail variables is necessary for this finite-sink result. If at most two sink-head activities are positive, gamma_4=0 and the assertion is immediate. The proof below treats three or four active sinks simultaneously.

Use the exact Boolean-support coefficient notation of STRUCTURAL_REDUCTION.md:

    gamma_2=b+cE_1+e_2E_2,
    gamma_3=fE_1+dE_2+e_3E_3,
    gamma_4=gE_3+e_4E_4.

The coefficient polynomials are sums over disjoint endpoint sets, with each feasible support counted exactly once. The ordinary comparisons previously proved are

    3fd >= bg,
    2de_3 >= 2e_2g+ce_4,
    e_3^2 >= 2e_2e_4.

We first sharpen the other ordinary comparison to

    4fe_3+2d^2 >= be_4+4cg.                         (II*)

This sharpening is coefficientwise in the independent core activities. The original proof had the unnecessary larger coefficient 3 before d^2.

## Ordinary proof of (II*)

The squared-head coefficient is 2d_j^2-4c_jg_j. The inequality

    d_j^2 >= 2c_jg_j

holds coefficientwise. If j has at least two incoming core neighbors, d_j is the full e_3 on its other four tail variables, c_j<=e_2 there, and g_j=e_4 there. Use e_3^2>=2e_2e_4 coefficientwise in four variables. If its neighborhood is the singleton with activity a, write t,s,p for e_1,e_2,e_3 of the other three activities. Then c_j=at,d_j=as,g_j=ap and s^2>=2tp coefficientwise. Empty neighborhoods give zero.

For distinct heads j,k, let A=C\{j,k}, x=u_j,y=u_k, and let t,s,p be the elementary symmetric polynomials on the three activities in A. Let P,Q be the incoming neighborhoods of j,k from A. Let delta_j indicate k->j and delta_k indicate j->k. Define

    U=P if delta_j=0, and U=A otherwise,
    V=Q if delta_k=0, and V=A otherwise.

For a subset T of A, write

    L_T=sum_{a in T}u_a,
    B_T=sum_{|S|=2, S intersects T}u_S.

Put epsilon_P=1(P nonempty), epsilon_Q=1(Q nonempty), eta_P=1(U nonempty), eta_Q=1(V nonempty). Let epsilon indicate that P,Q have distinct representatives, and let b=b(P,Q) be the Boolean feasible two-tail polynomial for the head pair. Then

    c_j=B_P+yL_U, d_j=epsilon_P p+yB_U, g_j=eta_P yp,
    c_k=B_Q+xL_V, d_k=epsilon_Q p+xB_V, g_k=eta_Q xp,
    f_jk=epsilon p,
    e_3=p+(x+y)s+xyt, e_4=(x+y)p+xys.

The desired head-pair coefficient is

    R=4epsilon p e_3+4d_jd_k-be_4-4(c_jg_k+c_kg_j).

Its constant term is p^2(4epsilon+4epsilon_P epsilon_Q), which is nonnegative.

Its x coefficient divided by p is

    4epsilon s+4epsilon_P B_V-b-4eta_Q B_P.

If epsilon=1, epsilon_P=eta_Q=1 and use B_P<=s and b<=B_V. If epsilon=0, b=0. The expression vanishes unless epsilon_P=eta_Q=1. In that case delta_k=1 gives B_V=s>=B_P; otherwise P=Q is a common singleton, giving B_V=B_P. Thus this coefficient is nonnegative. The y coefficient is symmetric.

Its xy coefficient is

    4epsilon pt+4B_U B_V-bs-4p(eta_Q L_U+eta_P L_V).

If eta_P eta_Q=0 the expression vanishes. Otherwise both eta indicators are one. The following elementary three-variable comparisons hold coefficientwise:

    sB_T >= p(t+L_T) for nonempty T,
    B_U B_V >= 2p L_(U intersection V),
    B_U B_V >= b(U,V)s.

For the first, a singleton T gives equality on the p-multiples and extra positive square terms; for |T|>=2, B_T=s and s^2>=2pt>=p(t+L_T). For the second, each a in U intersection V contributes both orders of the two distinct pairs containing a. For the third, if both neighborhoods have size at least two then B_U=B_V=s and b(U,V)<=s. If one is a singleton and the other has size at least two, b(U,V)<=B_singleton. Two distinct singletons give u_a(u_b+u_c)u_b(u_a+u_c)=u_au_b(s+u_c^2)>=u_au_b s; equal singletons have b(U,V)=0.

If epsilon=0 and at least one delta is one, assume U=A. The xy coefficient is

    4sB_V-4p(t+L_V)>=0.

If epsilon=0 and both deltas are zero, nonempty P,Q must be the same singleton, and B_U^2>=2pL_U gives the result.

If epsilon=1, b(P,Q)<=b(U,V) and L_U+L_V-t<=L_(U intersection V). Therefore the xy coefficient is at least

    3B_U B_V-4pL_(U intersection V)>=0.

This completes an ordinary proof of (II*) for every directed five-core.

## Finite-sink Newton bounds

For three or four positive sink activities, binomial-normalized Newton inequalities give, with common weaker constants valid for both cases,

    E_1E_2 >= 6E_3,
    E_2^2 >= (9/4)E_1E_3,
    E_1E_3 >= 4E_4,
    E_2E_3 >= 2E_1E_4,
    E_3^2 >= (8/3)E_2E_4.

When there are three active sinks, E_4=0 and the final three comparisons involving it are immediate. For four active sinks the stronger constants in the middle two are respectively 16 and 6. The proof only uses 4 and 2 there. These comparisons remain valid with zero activities.

## Square completion

Put

    X=fE_1, Y=dE_2, Z=e_3E_3.

The core and sink comparisons imply

    bgE_3 <= (1/2)XY,

    be_4E_4+cgE_1E_3
      <= (be_4/4+cg)E_1E_3
      <= (fe_3+d^2/2)E_1E_3
      <= XZ+(2/9)Y^2,

    ce_4E_1E_4+e_2gE_2E_3
      <= (ce_4/2+e_2g)E_2E_3
      <= YZ,

    e_2e_4E_2E_4 <= (3/16)Z^2.

These four bounds account for every term of gamma_2 gamma_4. Thus

    gamma_3^2-(8/3)gamma_2gamma_4
      >= X^2+(2/3)XY+(11/27)Y^2+(1/2)Z^2
           -(2/3)XZ-(2/3)YZ
      = [X+(Y-Z)/3]^2+(8/27)[Y-3Z/4]^2+(2/9)Z^2
      >=0.

This is a uniform ordinary proof for the three- and four-positive-sink branches. It uses no numerical search or computer-discovered nonnegativity certificate as a premise.

## Combined boundary conclusion

If the actual degree is four, there are at least four active core tails. If exactly four tails are active, FOUR_ACTIVE_TAILS.md proves the desired last inequality for every finite sink count, retaining the fifth physical vertex as a possible head. If all five tails are active, gamma_5=e_5E_5=0 forces at most four active sink heads. At least three are needed for gamma_4>0. The present finite-sink proof applies. Therefore the last actual-degree-four inequality is proved for every boundary face of this five-core universal-sink family.

This result alone does not prove the first middle actual-degree-four inequality gamma_2^2>=(9/4)gamma_1gamma_3, and makes no claim about actual degree three.
