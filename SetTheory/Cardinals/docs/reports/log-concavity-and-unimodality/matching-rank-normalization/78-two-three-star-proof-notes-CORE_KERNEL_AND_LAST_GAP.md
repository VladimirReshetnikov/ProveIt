# Arbitrary internal two-by-three core with complete exterior blocks

Status: ordinary reduction proposed for review. No frozen package is changed.

Let P and Q have sizes two and three, respectively. Let H be ANY bipartite core on P x Q. The full graph has edge blocks H, P x Y and X x Q, with both exterior blocks complete. Activities are independent and nonnegative. Supports are counted once.

## Boolean core formula

For selected core sets I subset P and J subset Q, and a support size k, the exterior selections have sizes k-|I| and k-|J|. The support is feasible if and only if

    |I|+|J|>=k and nu(H[I,J])>=|I|+|J|-k.

Indeed the latter is exactly the number of internal core edges a witnessing matching must use. Any such core matching can be completed because the two exterior blocks are complete. Thus

 gamma_k = sum_(I subset P,J subset Q)
   1_{|I|+|J|>=k, nu(H[I,J])>=|I|+|J|-k}
   u_I v_J e_(k-|I|)(X) e_(k-|J|)(Y),

with out-of-range elementary sums zero. The condition is Boolean: multiple core matchings do not multiply a support's contribution.

## Explicit coefficient kernels

Retain A=e1(P), B=e2(P), C=e1(Q), D=e2(Q), E=e3(Q), and L,M,N=e1,e2,e3(X), R,S=e1,e2(Y). Define

 W11 = sum_(ij in H) u_i v_j,
 W12 = sum_(i in P) u_i sum_(J subset Q, |J|=2, H[{i},J] nonempty) v_J,
 W21 = B sum_(j in Q, H[P,{j}] nonempty) v_j,
 W13 = E sum_(i in P, H[{i},Q] nonempty) u_i,
 W22 = B sum_(J subset Q, |J|=2, H[P,J] nonempty) v_J,
 J22 = B sum_(J subset Q, |J|=2, nu(H[P,J])=2) v_J,
 J23 = BE 1_{nu(H)=2},
 W23 = BE 1_{H nonempty}.

The formula becomes

 gamma_1 = AR+CL+W11,
 gamma_2 = ACLR+BS+DM+W12 L+W21 R+J22,
 gamma_3 = ADMR+BCLS+EN+W13 M+W22 LR+J23 L,
 gamma_4 = AENR+BDMS+W23 MR,
 gamma_5 = BENS.

The complete core gives W11=AC, W12=AD, W21=BC, W13=AE, W22=BD, J22=BD, J23=BE and W23=BE, recovering the independently approved complete-block formulas.

## Strict last gap for every nonempty active core

Assume the actual degree is five. Then B,E,N,S>0, so all five core activities are positive. If H is nonempty, gamma_4 and gamma_5 are identical to those for the complete core. Every support in H is still a support after completing H, so gamma_3(H)<=gamma_3(K_(2,3)). Consequently

 4 gamma_4(H)^2-10 gamma_3(H)gamma_5(H)
 >=4 gamma_4(K_(2,3))^2-10 gamma_3(K_(2,3))gamma_5(K_(2,3))>0.

The final strict inequality is the approved ordinary complete-block last-gap proof. Thus all 63 nonempty labeled internal masks satisfy the strict last degree-five Newton inequality for arbitrary independent weights and arbitrary finite exterior populations.

The first gap also remains strict universally: at degree five the complete block P x Y contains a positive K_(2,2), supplying duplicate size-two witnesses in the universal compatibility-graph proof. The only remaining rank-five inequalities for these nonempty masks are gamma_2^2>=2gamma_1gamma_3 and gamma_3^2>=2gamma_2gamma_4. No claim about them is made here.

If H is empty, Gamma factors into the support polynomials of the two disjoint complete bipartite exterior components, of actual degrees two and three in the full-rank case. This case is already covered by the standard product closure of ULC sequences (equivalently, products of bivariate Lorentzian polynomials) together with the approved lower-rank bipartite theorem. This last paragraph is only a scope observation, not an extra input to the nonempty-core last-gap proof.
