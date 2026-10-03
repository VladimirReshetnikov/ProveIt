# A fully multivariate two-tail Lorentzian theorem

Status: proposed ordinary strengthening, awaiting independent review. October 1, 2026. The released rank-five paper is unchanged.

## 1. Abstract matroid statement

Let M be a rank-q matroid representable over a characteristic-zero field, on a ground set E union {A,B}, where the old set E spans M. The distinguished elements A,B may be loops or dependent. In variables w_e for e in E, define:

- U0: the basis polynomial of M restricted to E;
- UA and UB: old (q-1)-subsets extendable to a basis by A or B, respectively;
- U: old (q-1)-subsets extendable by at least one of A,B;
- V: old (q-2)-subsets extendable by both distinct elements A,B.

Every feasible old subset contributes coefficient one. Terms with negative set cardinality are zero. Thus at q=0, U0=1 and all other polynomials vanish; at q=1, V=0.

Take three finite populations of nonnegative weights, called private-A, private-B and common. Let their sums be L0,L1,H, and let S be the second elementary moment of the common population. Put

  R0=L0+H,  R1=L1+H,
  M2=L0L1+H(L0+L1)+S,
  Mmax=L0L1+H(L0+L1)+H²/2,
  W=L1 UA+L0 UB+H U.

The parameters are constants; a,b,z and all w_e are independent polynomial variables.

**Proposed theorem.** The homogeneous degree-(q+2) polynomial

  F_M=z²U0+z(aR0+bR1)U0+ab M2 U0
             +z²(aUA+bUB)+ab z W+ab z²V                   (1)

is Lorentzian.

**Graph corollary.** For every bipartite graph with disjoint shores P union X and Q union Y, |P|=2, |Q|=q, and no X×Y edge, the polynomial retaining ALL selected-tail variables individually,

  F_G(x_left,z,z_Q)=sum_(S,T feasible)
       [product_(j in T) v_j] [product_(i in S) x_i]
                 z^(2-|T intersect Y|) product_(j in Q minus T) z_j,      (2)

is Lorentzian under arbitrary nonnegative head activities. Independent tail activities can be inserted by nonnegative scaling of each x_i. Thus this strengthens the released theorem, which identifies all selected-tail variables with weighted copies of one variable t.

This does not make Y activity parameters into homogeneous variables, and does not establish a physical-role collision theorem for directed relations.

## 2. Lorentzian facts and the principal-line seed

Use the same primary Brändén–Huh facts as the released proof: matroid basis Lorentzianity, nonnegative linear substitution, differentiation, products, closedness, and the M-convex-support/quadratic-derivative characterization. Nonnegative directional derivatives preserve Lorentzianity: realize such a derivative as an ordinary derivative after substituting s_i -> s_i+r_i y with r_i>=0, then set y=0.

The following homogeneous degree-q seed is Lorentzian:

  S_M(sA,sB,sU,w)
     =U0+sA UA+sB UB+sU U
             +(sA sB+sA sU+sB sU+sU²/2)V.                (3)

For completeness, choose a matrix representation of M and add m generic columns C_i=alpha_i A+beta_i B. Old (q-1)-sets extend by C_i exactly when they extend by A or B, because the two coefficients are algebraically independent. Any pair among A,B,C_i extends an old (q-2)-set exactly when A,B do, by the determinant identity

  det(I,C_i,C_j)=(alpha_i beta_j-beta_i alpha_j)det(I,A,B).

Three line columns are dependent. Thus the basis polynomial has linear C contribution (sum h_i)U and quadratic contribution sum_(i<j)h_i h_j V, together with the displayed A,B terms. Set h_i=sU/m and let m tend to infinity. The quadratic coefficient tends to sU²/2. This proves (3), including loop or parallel cases by vanishing minors.

## 3. M-convex support via a generic matrix augmentation

We establish M-convex support for (1) for every q, before induction. Let n be the total size of the three weighted populations. Choose a q-row matrix representing M. Embed every old column as (old column,0_n). Add n new rows to the distinguished A,B columns: in the row for a private-A head, give A an independent new indeterminate and B zero; for private-B, do the reverse; for a common head, give both independent new indeterminates. Adjoin n new columns which are the unit vectors of these new rows. All new indeterminates are algebraically independent over the original field.

The augmented matroid has rank q+n because E spans the old q-dimensional space and the new dummy columns span the new rows. Consider its basis polynomial, with a,b on the distinguished columns, w_e on old columns, and d_y on the new dummy columns. Expanding a minor along the new rows gives the following complete description:

- No new dummy omitted: the old columns and selected A,B form an original M basis, giving U0+aUA+bUB+abV.
- One dummy y omitted: if only A or only B is selected, its permitted incidence in the new row leaves an old U0 basis. If both are selected, the remaining old condition is UB for private-A, UA for private-B, and the union U for a common row.
- Two dummies omitted: both distinguished columns must be selected, the two new rows must be matchable to A,B, and the old condition is U0.
- More than two dummies omitted: no basis exists.

There is no cancellation in the common one-row case: the determinant is a sum of the form alpha_y det(I,B)-beta_y det(I,A), with independent new indeterminates. For two rows, the independent new-row determinant is nonzero precisely for a feasible two-head pattern. We use only whether each determinant is nonzero, not its value; each basis is counted once.

For positive head-population weights omega_y, set d_y=z/omega_y and multiply by product_y omega_y. The resulting Lorentzian basis specialization is

  G=z^(n-2) F_M

as a Laurent identity. When n>=2 this is a polynomial monomial factorization; when n<2 the inverse relation is. Their exponent supports differ by a fixed translation, so F_M has M-convex support. Zero population weights follow by coefficientwise limits on G before translating its support. The old-basis term z^n U0 is nonzero, so zero output is excluded. This argument does not claim that Lorentzianity itself survives arbitrary monomial division.

## 4. Old-variable contraction closes the induction

Every old variable is multi-affine. If e is a loop, partial_(w_e)F_M=0. Otherwise the derivative is exactly F_(M/e), with the same population parameters and distinguished images of A,B. For example, differentiating UA restricts its old subsets to those containing e; deleting e from such a subset gives exactly the A-extendable subsets in M/e. The same statement applies to UB, their Boolean union U, and V.

The old set E minus {e} spans the rank-(q-1) quotient, and contraction preserves representability. Generic principal-line columns commute with the quotient. Therefore the class is closed under every nonzero old-variable derivative.

To prove (1) Lorentzian at rank q, use the already proved M-convex support and inspect derivatives of total order q. If an old variable occurs, the result is a derivative of a smaller-rank polynomial covered by induction. It remains only to check derivatives in a,b,z. Since a,b are multi-affine and z has degree at most two, these checks vanish automatically for q>=5. Ranks zero through four are treated explicitly below.

## 5. Rank zero

At q=0, (1) is

  F=z²+(aR0+bR1)z+ab M2.

Its Hessian in (a,b,z) is

  [[0,M2,R0],[M2,0,R1],[R0,R1,2]],

with determinant 2M2(R0R1-M2). Here R0R1-M2=H²-S>=0. When M2>0 there is a negative 2×2 principal minor, hence a positive and a negative eigenvalue; the nonnegative determinant forces at most one positive eigenvalue. Boundaries follow by adding two common heads of activity epsilon and taking the limit. Thus F is Lorentzian.

## 6. Rank one

The old basis polynomial is u=sum_(e nonloop)w_e. Let alpha=UA and beta=UB, which belong to {0,1}; then U=max(alpha,beta) and V=0. Before making the substitution u=sum w_e, use the same construction for a rank-one matroid with one old nonloop element and the given loop indicators for A,B. Its polynomial in u,a,b,z has M-convex support by Section 3. It is therefore enough to check its first derivatives and then make the nonnegative substitution u=sum w_e. Write

  W0=L1 alpha+L0 beta+H max(alpha,beta).

The u derivative is the rank-zero polynomial. The a derivative has Hessian in (u,z,b)

  [[0,R0,M2],[R0,2alpha,W0],[M2,W0,0]],

with determinant 2M2(R0W0-alpha M2), and the exact nonnegative identity

  R0W0-alpha M2
    =alpha(H²-S)+(1-alpha)beta R0²+alpha beta R0 L0.

The b derivative is symmetric. For M2>0 each has a negative principal 2×2 minor, so the nonnegative determinant gives the required signature. The z derivative has leading (u,z) Hessian block [[0,2],[2,0]]. Its Schur complement on (a,b) is

  [[-2R0 alpha,-H alpha beta],[-H alpha beta,-2R1 beta]],

which is negative semidefinite because 4R0R1>=H². The leading block has one positive and one negative eigenvalue; hence the full Hessian has at most one positive eigenvalue. Positive common-head perturbations include the M2=0 boundary. This proves rank one.

## 7. Rank two

Now (3) is a Lorentzian quadratic and V is a nonnegative constant (zero or one). Write

  m=(L1,L0,H)^T,
  phi(s)=sA sB+sA sU+sB sU+sU²/2,

so phi(m)=Mmax and phi(e_A)=phi(e_B)=0. Assume initially M2,R0,R1>0. The nonzero second derivatives involving only a,b,z have exact formulas

  partial_z² F_M = 2 S_M(s=(a,b,0)),

  partial_a partial_b F_M
      = M2 S_M(s=mz/M2)-[(Mmax-M2)/M2] z² V,

  partial_a partial_z F_M
      = R0 S_M(s=(2 e_A z+m b)/R0)-(Mmax/R0)b² V,

  partial_b partial_z F_M
      = R1 S_M(s=(2 e_B z+m a)/R1)-(Mmax/R1)a² V.           (4)

These follow by expansion, using e_A^T Jm=R0 and e_B^T Jm=R1 for the matrix J of the principal-line seed. Every seed substitution is a nonnegative linear substitution. The subtracted terms have nonnegative coefficients and change only one diagonal entry of the quadratic Hessian. Subtracting a positive semidefinite matrix cannot increase its number of positive eigenvalues. The actual derivative polynomials in (4) have nonnegative coefficients by (1). Their Hessians therefore satisfy the required signature condition. Common-head perturbations remove all denominator boundaries. Repeated a or b derivatives are zero. Old-variable derivatives were handled by contraction. This proves rank two.

## 8. Ranks three and four

At q=3, the only possibly nonzero order-three derivatives without old variables are

  partial_a partial_z² F_M=2(UA+bV),
  partial_b partial_z² F_M=2(UB+aV),
  partial_a partial_b partial_z F_M=W+2zV.

The first is twice the derivative partial_(sA)S_M specialized at sA=sU=0,sB=b; the second is symmetric. For the third, take the nonnegative directional derivative of S_M in direction m=(L1,L0,H). It equals

  W+(m^T J s)V.

If m≠0, some coordinate of Jm is positive, so choose r>=0 with m^T Jr=2 and set s=r z. This gives W+2zV and preserves Lorentzianity. If m=0, the polynomial is simply 2zV, a product of a nonnegative linear variable and a rank-one contraction basis polynomial. All other derivatives are zero or old-variable contractions.

At q=4, only partial_a partial_b partial_z² F_M=2V remains. If A,B are independent, V is the rank-two basis polynomial of M/{A,B} restricted to old elements, hence Lorentzian; otherwise V=0. For q>=5 all remaining derivatives in a,b,z vanish. The induction and quadratic-derivative characterization now prove the abstract theorem.

## 9. The graph specialization and boundaries

For the stated graph take M to be the transversal matroid with slots Q, old elements X plus private Q dummies, and distinguished A,B representing the two P tails. The old set spans M because the dummies form a basis. For positive Q activities, set old X variables to their individual selected-tail variables, dummy_j=z_j/v_j, a=x_p0, b=x_p1, and multiply by product_(j in Q)v_j. Use the actual Y activity populations in the constants L0,L1,H,S. The exact endpoint decomposition in (1) gives (2): the one-shared-head case uses the Boolean extension union, and all other cases are forced or independent of core witnesses.

This is a nonnegative linear specialization of the abstract Lorentzian polynomial and a positive scaling. Zero Q activities follow by limits in the explicit endpoint formula. Independent tail activities are inserted by further nonnegative scalings. The empty support gives z² product_j z_j with coefficient one, excluding zero output. Diagonalizing all selected-tail variables recovers the released order-(q+2) theorem, but this argument retains their individual variables.

No joint Lorentzian claim is made in the Y population activity parameters, whose degrees would change the homogenization. Thus the proof does not justify merging physical tail/head copies. The current task is the rigorous audit of the augmented-matrix support identity, contraction closure, and the small-rank derivative identities. There is no finite-enumeration premise and no change to the delivered paper.
