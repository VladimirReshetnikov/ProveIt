# Weighted growth indices and exact integer projections (Round22)

All coordinates range over the unrestricted integers. Each advertised equation
is the sum of the squares of the literal residuals in its `equation.json`.
The complete collected polynomial is supplied separately. No existential
coefficient search or uninstantiated universal polynomial occurs.

## 1. Precisely inherited interface

The pinned source is `inherited_anchor/source/parent225/equation.json` (SHA-256
`fee84c408828aba3e7ceebe9a37f58509327063aa7fd078fd49c80adf3af4e56`). The inherited
producer `inherited_anchor/code/build_anchor.py --quartic-index` reconstructs
`source/anchor221/equation.json` (SHA-256
`4024d913bde43aa47e8be1fe8c4f36f560420e8b5ceef999d1625e2e31c31c3e`). Its logical calibration and proof sources
are identified in `inherited_anchor/proofs/ORDINARY_PROOF_DEPENDENCY_BOUNDARY.md`.
The logical endpoints are `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation` at ProveIt commit
`953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4`. Those are inherited ordinary
mathematical/proof-assistant source interfaces; this package does not contain a
complete new compilable proof-assistant closure.

The inherited new anchor proof is in `C_ANCHOR_THEOREM.md`; the replacement
label-size theorem is in `LABEL_SEPARATION_WITHOUT_DERIVED_RANGE.md`.
The construction does not assume consistency or inconsistency of ZFC.

## 2. Uniform growth-index lemma

Write ell=2^20. Let h>=16 be a multiple of four, c>=1 an integer, and let
r be either 2 or 4, with c*h^(r-1)>=ell. Replace the growth interface by

    t=h+4z^2,    K=c*t^r,    F=t^K.

For r=4 retain the two quadratic definitions T=t^2 and K=c*T^2.
For r=2 retain only K=c*t^2 and delete the private T coordinate/definition.
The equation F=t^K is not an exponentiation symbol in the final polynomial:
it is enforced by the retained signed Pell power request at actual index K.
Every original frame atom, including actual K, is retained.

These changes preserve solvability iff a finite C222 refutation exists.
Here is the complete delta argument, rather than an assumption of equivalence
between witnesses at different horizons.

* The equation for t gives a positive, cofinal horizon divisible by four.
  The actual index K is positive and K>=ell*t>=t. No sign of the CRT
  representatives, radix, or Pell parameter is needed for these facts.
* The existing constructor-tree induction, bound to all fourteen literal
  constructor outputs, gives every positive local label less than
  t^(ell-1), and their fourteen-term sum less than L=t^ell. Hence
  F=t^K>=t^(ell*t)=L^t. The sharp finite-product separation lemma permits
  equality. It first recovers equal positive-factor counts at most t;
  corresponding elementary-symmetric coefficients lie in [1,F], so their
  differences have absolute value <F. Reduction modulo F at the first
  nonzero coefficient proves polynomial equality and then label multiplicity.
* The retained local Horn polynomial has a fixed polynomial majorant below
  R0^(2^23), R0=2+t+x+y+F. Since F>=t^t>=16^16, the beta bootstrap still
  yields x>2^32 and R0<2x, giving Local<2^x. Thus the CRT congruences are
  decoded into exact local rule equations without the deleted derived-label
  range test. The independent literal-gate audit accompanies the report.
* Radius and valuation estimates use only t>=16, four dividing t, and
  K>=t. In particular v2(F)=K*v2(t)>=2t exceeds v2(t!) and log2(t).
  Therefore B=binom(F+t,t) is odd, N=B^x is odd, and the beta spacing can
  be chosen as a sufficiently large odd multiple of F. All inherited
  every-prime and every-row CRT conditions remain valid.
* Completeness chooses t in this cofinal set above the finite proof's step
  count and local independent parameters, then computes K,F, the pending
  multiset states, y,x,B,N. It chooses the eight other CRT representatives
  before choosing the even representative C in its fixed class modulo N^2,
  cofinally above those representatives and t,K,F+t,y+1,x. Such C exist
  because N^2 is odd. Only afterward are H and q=(BH)^x chosen, and only
  afterward the actual square frame and Pell center. Enlarging C therefore
  changes no previously fixed CRT modulus. This is the same noncircular
  witness construction, with the new value K included among the dominated
  indices.
* Signed anchor soundness is unchanged: before sign recovery, its squared
  cap forces nonzero ordinate V with |V|>|C|, comparison Pell congruences
  force the classified index |C|, and orientation identifies all canonical
  signed-index pairs. The subsequent nonunit radix request forces C>0.
  No global inequality C<t or prior nonnegativity of C is assumed.

The weighted profile uses (r,c,h)=(4,32,32), and the quadratic profile uses
(2,1024,1024). Both attain the admissible boundary c*h^(r-1)=2^20.
The finite source checker compares every unchanged residual and coordinate;
the only changes are the two defining rows, plus removal of the unused T row
and coordinate in the quadratic profile. It checks exact frame retention (35 actual frame atoms). The selected profiles retain the coefficient-4 remainder norm: no sphere-normalization semantic change is used.

## 3. Transported algebraic operations

The round21 chart is used only as a source of proposed integer operations.
Every proposed operation is rechecked against the actual new residuals;
only the delivered operations are used. A label or similarly named variable
is not accepted as evidence of a polynomial identity.

The stored operation list contains:

1. Coordinate shears x_j=y_j+k*y_i, i!=j, inverse y_j=x_j-k*x_i.
2. Residual basis operations R_i <- R_i+k*R_j, i!=j, inverse with -k.
3. Unit definitions x_v=f(other coordinates), of degree at most two,
   permitting deletion of their defining residual and coordinate. A nonlinear
   f is substituted only when x_v occurs linearly everywhere else; every
   resulting residual is checked to remain quadratic. Insertion of f is
   the integral inverse on the zero set.

Thus every retained step preserves the integer zero set up to explicit
bijection; row changes need not preserve the polynomial itself.
The cosmetic variable rename growth.F to crt.growth_majorant_F changes
neither a coordinate nor a coefficient.

## 4. Common-Hessian projections

For a quadratic residual Q_i, let integer vector v satisfy H_i*v=0 for its
Hessian. If v_p=1 and the linear directional coefficient a_r is +/-1 for
one row r, write x=y+s*v with y_p=0. Then

    Q_i(y+s*v)=Q_i(y)+a_i*s.

The pivot row is exactly s=-a_r*Q_r(y). Substitute it into every other row:
R_i(y)=Q_i(y)-a_r*a_i*Q_r(y). This is still quadratic. Forward and inverse
maps are y_i=x_i-v_i*x_p and x_i=y_i+v_i*(-a_r*Q_r(y)), respectively.
No division side condition arises. The checker independently reconstructs
these row combinations, rather than reusing the producer's substitutions,
and verifies the recorded complete inverse identities.

Each profile uses two such projections after the transported chart. The
weighted profile has 215 coordinates and 154 rows; the quadratic profile
has 214 coordinates and 153 rows. Subsequent basis improvements are integer
row operations only, with their composed inverses explicitly checked.

## 5. Logical conclusion and scope

For each final literal polynomial P, the foregoing arithmetic constructions
and exact algebraic bijections prove, within ZFC,

    (exists integer tuple x: P(x)=0)
      iff a finite C222 refutation exists
      iff a finite ZFC refutation exists.

Negation gives ZFC |- [P has no integer zero <-> Con(ZFC)], for the fixed
effective ZFC proof presentation of the inherited calibration. Proof codes
are internal natural numbers of ZFC, not a restriction to externally
standard codes. This proves the equivalence, not either side separately.

The independent normal/-O checks certify finite coefficient identities,
source deltas, inverse maps, expansions and deterministic reconstruction.
They do not replace the unbounded CRT, Pell, finite-proof or logical theorems
by finite testing. No global variable/degree/height optimum or external human
peer review is claimed.
