# CRT-anchor / joint-certificate composition

Ordinary mathematical proof at ProveIt commit
`ecb9a4b4dda617512952525d50f17343700aac52`. The new bridge is formalizable
in ZFC; no freshly emitted object-language proof or end-to-end Lean build
is claimed. Indices below are zero-based source219 indices.

## Calibrated parent

`source/anchor219.json` is package173's literal
`source/anchor219/equation.json`, unchanged. The parent has219 unrestricted
integer variables and158 quadratic residuals. Its affine-horizon profile is
t=16+4*d^2, K=2^20*t, F=t^K, C=2*c. Variable powers here state the
certificate's semantics; they are absent from the actual polynomial.
Package173 proves its ordinary arithmetic/calculus bridge using
`C_ANCHOR_THEOREM.md` plus the sharper
`LABEL_SEPARATION_WITHOUT_DERIVED_RANGE.md`. The latter's boundary-valid
lemma F>=L^t is necessary for the affine multiplier2^20; the earlier
non-sharp paragraph requiring D>d+1 must not be used instead.
Logical calibration is `KEndpoint.c222_iff_zf_refutation`, composed with
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

## Literal request table and edit

Write A=x137+1. The five bases are t=x0, B=x3, BH=x189, q=x100-1,
q+1=x100. Actual abscissae are X=D+Z; retained gates say Z=A*Y.

|base|m|k|D|Y|Z|
|---|---|---|---|---|---|
|t|x2|2^20*x0|x186|x187|x188|
|B|x17|x1|x177|x178|x179+1|
|BH|x100-1|x1|x177|x178|x179+1|
|q+1|x101|x0+x2|x150|x151|x152|
|q|x102|x0|x141|x142|x143|
|q+1|x106|x8-1|x153|x154-1|x155|
|q+1|x109|x9|x156|x157|x158|
|q+1|x112|x10|x159|x160|x161|
|q+1|x115|x11|x162|x163|x164|
|q+1|x118|x12|x165|x166|x167|
|q+1|x122|x13|x171|x172|x173|
|q+1|x125|x14|x174|x175|x176|
|q+1|x130|x15|x180|x181|x182|
|q|x119|x4|x168|x169|x170|
|q|x126|x1|x177|x178|x179+1|
|q+1|x133|2*x16|x183|x184|x185|

There are16 requests and14 unique principal pairs. The growth pair at
2^20*t is distinct from the t pair used for q^t. The semantic anchor is
C=2*x16 and its pair(D,Y,Z)=(x183,x184,x185).

Delete coordinates144,145,146,147,148,149,204,214,215,216,217 and
rows102,103,104,105,106,107,147,153,154,155,156. Every deleted coordinate
occurs only in deleted rows. Retain the other147 quadratic rows, relabel
the208 retained coordinates in increasing order, and append one integer z.

For each base n_j, sum over requests in that group:

    T_j=2*A*n_j-n_j^2-1,
    H_j=sum Y_i*(m_i-X_i),
    S_j=sum ((m_i-D_i)^2-Y_i^2),
    E_j=S_j-2*n_j*H_j.

For the14 distinct pairs define Omega=sum((X_i-1)^2+(Y_i-k_i)^2),
and set d=A-1. Append the one residual

    J=Omega*product_j T_j
      +d*sum_j n_j*E_j*product_(l!=j) T_l
      -z*d*product_j T_j.

The209-variable polynomial is the sum of the squares of147 retained
quadratic rows and J. This is a fixed integer polynomial of degree at
most26, fully defined by `joint209.json`.

## Simultaneous soundness

The retained frame and package173's C-anchor argument, before either
orientation or power recovery, give W>=258, |A|>W^W and
k_i^2,n_j^2,m_i^2,C^2<W. The private comparison congruences first recover
the anchor's classified positive index as |C|; the squared-ordinate
bound bounds all other classified indices. This argument uses none of
the removed rows. The actual index2^20*t is included in the square frame.

Let b=floor(sqrt(W-1))>=16. Every raw principal pair has a representation

    (X_i,Y_i)=epsilon_i*(X_nu_i(A),Y_nu_i(A)),
    epsilon_i in {+1,-1}, nu_i in Z, |nu_i|<=b.

This includes both signs at indexzero. The canonical signed recurrence
modulo d gives X_nu(A)=1, Y_nu(A)=nu. Hence Omega modulo d equals

    o=sum_i ((epsilon_i-1)^2+(epsilon_i*nu_i-k_i)^2)>=0.

For a nonzero base n, gcd(n,T)=1, and
X_i+(n-A)*Y_i=epsilon_i*n^nu_i modulo T. Define
delta_i=m_i-X_i+(A-n)*Y_i. On retained gates the exact identity is

    sum_(group j) delta_i^2=E_j-T_j*sum_(group j)Y_i^2.

The denominator d is nonzero, has sign(A), and |d|>=W^W. At a nonzero
base, |T_j|>W^W and n_j/T_j has sign(A). At a zero base T_j=-1 and its
weighted contribution vanishes. Thus J=0 says that

    Omega/d+sum_(j,i in j) n_j*delta_i^2/T_j

is an integer. Let Cstar=product n_j^b over nonzero base groups, and put

    d_i=Cstar*m_i-epsilon_i*(Cstar/n_j^b)*n_j^(b+nu_i).

Here Cstar is nonzero and every exponent is nonnegative. Multiplying
the integrality assertion by Cstar^2 and reducing numerators in their
individual denominators shows that

    V=Cstar^2*o/d+sum_(nonzero j,i in j) n_j*d_i^2/T_j

is an integer. No coprimality between distinct denominators is used.
All summands have the same sign, sign(A), or are zero. With14 pairs and
16 requests the bounds from package176 apply unchanged:

    o<=120*b^2, |Cstar|<=b^(5*b),
    Cstar^2*o+sum |n_j|*d_i^2
      <=120*b^(10*b+2)+68*b^(12*b+1)
      <=188*b^(12*b+2)<W^(6*b+2)<=W^W.

The last comparisons use188<W, b^2<W, and6*b+2<=b^2+1<=W. Therefore
|V|<1, so V=0. Common signs force o=0 and every d_i=0. The first says
epsilon_i=1 and nu_i=k_i, authenticating the canonical signs and indices;
the second gives m_i=n_j^k_i at every nonzero base. Integer outputs at
|n_j|>=2 exclude negative k_i. This proves orientation and powers
simultaneously, without assuming the orientation to be proved.

## Direct restoration, including zero bases

There is no need to reprove the parent's semantic sign bootstrap. The
new zero restores the old219-coordinate zero directly. At every nonzero
base, exact powers and the canonical Pell congruence give T_j|delta_i,
and the squared-error identity gives T_j|E_j. At a zero base T_j=-1,
so both divisibilities hold automatically. Restore the three old moduli
as T_j and their quotients as -delta_i/T_j. For the q and q+1 groups set

    L_j=E_j/T_j, K_j=2*H_j+(2*A-n_j)*L_j.

Both old pooled rows then vanish. Restore the old orientation quotient
as Omega/(A-1), integral by canonical base-one congruences. The literal
source147 row differs from Omega-(A-1)*Q by minus the sum of14 retained
norm rows. Hence it vanishes as well, and all other rows were retained.
This restores every deleted coordinate with an integer value on zeros.

Conversely, for any219-coordinate zero the retained frame makes every
T_j and A-1 nonzero. The old orientation row and the norm-row identity
make Omega/(A-1) an integer. The old singleton and pooled-power rows make
every E_j/T_j an integer: for a singleton, its old power congruence gives
T_j|delta_i and the squared-error identity gives T_j|E_j; for the two
pools, eliminating K_j between their rows gives E_j=T_j*L_j directly.
Thus

    z=Omega/(A-1)+sum_j n_j*E_j/T_j

is an integer and supplies the new zero. This reverse direction does
not need the semantic interpretation of the old equation either.
The restoration quotients are asserted on zero sets, where their
integrality has been proved. This argument handles zero bases uniformly.

Therefore the209-coordinate equation and the fixed219-coordinate
parent have integer zeros simultaneously. Composing with the parent's
ordinary arithmetic and C222/ZF/ZFC calibration proves in ZFC:

    exists integer zero of the209-variable polynomial
    iff exists a finite syntactic ZFC refutation.

Negation gives the desired Con(ZFC) equivalence. No consistency
assumption or restriction to externally standard proof codes is used.

## Exact monic projections

Each selected retained source row is epsilon*x_v+R=0, epsilon=+1 or-1,
and x_v does not occur in R. Set x_v=-epsilon*R. The selected variable
dependencies are acyclic, so these equations define an integer-polynomial
restoration map from the free coordinates to all209 coordinates.
Selected rows become identically zero. The final polynomial is the sum
of the squares of every remaining row after substitution. Projection and
restoration are inverse on integer zero sets; the pullback of the209
polynomial is the final polynomial as an exact identity.

The85-coordinate profile makes124 unit eliminations and retains24
residuals. The independent projection checker imports neither search nor
producer. It verifies the literal source bindings, pivot units, acyclicity,
every substituted source node, retained rows and final sum of squares.
An explicit integer ray yields a nonzero top homogeneous coefficient
modulo1000000007 in a degree8482 residual. More specifically, retained
source row83 has unique highest-degree term -x79*x95: the restored
coordinates have degrees8198 and284, and respective top-ray residues
46952950 and64682962. Their negative product is140621492 modulo1000000007.
Every other term in row83 has degree at most12. A sum of real polynomial
squares cannot cancel its maximal homogeneous part, proving exact degree
16964. Nonzero derivative certificates prove all85 variables occur.

The inherited logical calibration is identified, not freshly rebuilt.
Finite artifact verification is distinct from the unbounded proof above.
Novelty relative to unread incoming ZIPs is not asserted.
