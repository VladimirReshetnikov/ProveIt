# Residue orientation and an integral Pell-coordinate elimination

Independent ordinary mathematical review for the current research iteration.
The contribution is the explicit composition of source136's linear residue
orientation with an integral unit-coordinate elimination in the current
source. The preferred exported equation uses that linear form. A triangular
variant is also proved and compared exactly. The underlying orientation idea
is credited in Section6; no literature-wide priority or new proof-assistant
formalization is claimed.

## 1. General signed-Pell orientation theorem

For an integer A with |A|>1, define C_n(A), S_n(A), for every n in Z, by

    (A+sqrt(A^2-1))^n = C_n(A)+S_n(A)*sqrt(A^2-1).

The inverse unit has integer coefficients. Recurrence, including inverse
recurrence for negative n, gives

    C_n(A)=1 (mod A-1),     S_n(A)=n (mod A-1).             (1)

Let M=A-1. Suppose r<=17 principal Pell pairs and nominal integer indices
k_i satisfy the following hypotheses established WITHOUT the orientation
condition under discussion:

* every pair satisfies X_i^2-(A^2-1)Y_i^2=1;
* integer Pell classification provides epsilon_i in {+1,-1} and n_i in Z
  with (X_i,Y_i)=epsilon_i*(C_n_i(A),S_n_i(A));
* |n_i|<W, |k_i|<W, W>=258, and |M|>4W^3.

The classification itself holds for every integer Pell solution at |A|>1.
The essential additional hypothesis is the uniform bound on the classified
indices. It must be obtained from the retained cap/anchor before orientation.

Then each of the following conditions is equivalent to canonicity of every
pair at its nominal signed index, namely
(X_i,Y_i)=(C_k_i(A),S_k_i(A)) for all i:

    M divides sum_i[(X_i-1)^2+(Y_i-k_i)^2];                 (2)

    M divides sum_i[X_i(X_i-1)+(Y_i-k_i)^2].                (3)

    M divides sum_i[1-X_i+(Y_i-k_i)^2].                    (3L)

Condition (2) is the inherited squared orientation. Condition (3L) is the
linear orientation of source136, here applied to all fourteen pairs with
signed A. Condition (3) is a triangular variant. The polynomial X(X-1)
is twice an integer triangular number; no division by two is used.

### Proof

Put rho_i=epsilon_i*n_i. By (1), X_i=epsilon_i and Y_i=rho_i modulo M.
Both the triangular sum in (3) and the linear sum in (3L) are congruent
modulo M to

    E_tri=sum_i[epsilon_i(epsilon_i-1)+(rho_i-k_i)^2].

Indeed epsilon_i(epsilon_i-1)=1-epsilon_i is either 0 or 2. Hence

    0 <= E_tri < 4rW^2+2r < 4W^3 < |M|.                  (4)

The middle strict inequality follows from r<=17 and W>=258; even
68W^2+34 is strictly less than 4W^3. Divisibility forces E_tri=0.
Every summand vanishes, so all epsilon_i=+1 and rho_i=k_i. Thus n_i=k_i,
giving canonicity. Conversely, canonical pairs satisfy X_i=1 and Y_i=k_i
modulo M; both sums are divisible by M. This proves (3) and (3L).

The proof of (2) is identical, using sign errors (epsilon_i-1)^2 in
{0,4} and the still sufficient bound 4rW^2+4r<4W^3.

All these arguments use |M|. They remain valid for negative A. In that
case C_n(A) may be negative, so epsilon_i is the sign relative to the
SIGNED-PARAMETER canonical Pell pair; it must not be identified with the
ordinary sign of X_i. No positive-index or positive-abscissa assumption is
introduced.

## 2. The algebraic reason the linear orientation saves a variable

Let Z_i=A*Y_i be retained multiplication wires, and let

    N_i=X_i^2-Z_i^2+Y_i^2-1

be the corresponding quadratic norm residuals. In difference coordinates
D_i=X_i-Z_i, the preferred linear orientation residual is simply

    R_lin=sum_i[Y_i^2-D_i-Z_i-2k_iY_i+k_i^2+1]-M*Q.     (5L)

Every D_i occurs with coefficient -1 and nowhere else in this row. Thus
R_lin=0 is equivalent over the INTEGERS to

    D_j=sum_i[Y_i^2-Z_i-2k_iY_i+k_i^2+1]
        -sum_(i != j)D_i-M*Q.                            (7L)

The right side is an integer polynomial independent of D_j. Substituting it
in every other row and deleting R_lin removes one variable and one residual,
with an exact integral inverse lift. No division or domain change occurs.

For comparison, the triangular form gives the exact polynomial identity

    sum_i[X_i(X_i-1)+(Y_i-k_i)^2] - sum_i N_i - M*Q
     =sum_i[Z_i^2-X_i-2k_iY_i+k_i^2+1]-M*Q.              (5)

Consequently, under the retained equations N_i=0, triangular orientation
can be represented by the right-hand side of (5), a quadratic residual.
Writing the existing difference coordinates as D_i=X_i-Z_i gives

    R_tri=sum_i[Z_i^2-D_i-Z_i-2k_iY_i+k_i^2+1]-M*Q.      (6)

Every D_i has coefficient -1 in this row and occurs nowhere else in it.
Pick one j. The equation R_tri=0 is equivalent, over the INTEGERS, to

    D_j = sum_i[Z_i^2-Z_i-2k_iY_i+k_i^2+1]
          -sum_(i != j)D_i-M*Q.                         (7)

This is another valid unit pivot. Names of all substituted expressions are
arithmetic abbreviations, not additional quantified variables.

For contrast, the corresponding norm-reduced SQUARED orientation has
coefficient -2 on each D_i. A direct elimination from that row would
require an unproved evenness/division step. Replacing the squared orientation
by the known linear residue penalty provides the integer unit. The triangle
is a convenient equivalent presentation, not a separate underlying principle.

The substitution is quadratic in the raw coordinates. The selected Pell
norm becomes a quartic residual, hence may yield an octic sum-of-squares
equation. In a source with an already higher-degree pooling residual, or
after further exact projections, the actual final degree must be audited
from the COMPLETE emitted polynomial circuit. No old degree is inherited
without that audit.

## 3. Exact old/new quotient maps

For the preferred linear form, the full linear sum minus the full squared
sum is -sum_i X_i(X_i-1). At every old zero the squared orientation theorem
gives canonicity, hence M divides every X_i-1. Therefore the forward map is

    Q_lin=Q_old-sum_i X_i(X_i-1)/M.                       (8L)

Conversely, linear orientation gives the same canonicity, and

    Q_old=Q_lin+sum_i X_i(X_i-1)/M                        (9L)

is an integer restoring the old squared row. Every other retained coordinate
is unchanged. These maps are inverse on the corresponding zero sets.

The triangular variant has the following companion maps.

The squared sum and triangular sum differ by sum_i(X_i-1). At every old
zero the inherited orientation theorem gives canonicity, hence each
X_i-1 is divisible by M. If Q_old is the old orientation quotient, set

    Q_new=Q_old+sum_i(X_i-1)/M.                           (8)

This is an integer and annuls the new triangular row; every other shared
coordinate is unchanged. Conversely, at a new zero the theorem in Section1
gives canonicity, so

    Q_old=Q_new-sum_i(X_i-1)/M                            (9)

is integral and restores the old orientation row. Thus old and triangular
systems have the same projected solution set and mutually inverse quotient
maps on zeros. These are proved exact divisions in the MATHEMATICAL witness
maps, not operations in the emitted equation. No claim of identical
polynomials at identical arbitrary coordinates is made.

After either unit pivot (7L) or (7), the corresponding 206-coordinate system
and its 205-coordinate projection are related by an everywhere-defined integer
polynomial restoration. Their sum-of-squares polynomials agree after that
restoration because the omitted row becomes identically zero. Further
monic projections have the same exact algebraic status.

## 4. Actual source173/Cofinal bindings

The inspected parent is pooling/oriented_pool/principal206.json in the
imported ConZFC_Cofinal_Pell_Compression_2026-10-25 archive. Its SHA-256 is

    7da179bedf0e072d01655aeb174516e94809294d67218b3db1c66a817f631e67

It has 206 unrestricted integer coordinates and 145 residuals. In its
ZERO-BASED coordinate numbering, the chosen pair and modulus are

    D_j=x142,  Y_j=x143-1,  Z_j=x144,
    X_j=x142+x144,  k_j=x8-1,
    A=x132+1,  M=x132,  Q=x193.

The existing fourteen principal norm residuals are 95,97,99,...,121.
The chosen pair's norm is residual99; its multiplication row is residual98.
The old pooled orientation quotient x193 occurs only in residual135.
Every displayed offset is material: neither Y_j=x143 nor k_j=x8 is correct.

The stored orientation residual135 is already norm-reduced:

    R_old=sum_i[(X_i-1)^2+(Y_i-k_i)^2]-sum_i N_i-M*x193.   (10)

The preferred exported LINEAR residual is literally

    R_new=R_old+sum_i[X_i-1+Y_i^2-Z_i^2].                 (11L)

It equals the complete linear expression (3L) minus M*x193 as an exact
polynomial, by (10) and the definitions of N_i. The triangular comparison
residual is

    R_new=R_old+sum_i(X_i-1).                             (11)

The finite source audit must reconstruct every X_i,Y_i,k_i,Z_i, verify
all fourteen norm/wire identities, verify (10), and verify (11) coefficient
by coefficient, using (11L) for the selected source or (11) for the
triangular comparison. The matched 85-variable control instead retains
the original squared row (10).
It must then verify the -1 unit coefficient on x142 and
substitute its full integral expression in every retained residual,
including the degree-12 oriented five-base pooling residual144.

The 205-coordinate source has 144 retained residuals. A later count such as
84 variables is justified only by its separately supplied and audited
acyclic monic-pivot list. In particular, every prior pivot definition must
be independent of the chosen x142 and the old quotient x193 if the prior
pivot order is reused without modification. Variable counts and graph
liveness alone do not establish that independence or the inverse maps.

## 5. Independent audit of the signed-anchor dependency order

The inherited proof is in
pooling/173-crt-index-anchor-215/proofs/C_ANCHOR_THEOREM.md, with the later
cofinal growth modification in the enclosing package. Its semantic anchor
is the actual encoded row-index representative c0 with principal pair (U,V).
In the principal206 chart these are

    c0=2*x16,  U=x172+x174,  V=x173.

This is a DIFFERENT pair from the eliminated pair j. All cap constructor,
comparison, and rank rows125--134 are independent of x142 and x193. The
common squared cap is residual138. It retains Y_j=x143-1, but contains
neither the distinguished abscissa nor the orientation quotient. The frame
row122 also contains neither x142 nor x193. Hence these inputs to the
pre-orientation proof are unchanged by the new unit pivot.

The valid noncircular order is:

1. The odd Pell frame proves W>=258, |A|>W^W, and
   |A-1|>4W^3. Every actual nominal-index square belongs to that frame,
   so |k_i|<sqrt(W)<W. No power interpretation or orientation row is used.
2. The squared anchor bound gives V^2>c0^2 and bounds all other principal
   ordinate squares by V^2. Its ternary slack a^2+b^2+c(c+1) is
   nonnegative for every integer tuple, before any semantic positivity.
3. Integer Pell classification, squared divisibility, and comparison-pair
   transfer identify the anchor's absolute index as |c0|. The proof first
   obtains c0!=0 and |V|=S_|c0|(|A|). Every other classified absolute index
   is smaller than |c0|, hence below W. Positivity of c0 is not assumed.
4. Apply the linear orientation theorem of Section1 with signed A. All principal
   pairs, including the semantic anchor, become canonical at their nominal
   signed indices. The old pooled row is not assumed in this step.
5. Apply the retained oriented reciprocal pooling theorem and its parity
   bootstrap to recover actual powers. Positivity of c0 is justified only
   later through the nonunit radix power request, as in the inherited proof.

The new substitution changes the selected norm and the later power
polynomial only algebraically. At a new zero, the retained norm equations
hold at the reconstructed old coordinates. This is precisely what Steps1--3
require. Thus neither canonical orientation nor a genuine power value is
being used to prove itself.

## 6. Prior source136, exact relation, and logical conclusion

The essential finite-residue idea is inherited. Source136,
`136-local-certificates/signed_section.tex`, subsection "Linear orientation
in a bounded residue pool", explicitly proves

    sum_i(Y_i-k_i)^2 + sum_(i in I)(1-X_i) = (A-1)q,

where its trace residues are 0 or2. It emphasizes that only the small residue
representative is nonnegative and that q must remain unrestricted. That
report applies the lemma to nine of fifteen pairs at A>0 to remove front
sign graphs. Its report.tex also states the general finite-residue viewpoint.
The present fourteen-pair signed-A application and emitted unit-pivot
composition must be compared with, and attributed to, that earlier result.

For all principal pairs, write

    R_lin=sum_i[1-X_i+(Y_i-k_i)^2]-M*Q_lin.

The same proof as Section1 works for negative as well as positive A. Let
L=sum_i Y_i^2 and set Q_tri=Q_lin+(A+1)L. Then the exact identity is

    R_tri(Q_tri)-R_lin(Q_lin)
      =sum_i[Z_i^2-A^2*Y_i^2]
      =sum_i[(Z_i-A*Y_i)(Z_i+A*Y_i)].

All factors Z_i-A*Y_i are retained multiplication residuals. Thus the
triangular norm-reduced form and the linear form are related by an integral
polynomial quotient shear on the retained AY zero set. This demonstrates
precisely why the triangular formula is a convenient variant of source136's
method, not an independent discovery of a wholly new orientation principle.

The completed source-to-source composition and the resulting emitted
equation may be new relative to the inspected repository; no exhaustive
literature or global-minimality claim follows from that fact.

The source-to-source theorem gives an explicit local replacement of an imported direct
C222 consistency equation. The final consistency result composes it with
that parent's ordinary signed-Pell, binomial-CRT, Horn-certificate, and
C222/ZF/ZFC calibration. Those inherited unbounded results are credited
dependencies, not facts established by finite coefficient tests here.

Every new argument is elementary integer arithmetic, finite Pell recurrence
and classification, bounded comparison, and exact polynomial substitution.
It is formalizable in ZFC uniformly over its internally coded finite
objects. No consistency assumption selects coefficients; the construction
neither proves Con(ZFC) nor proves the equation unsolvable independently.

