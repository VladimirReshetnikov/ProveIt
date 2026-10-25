# A fixed Pell comparison center at the ordinate modulus

This is the ordinary unbounded proof of the deterministic-center part of the
new direct construction. It is separate from the finite checker. The source
is the factored quadratic system underlying the incoming Cofinal Anchors
282-integer equation, at repository commit
`e0c98c629bf10d30b695884f6b1d2ab361bdf513`. Its exact bytes and three relevant
ordinary proof files are retained in `baseline/`.

The predecessor already uses the center polynomial
`D=A+(1-A)H^2` in the independently arriving Certificate Reductions packet,
but there with a doubled frame and a modulus `4C`. The present result shows
that the original signed frame and modulus `C` suffice, including the
exceptional unit-ordinate case. It then combines this simplification with
the independently proved selective nine-term linear orientation pool. No
literature-wide priority or global optimality is asserted.

## 1. The inherited source interface

For an integer center `a>=2`, define Pell polynomials `X_n(a),Y_n(a)` by

    X_0=1, Y_0=0,
    X_(n+1)=a X_n+(a^2-1)Y_n,
    Y_(n+1)=X_n+a Y_n.

The same recurrences define integer polynomials at signed centers. Extend
indices by `X_(-n)=X_n` and `Y_(-n)=-Y_n`. We use ordinary classification of
positive integral solutions of `x^2-(a^2-1)y^2=1` by these sequences.

The retained frame, squared cap, fourteen main norms, and genuine power
requests have the following consequences before interpreting any power:

* `W>=258`, every actual base, requested index and output atom has absolute
  value less than `W`, and `a=|A|>W^W`.
* `|A-1|>4W^3`.
* The anchor pair satisfies `U^2-(A^2-1)C^2=1`.
* Its proposed index is a signed integer `h` with `|h|<W`.
* The squared cap is

      C^2=h^2+1+sum_nonanchor y_j^2+u^2+v^2+w(w+1).

  All its terms after `h^2` are nonnegative on the integers. Consequently
  `C!=0`, `|h|<|C|`, and every nonanchor ordinate has magnitude less than
  `|C|`.

The common pair has

    H^2-(A^2-1)J^2=1,       J=C^2(2e+1),

where `e` is unrestricted. Therefore `J!=0` and `C^2` divides `J`. None of
`A,U,C,H,J` is assigned a positive sign at this stage.

## 2. The exact replacement

The old private comparison construction was

    D=1+4J(2d+1),   D=A+Hf,
    S^2-(D^2-1)R^2=1,
    S=U+Hg,        R=h+4Cq.

Replace the first and last rows by

    f=(1-A)H,      R=h+Cq.

Retain `D=A+Hf`, the comparison norm and the abscissa congruence. These are
quadratic rows, and the coordinate `d` becomes unused. The definition gives

    D=A+(1-A)H^2
     =1-(A-1)(A^2-1)J^2.

Hence `D=A mod H` and `D=1 mod C` for every signed solution, without a
parity condition on `A` or `H`. Also `|D|>1`: if `A>=2`, then
`D=1-(A-1)(A^2-1)J^2<=-2`; if `A<=-2`, then `D>=10`. The signed Pell
classification at `|D|` is therefore available.

## 3. Two elementary Pell facts, with their exact ranges

### Squared-ordinate divisibility

Suppose `c=Y_i(a)>1`, `i>=1`, and `c^2` divides `Y_l(a)`. The standard
strong-divisibility identity

    gcd(Y_i(a),Y_l(a))=Y_gcd(i,l)(a)

gives `i|l`, because the positive sequence is strictly increasing. This
identity follows from the Pell addition law and Euclid's algorithm, using
`gcd(X_n,Y_n)=1` from the norm. Write `l=ik`. Expanding
`(X_i+Y_i sqrt(a^2-1))^k` and taking its radical coefficient gives

    Y_l/Y_i = k X_i^(k-1) mod Y_i.

Since `gcd(X_i,Y_i)=1`, the premise `Y_i^2|Y_l` forces `Y_i|k`, hence
`c|l`. In fact the stronger `ic|l` holds. The argument depends only on
absolute ordinates, so it applies to `C^2|J` irrespective of their signs.

### Abscissa residue separation

Let `0<=i<l`, `a>=2`, and suppose

    X_j(a)=+/-X_i(a) mod X_l(a).

Then `j=+/-i mod 2l`. To see this, write
`alpha=a+sqrt(a^2-1)` in the quadratic ring. Modulo `X_l(a)`, the norm
identity gives `alpha^(2l)=-1`. Thus

    X_(n+2l)=-X_n mod X_l,
    X_(2l-n)=-X_n mod X_l.

These identities reduce `j`, up to the allowed sign, to an index
`r` between zero and `l`. The case `r=l` would give a zero residue and
cannot equal the nonzero `X_i`. For `r,i<l`,

    X_r+X_i <= 2 X_(l-1) < X_l.

The last inequality follows from the Pell addition recurrence at `a>=2`
and `l>=2`; the trivial boundary case is immediate. Thus the residue
congruence is an equality of the positive abscissas, which forces `r=i`.

This proof is included to make explicit that the result is about a
congruence up to sign and does not presume a positive representative.

## 4. Anchor recovery for ordinate index at least two

Classify the anchor and common norms at `a=|A|`:

    |U|=X_i(a), |C|=Y_i(a),
    |H|=X_l(a), |J|=Y_l(a),       i,l>0.

If `i>=2`, then `|C|>1`, and `|J|>=C^2>|C|` gives `l>i`. Squared
divisibility proves `|C||l`. Classify the comparison pair at `|D|`.
For some `j>=0` and independent signs it is

    S=+/-X_j(D),       R=+/-Y_j(D).

Polynomial base transfer through `D=A mod H` and `S=U mod H` gives
`X_j(a)=+/-X_i(a) mod X_l(a)`. This remains valid for negative `A` or
`D`: `X_j(-a)=(-1)^j X_j(a)`, and the parity factor is absorbed into
the independent sign. Abscissa residue separation therefore gives

    j=+/-i mod 2l.

On the other hand, `D=1 mod C` gives `Y_j(D)=j mod C`, so
`R=h mod C` gives `j=+/-h mod |C|`. As `|C||l`, it follows that

    i=+/-h mod |C|.

The useful sharper range is supplied by Pell growth, not by a larger
residue modulus. For `i>=2`, induction from `Y_2(a)=2a` gives

    Y_i(a)>=i+2a-2.

Since `a>W^W` and `|h|<W`, this implies

    i+|h|<|C|.

The displayed congruence can therefore only mean `i=h` or `i=-h`.
Consequently `i=|h|<W`, and `h!=0`. Every other actual Pell index is
strictly smaller than `i`, by the squared cap and monotonicity.

## 5. The exceptional unit ordinate has no zero

The preceding argument must not be applied at `i=1`. In that case
`|C|=Y_1(a)=1`. The squared cap forces `h=0` and every nonanchor
ordinate to be zero. Thus all actual indices are zero except for the
anchor's index one. They are independently bounded by `W`, without
using a conclusion of the desired index theorem.

For any classified signed Pell pair, its small residues modulo `A-1`
are `s_j in {-1,1}` for the abscissa and `r_j in {-j,j}` for the
ordinate. This holds also at negative `A`. Let `I` denote either all
fourteen pairs or the nine selected CRT-representative pairs. The linear
pool gives divisibility of the ordinary integer

    E=sum_all(r_j-k_j)^2 + sum_(j in I)(1-s_j).

Every summand is nonnegative. In the present exceptional case, the
anchor alone contributes `(+-1-0)^2=1`. On the other hand,

    0<E<4*14*W^2+28<4W^3<|A-1|.

This contradicts divisibility by `A-1`. Thus `i=1` supplies no solution.
The argument also works with the original squared-abscissa pool, using
`sum(s_j-1)^2` and the same frame majorant. It is not a positivity
assumption about the actual large pooled expression.

Combining the two cases proves the exact anchor index and the bounds on
all actual indices under the new comparison equations.

## 6. Canonical ordinates and selective orientation

For the nonexceptional case, all actual indices are below `W`. The same
small-residue argument gives

    0<=E<4*14*W^2+18<|A-1|,

for the nine-term pool. Hence `E=0`. All ordinates are the Pell
polynomials at their actual signed requested indices. The nine selected
abscissas are canonical too. Their requested indices are

    a,b,c,d,S,Sp,u,vq,C0.

The remaining five requested indices are `t,F^2+t,y+1,x,h`.
Their orientations follow from the retained genuine power requests in
the acyclic order proved in `LINEAR_POOL_REVIEW.md`: positive `t`
first orients the common t pair; its second request recovers the raw
factorial power and hence `B>=2,q>=3`. The nine already canonical
representative pairs make all actual representatives nonnegative.
The request with base `B*(1+sum representatives)>=2` has the known
positive output `q>=3`, and therefore forces `x>0` and its canonical
abscissa. The endpoint inequalities then give the old strict amplification
bound. The other three proposed indices are positive, so their genuine
power requests orient them. All later factorial, CRT-range, Horn-flow
and syntactic-refutation steps are unchanged.

This order avoids both a presumption that the shifted stored
representatives are nonnegative and a use of `x>=0` before its proof.

## 7. Completeness, including the odd auxiliary quotient

Start with a finite refutation and the predecessor's cofinal witness
construction. Keep its positive main center `A`, its even dominant
semantic anchor `h`, all semantic-front values, and all canonical main
pairs. In particular `C=Y_h(A)` is even and `U=X_h(A)` is odd.

Choose the common index `l=hC`. Composition gives

    J=Y_l(A)=C Y_C(U).

The binomial Pell expansion, using `U^2-1=(A^2-1)C^2`, gives

    Y_C(U)/C = U^(C-1) mod C.

This proves both integrality of `J/C^2` and its oddness, since `C` is
even and `U` odd. Set `e=(J/C^2-1)/2`, exactly as in the predecessor.
Let `H=X_l(A)` and define

    f=(1-A)H,       D=A+Hf,
    S=X_h(D),       R=Y_h(D).

Although `D` is negative, all new coordinates are unrestricted integers.
Polynomial transfer gives `S=U mod H`, while `D=1 mod C` gives
`R=h mod C`; the unrestricted quotients `g,q` exist. The comparison
norm is automatic. No CRT choice of a new center or parity condition
on `A` is needed.

All canonical abscissa and ordinate errors are divisible by `A-1`.
Thus the private quotient can be freshly chosen for the nine-term
linear pool. No sign constraint was ever imposed on that quotient.
All unchanged guards and all new quadratic rows are satisfied.

This proves both existential directions. It need not preserve private
comparison witnesses pointwise and is not claimed to be a bijection of
complete old and new witness tuples.

## 8. Polynomial and proof boundaries

The source transformation is three literal row replacements. Its new
source has the same variable list; the old `cap.d` is unused. Every
subsequent deleted coordinate has an explicit integral monic restoration
certificate, and final shifts are integer translations. The final
equation is the sum of squares of its complete emitted quadratic
residuals, with every collected coefficient supplied.

The independent finite checker validates the exact source delta,
coordinate restoration, translation, degree, variable count and all
quartic coefficients. Deliberate source and coefficient mutations are
rejected under ordinary Python and Python with assertions disabled.
These checks do not replace the unbounded Pell proof above or the
inherited C222/ZF/ZFC-refutation calibration. Their composition yields
the ordinary proof formalizable in ZFC of the requested equivalence;
no new end-to-end proof-assistant or encoded object-ZFC derivation is
claimed.
