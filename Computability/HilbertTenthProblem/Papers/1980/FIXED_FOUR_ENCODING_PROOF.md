# A fixed digit alphabet and a 101-operation certificate

This note changes the admissible index of the published 102-operation
system. Its digit parameter is always `Z=4`, and its exponent `L` is now
a fixed component of the index. Consequently the positive input list is
`(x,V,H,L)`, rather than `(x,Z,V,H)`. The index depends only on the
represented recursively enumerable set, and never on the queried input
`x`. The number of decoded circuit coordinates may depend on that set;
they are digits of the same integer code, not new unknowns of the final
polynomial system.

The arithmetic saving is that `theta=B-4`, already required by the digit
congruence, is also the third binary mask coefficient and the shift used
in the second Pell exponential congruence. The separate subtraction
`B-4` therefore disappears. All fixed numerals are free in the complexity
measure. The exact certificate is
`../verification/round23_1980_fixed_four_certificate.py`; its operation
count is to be certified independently of this mathematical proof.

## 1. Compiling arbitrary coefficients into small primitive rows

Begin with any finite polynomial system representing the desired set
over nonnegative integer witnesses and a positive integer input `x`.
In particular, the quadratic-system representation used in the earlier
constructions is sufficient. Split each polynomial equation into an
equality between polynomials with nonnegative integer coefficients.
Evaluate these polynomials by finite circuits using addition,
multiplication, constants zero and one, and copies. Each gate has a fresh
nonnegative output coordinate. Constants can be constructed from one by
finitely many additions, or by binary arithmetic; their circuit size is
irrelevant to the final number of integer-code unknowns.

Repeated operands are replaced by distinct copied coordinates before an
addition or multiplication gate. All circuit coordinates are distinct
from the homogenizing coordinate `delta`. The homogeneous quadratic
rows can therefore be chosen from the following list:

* multiplication: `F=XY-W*delta`, where `X,Y` are distinct coordinates
  and `W` is a fresh output;
* addition: `F=(X+Y-W)*delta`, with distinct summands and fresh output;
* copy or final equality: `F=(X-Y)*delta`, with distinct coordinates;
* zero: `F=X*delta`;
* unit: `F=X*delta-delta^2`.

Here `X` or `Y` may be the input coordinate `x`. The unit row has the
displayed orientation. Constant multiples and negative coefficients
have been eliminated by the circuit construction, not bounded by an
assumption about the represented set. At `delta=1`, the rows are
equivalent to the original equations, and every original nonnegative
solution has a nonnegative extension by its circuit values.

Add a fresh nonnegative coordinate `u` and the guard row

    F_guard=u*delta-x^2.

For every ordinary row, including this guard, use the target polynomial

    G=2*F+delta^2.

Add one special target `G_special=delta^2`. For a homogeneous quadratic
monomial, let its multinomial coefficient be `c_I=1` for a square and
`c_I=2` for a product of distinct coordinates. Every coefficient of
every `G`, divided by its `c_I`, is an integer in

    {-2,-1,0,1}.

For multiplication and addition rows the cross-term quotients are
`+1` or `-1`, and the added `delta^2` has quotient `1`. Distinct copied
operands prevent an unwanted positive square coefficient or a doubled
cross coefficient. The unit row gives
`G=2*X*delta-delta^2`, with quotients `1,-1`. The guard gives
`G=2*u*delta-2*x^2+delta^2`, with quotients `1,-2,1`. The special target
has quotient `1`. Fresh outputs, and omission of trivial identical
equalities, prevent accidental coincidence within a row.

## 2. A finite support layout for any compiled circuit

Let `m` be the number of positive-weight coordinates, including `delta`,
the original witnesses, all circuit coordinates, and `u`. The input
`x` alone has weight zero. Give the other coordinates weights

    v_i=3^i,                  0<=i<m,
    v_0=1 for delta,
    M=3^(m-1).

The weights of all homogeneous quadratic monomials are distinct:
they are zero, one of the `3^i`, or a sum of two such powers. Their
base-three digits recover the unordered pair, including the repeated
case. This proof works for every finite `m` and requires no fixed
dimension bound.

Let `s` be the number of ordinary targets plus the special target. Put

    d=4*M+1,
    t_first=(s+1)*d+2*M,
    t_j=t_first+j*d,          0<=j<s,
    t_last=2*s*d+2*M,
    K=t_last+1.

Choose a power of two `L>3*K+2`. The intervals
`[t_j-2*M,t_j]` are disjoint. Their lowest point is greater than `M`.
Furthermore

    2*t_first-2*M>t_last.

As before, include dummy coordinates at the target positions. Any
quadratic product involving such a dummy, multiplied by a nonzero
coefficient-code term, lies above every target. Thus dummy digits never
alter the tested equations. No dummy is added to the final polynomial
system's list of unknowns.

For each target, put its divided monomial coefficient at the
complementary position `t_j-w(I)` and let `D(B)` be their sum. The
support separation and monomial uniqueness prove that no coefficients
from different rows or monomials collide. Consequently every coefficient
of `D` lies in `{-2,-1,0,1}`, its support is below `K` and above `M`, and

    [B^t_j] D(B)*C(B)^2=G_j

for the decoded coordinate polynomial `C(B)`.

Set

    ell_0(B)=sum_i B^v_i + sum_j B^t_j,
    e_0(B)=2*sum_(0<=j<K) B^j + D(B),
    V=ell_0(4)+e_0(4)*4^L.

Every digit of `e_0` is in `{0,1,2,3}`. Zero digits are allowed. Its
unit digit is exactly `2`, since `D` has no constant coefficient, so
`e_0>0`; also `ell_0>0` and `V>0`. All digits of the packed polynomial
`ell_0(B)+e_0(B)*B^L` are below four and its degree is below `2L`.

Write `c_*=m+s+1`, the number of available code coordinates including
the input. Choose a power of two `H` with

    H>max(2*4^(2L+1), 4^(t_last+3)*4*c_*^2, 3*L, 16).

An admissible index is a triple `(V,H,L)` obtained by these rules from a
finite compiled system. All its choices are made before the input `x`
is queried. They replace the previous index construction in full.

## 3. The polynomial equations and preliminary bounds

Keep the 102-operation system, set every occurrence of `Z` to the
literal `4`, and replace its fixed exponent by the parameter `L`.
In particular, with charged abbreviations `B=H*b^2` and `C=x+g`, use

    b=x+beta,
    lambda*(B-1)=q^2-1,
    theta+4=B,
    Y_code=ell+e*q=V+t*theta,
    Y_code+alpha=q^2,
    Omega=4*lambda-2*e>0,
    sigma=B*lambda*q-Omega*C^2>0,
    n=q^8.

Here `Omega` and `sigma` are existing positive unknowns with equality
tests, and `Y_code` is only an abbreviation. The packing is

    S=g+q^2*(Y_code+q^2*sigma),
    Tplus=q^2*(1+theta*lambda)-(b-1)*ell+theta*ell*q^4,
    r=S*(n^2-n)+Tplus*(n^2-1).

The second exponential congruence uses the same `theta=B-4` in
`a-theta`, where the mathematical main Pell base is `a+4`.

The preliminary proof of the 102-operation system applies with `Z=4`.
Explicitly, `Y_code<q^2` gives `e<q` and `ell<q^2`. The geometric
equation and `H>16` give `B<=q^2`, `q>4*b`, and `3*L<=B<=n`.
Positivity of `Omega` and `sigma` gives `C^2<B*lambda*q<3*q^3<q^4`.
The first block may borrow fewer than `b` units from the middle block;
the latter remains positive because `theta=B-4>b`. With widths `(2,2,4)`
the packed quantities satisfy

    0<S<n,       0<Tplus<=n,
    n<=r<=2*n^3-2*n^2.

These are precisely the pre-decoding hypotheses in
`PELL_COMMON_WITNESS_PROOF.md` and the unit-scale and shared-ratio
proofs on which it depends. The same Pell argument yields powers of
two `b,B,q`, the exact equality `q=B^L`, and the central-binomial
divisibility. The changing numerical value of the fixed index `L`
does not change that argument: the hypotheses it uses are `L>=2` and
`3*L<=B<=n<=r`, both established here.

## 4. Canonical decoding and quotient-alias removal

After `q=B^L`, one has `lambda>q`, so `Omega>2*lambda`. Hence
`C^2<B*q/2<q^2`, and in particular `g<C<q`.

The first-block borrow `d=floor((b-1)*ell/q^2)<b` changes only the
unit digit of `(B-4)*lambda`. The middle no-carry condition therefore
bounds every nonunit digit of `Y_code` by three and its unit digit by
`3+d`. The resulting bound

    ell<=Y_code<4*q^2/(B-1)+b

forces `(b-1)*ell<q^2` by `B=H*b^2` and `H>16`. Thus `d=0`.
The canonical evaluation lemma now applies to the base-four digit
polynomial defining `V`, using `H>2*4^(2L+1)`. It gives

    Y_code=ell_0(B)+e_0(B)*q,
    ell=ell_0(B)+a_alias*q,
    e=e_0(B)-a_alias,          0<=a_alias<e_0(B).

The first mask and `g<q` decode the low coordinate positions using
`ell_0`. In particular every coordinate is less than `b`, the unit
digit of `g` vanishes, and the unit digit of `C` is the input `x`.
If `A_C=C(1)^2`, then

    C(1)<c_*b,       J_C=4*A_C<B/4.

The proof in `HIGH_MASK_SINGLE_OFFSET_PROOF.md` is unchanged. For
completeness, `e,C<B^K` and `L>3K+2` give `2*e*C^2<q`. The polynomial
`4*lambda*C^2` has all coefficients at most `J_C<B`, with a constant
plateau `J_C` in the positions from `L` through `L+K`. Exact division
of `sigma=B*lambda*q-4*lambda*C^2+2*e*C^2` by `q` shows that its
digit at `L` is `B-J_C-1` or `B-J_C`, and its digits at `L+1` through
`L+K` are `B-J_C`. The high part of the third mask is

    X=(B-4)*a_alias,

with degree at most `K`. No binary overlap therefore bounds every
base-`B` digit of `X` by `J_C`. If `F_X` is that digit polynomial,
then `F_X(4)` is divisible by `B-4`, whereas

    0<=F_X(4)
      <=J_C*(4^(K+1)-1)/3
       <B/12
       <B-4.

The strict estimate uses the displayed bound on `H`. It follows that
`X=0` and `a_alias=0`. Thus both supplied codes are canonical. Allowing
some zero digits of `e_0` has affected none of these arguments.

## 5. The smaller target coefficients still force the original rows

Below `K`, the raw coefficients of `sigma` are those of `2*D*C^2`.
Each has absolute value at most

    2*2*C(1)^2=J_C<B/4.

Beginning with incoming carry zero, all carries in this range are zero
or minus one. The binary mask `B-4` permits only the digits `0,1,2,3`.
For a target raw coefficient `v` with incoming carry `epsilon` in
`{-1,0}`, the allowed condition is exactly `0<=v+epsilon<=3`:
a negative value borrows from the next place and has a normalized digit
greater than three.

The special row has raw coefficient `2*delta^2`, so it forces
`delta` to be zero or one. If `delta=0`, the guard row has raw
coefficient `-4*x^2`, which fails because `x>0`. Hence `delta=1`.
Every ordinary row then has raw coefficient `4*F+2`; with either
possible incoming carry it lies in the permitted range exactly when
`F=0`. The compiled primitive rows consequently recover the original
system at the actual input `x`.

Conversely, extend an original solution by its circuit values, take
`delta=1` and `u=x^2`, and choose a power-of-two `b` larger than every
coordinate. Use the canonical codes. All ordinary and special target
raw coefficients are `2`, so their normalized digits are `1` or `2`,
both permitted. The low variable positions have coefficient zero, by
the support separation. Every canonical bound is positive: `e_0<B^K<q`,
`ell_0<B^K<q`, `Y_code<q^2`, and `Omega>2*lambda`. Finally
`4*C^2<B*q` follows from the coefficient bound and `2K<L`, so
`sigma=B*lambda*q-Omega*C^2>0`. The standard positive Pell witnesses
from `PELL_COMMON_WITNESS_PROOF.md` complete the final system. This
proves both directions for all admissible indices.

## 6. Arithmetic consequence

The 102-operation predecessor has one register for `B-4` and separately
tests `theta+Z=B`. In this index `Z=4`, so all uses of the former register
can use the supplied positive unknown `theta`. The equation
`theta+4=B` already proves the required identification. No new arithmetic
operation is introduced by the primitive circuit or its support layout:
they are used only to construct the fixed index `(V,H,L)`. The result
has the same 34 positive unknowns and 22 equations, and one fewer
addition: 56 multiplications and 45 additions, for 101 operations.
