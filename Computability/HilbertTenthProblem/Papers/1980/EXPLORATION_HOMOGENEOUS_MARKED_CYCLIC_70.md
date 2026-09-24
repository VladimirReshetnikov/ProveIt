# A homogeneous one-hot compiler and a 70-operation marked halting-instance system

An alphabet symbol can be represented by one occupied Boolean position.
Local at-most-one tests and occupancy equalities permit the zero state
temporarily; an actual accepting marker forces every cyclic cell to be
occupied. This permits a homogeneous local test, deleting the affine
guard and its two arithmetic operations.

The resulting system has **70=40M+30A**, 27 strictly positive unknowns,
and 17 equations. It is an effective positive Diophantine certificate
for each compiled Turing-machine halting instance. Its constants depend
on both machine and input, so this is an encoded-instance improvement
from72, not an improvement to the89-operation fixed-index raw-input
universal theorem.

The [checker](../verification/explore_homogeneous_marked_cyclic.py) and
[receipt](../verification/explore_homogeneous_marked_cyclic.json) contain
the exact source schedule and finite verification. This proof retains
the complete packing and Pell argument of the
[generic cyclic70 construction](EXPLORATION_MULTIBIT_CYCLIC_CERTIFICATE.md),
but changes the local compiler and pays for a marked occurrence.

## 1. A homogeneous masked test on one-hot states

Let the fixed alphabet have `k>=1` symbols, numbered `0,...,k-1`, with
symbol0 the accepting marker. Let `R4` be an arbitrary relation on four
symbols, in order left, center, right, next. Each site has `k` Boolean
indicator bits `z_si`. Its occupancy is `n_s=sum_i z_si`.

Choose a fixed power of two `A>max(2k,4)`. Form a list of nonnegative
linear clauses, each with a mask inside one radix-A digit:

* For each of the four sites, use value `n_s` and mask `A-2`.
  Since `0<=n_s<=k<A`, this tests `n_s in {0,1}` exactly.
* Use values `n_C+n_L` and `n_C+n_Y`, each with mask1. Under the first
  tests, these values belong to `{0,1,2}`. Their low bit vanishes exactly
  when the two occupancies agree.
* For every forbidden alphabet tuple `(a_L,a_C,a_R,a_Y)`, use value
  `z_L,a_L+z_C,a_C+z_R,a_R+z_Y` and mask4. Its value is in `[0,4]`, and
  its tested bit is set exactly when all four indicated bits are1.

Every clause value is strictly below `A`, even before the at-most-one
tests are assumed. Let `t_j` and `mu_j` be the clause values and masks.
Define

    phi(z)=sum_j A^j t_j(z)=sum_(s,i) c_si z_si,
    mu=sum_j A^j mu_j.                                  (1)

No radix-A carry occurs. Thus `phi AND mu=0` means precisely: all sites
have occupancy at most1; center agrees in occupancy with left and next;
and no forbidden alphabet tuple has all four selected indicator bits1.
When all occupancies are1, this is exactly the intended relation `R4`.
The all-zero bit tuple passes; its eventual exclusion uses the marker
and global overlap, not a nonexistent local nonzero test.

Every coefficient `c_si` is a positive integer because the at-most-one
clause at that site contains the bit with a positive weight. There is
no constant term. Let `m=popcount(mu)`. If `m<k`, append `k-m` clauses
whose value is identically zero and whose mask is1, each in a fresh
radix-A digit. They always pass, and give `m>=k` without changing the
coefficients or truth condition. Here `m` is the number of tested binary
positions, not necessarily the number of clauses.

## 2. One scalar cell per state, with balanced masks

Choose a fixed power of two

    R>=max(2m sum_(s,i)c_si, 2mu)+2,
    p=k-1, H=k+m-2, B=R^(H+1)=2^d.                    (2)

Use `m` Boolean positions per cell. Its first `k` are state indicators;
the others are ignored dummy bits. The encoded scalar and coefficients
are

    Ccell=2 sum_(j=0)^(m-1) z_j R^j,
    Ds=sum_(i=0)^(k-1) c_si R^(p-i),
    MC=B-1-2 sum_(j=0)^(m-1) R^j,
    MF=2mu R^p.                                        (3)

The homogeneous local field is

    Fcell=DL*Lcell+DC*Ccell+DR*Rcell+DY*Ycell.           (4)

The coefficient at degree `p` is exactly `2phi` of the genuine state
bits. Dummy terms have strictly larger degree. Every coefficient is
nonnegative, and their total mass is at most `2m sum c_si<=R-2`.
Thus there are no inner-radix carries, including from off-diagonal
terms. All degrees are between zero and `H`, giving

    0<=Fcell<=B-2.                                     (5)

Consequently `Fcell AND MF=0` tests exactly (1). The state mask types
arbitrary values in `[0,B)` into the indicated Boolean positions.
As in the affine compiler,

    0<DL,DC,DR,DY<B,
    0<MC,MF<=B-2, MC odd, MF even,
    popcount(MC)=d-m, popcount(MF)=m.                  (6)

All encoded cells are even. A genuine alphabet state has one indicator
equal to1 and therefore has value at least2, regardless of its dummy
bits. The marker with zero dummy bits has scalar value2. The fixed
construction has `B>=16`.

## 3. Global occupancy is forced by the actual marker

Suppose a cyclic word of length `N>=1` satisfies the local masks at
offsets `h,0,-h,-h-1`. The center at-most-one tests give an occupancy
`n_i in {0,1}` at every cell. The equality clauses give

    n_i=n_(i+h), n_i=n_(i-h-1).                        (7)

Replacing `i` by `i+h+1` in the second equality shows invariance under
`h+1`; combining it with invariance under `h` gives invariance under1.
Hence every occupancy is the same, for every `N,h`, with no coprimality
assumption on either individual shift and `N`.

If the unit cell is the marker, its occupancy is1. Therefore every
cell contains exactly one genuine alphabet symbol. The forbidden-tuple
clauses then prove `R4` at each cyclic cell. Nonzero dummy bits cannot
replace this reasoning: they do not enter any occupancy, and the unit
marker is imposed as a complete cell value.

## 4. Source equations and the70-operation ledger

Use the same three positive coordinates `q,P,C`, six outer coordinates
`v,J,align,F,alpha,z`, and seventeen kernel coordinates as the generic
cyclic70 source, with one additional positive marker tail `T`. All27
coordinates are now existential. The coefficients are those of (3),
and `E=DR+B*DY` is one fixed numeral.

Construct the same

    Lambda=q^2, D0=q^3, S=C+qF, M=(MC+q*MF)J,
    r=(Lambda-S)(Lambda-1)+M.

Replace the local equation by its homogeneous form and add the marker:

    (B-1)J=q-1, Pv=q, (B-1)align=P-1,
    C+alpha=q,
    P[(DC+E*P)C-F]+DL*C=z(q-1),
    r=(Lambda-S)(Lambda-1)+M,
    C=2+B*T.                                            (8)

Retain exactly the ten fixed-minus Pell equations, the scale `D0=q^3`,
and the counted43-operation kernel from the generic construction. All
computed registers may be signed; all27 supplied coordinates are
strictly positive. The seven outer equations plus the ten kernel
equations give17.

| Part | M | A | Total |
|---|---:|---:|---:|
| Geometry |3|2|5|
| Low-field bound |0|1|1|
| Homogeneous local transport |5|3|8|
| Powers and inverse mask packing |6|5|11|
| Unit marker |1|1|2|
| Outer subtotal |15|12|27|
| Fixed-minus Pell kernel |25|18|43|
| **Complete marked source** |**40**|**30**|**70**|

Deleting `G0*J` and its addition from the generic70 source removes one
multiplication and one addition. The marker restores exactly those two
operations. This is a marked70 system, whereas the earlier generic70
was an unmarked pointwise predicate in supplied `q,P,C`.

## 5. Soundness, including the initially empty cells

The preliminary proof is unchanged: (6), the repunit equation, and
`0<C<q` give `0<M<q^2-1`; positivity of `r` then gives `0<F<q` and
`0<S<q^2`. Thus `q^2<=r<q^4` before any power or cell interpretation.
The retained nonsquare-scale kernel argument gives

    q=B^N, P=B^h, 1<=h<=N,
    q^3 divides binom(2r,r).

The balanced mask weights and inverse-packing identity force

    C AND (MC*J)=0, F AND (MF*J)=0.                     (9)

The first identity types every cell's genuine and dummy Boolean bits.
Some genuine cells might still be empty or have several indicators.
Construct the cyclic neighboring words `L,Rw,Y` and set

    Factual=DL*L+DC*C+DR*Rw+DY*Y.

Bound (5) applies before occupancy recovery and gives `Factual<q-1`.
Its strict lower bound follows from `DC*C>0`, since `DC,C` are positive,
even if all projected indicators were empty. This is the one place
where the homogeneous proof differs from using a positive scalar guard.

The homogeneous local equation in (8) implies `F=Factual mod(q-1)`.
As `0<F<q` and `0<Factual<q-1`, it forces exact equality. The second
mask identity now supplies the clauses in Section1 everywhere. Equation
`C=2+B*T` sets the complete unit cell to the genuine marker with dummy0.
Section3 proves global occupancy1; the forbidden-tuple tests then prove
the intended alphabet relation at every cell. This proves a genuine
marked cyclic configuration without assuming its occupancy prematurely.

## 6. Positive completeness and the full halting reduction

Start with any valid marked cyclic configuration. Rotate its marker to
the unit cell, assign all dummy bits zero, and repeat the word if needed
so that `N>=2`, keeping its stride. The marker tail `T=(C-2)/B` is positive
because every other cell is nonzero. Use the actual homogeneous field
and set `alpha=q-C` and the geometry coordinates canonically.

For the usual wrap quotients,

    PL=C+kL*(q-1), Rw=PC-kR*(q-1),
    Y=BPC-kY*(q-1),

we have `0<=kL<P`, `kR>=0` and, from `C>=2J`, `kY>=2P`. The homogeneous
transport quotient is therefore

    z=P(DR*kR+DY*kY)-DL*kL
      >=2P^2-DL(P-1)>2P^2-B(P-1)>0.                  (10)

All outer coordinates are positive and meet (8). Their masks vanish,
so the actual packed index satisfies `popcount(r)=3dN` and gives the
central-binomial divisibility. It is odd: `C,q,F` are even except that
only evenness of `C,q` is needed, while `MC,J` are odd. Thus `S` is even,
`M` and `r` are odd. Its pre-power bounds still hold.

The seventeen fresh positive Pell coordinates of Section6 of the
generic cyclic proof therefore apply at this actual `r,D0`. That
construction proves every retained equation; no full enormous tuple is
claimed to have been materialized numerically.

Finally, apply the proved marked-tableau compiler and period-preserving
four-cell lift exactly as in the
[marked72 halting theorem](EXPLORATION_MARKED_CYCLIC_72.md). A halting
computation has independently padded `(h+1)`-by-`h` tori, hence marked
cyclic words. Conversely, every marked cyclic word pulls back to a
marked periodic tableau and therefore to a genuine halt on the compiled
input. The change of local arithmetic does not alter any of these
finite-state, marker, period, initialization, or acceptance obligations.

This proves the70-operation halting-instance theorem. Fixing one machine
index before an arbitrary raw integer input varies still requires a
separately counted input connection.

## 7. Evidence and independent review

Independent complete scoped mathematical/source review passes, including
the distinction between a locally empty state and a globally marked
configuration, the positive actual field before occupancy recovery,
all mask counts, the transport quotient, and the complete positive Pell
extension. Author and independent fresh default runs reproduce the saved
receipt exactly. The checker compares all70 primitives and17 residuals,
including the shifted auxiliary-norm correction after marker insertion.

There are10,304 exhaustive scalar cases across singleton, binary and
ternary alphabets, with empty/full relations, Rule110 and a directional
copy rule. Four additional large-alphabet cases exercise six zero-value
padding clauses at alphabet size32, distinguishing clause count from
mask population. The3,348 cyclic cases include90 marked configurations,
of which80 directly give complete positive outer tuples at length at
least2. Length-one repetition is checked separately. There are also71
positive dummy-only words and236 locally valid positive unmarked words;
the actual marker prevents them from becoming false accepted instances.
The retained kernel source is identical to the reviewed43-operation
source, with its prior exact Pell regressions; no full enormous packed
Pell tuple is numerically instantiated.
