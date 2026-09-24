# A smaller support layout and a six-operation numeral chain

The construction below preserves the 107 core arithmetic instructions of
`COMPOSED_107_PROOF.md` and reduces the count with literal numerals generated
from 1 from 114 to 113. It changes the fixed encoding indices and replaces
the intermediate computation of `4a-5` by `4(a-1)-1`. The source polynomial
of that congruence is identical. Previous constructions are unchanged.

The complete core and strict schedules, all primitive identities, and all
source residual identities are checked by
`../verification/round13_1980_certificate.py` and serialized in its JSON.

## Modular pair-sum positions

For each integer `0<=i<=59`, let `r_i` be the least nonnegative residue of
`i^2` modulo the prime 61, and define

    a_i = 122i+r_i,
    v_i = 1+3a_i.

The sums `a_i+a_j` distinguish all unordered pairs of indices, including
repeated indices. Indeed, `0<=r_i+r_j<=120<122`, so Euclidean division by
122 recovers both the exact integer sum `s=i+j` and the sum `r_i+r_j`.
Over the field with 61 elements, these determine

    i+j=s,    i^2+j^2=r_i+r_j,
    ij=(s^2-r_i-r_j)/2.

Division by 2 is legitimate in this proof because 61 is odd; it is not
an arithmetic instruction in the final certificate. The monic polynomial
`X^2-sX+ij` determines its unordered pair of roots. Every index belongs to
`{0,...,59}`, a set of distinct residues modulo 61. Thus the integer pair
itself is recovered. This proves the pair-sum property uniformly, rather
than inferring it only from the finite enumeration in the checker.

All positive weights `v_i` are 1 modulo 3. Hence zero, a single positive
weight, and a pair of positive weights are distinguished modulo 3. Within
each class, the preceding pair-sum argument or the strict increase of
`a_i` gives uniqueness. Therefore

    {0}, {v_i}, {v_i+v_j : i<=j}

are mutually disjoint sets, with altogether `1+60+1830=1891` elements.
These are exactly the monomial weights of homogeneous degree two in the
61 coordinates of `INPUT_UNIT_PROOF.md`: the input has weight zero;
`delta` has weight `v_0=1`; the original 58 witnesses have weights
`v_1,...,v_58`; and the guard coordinate `u` has weight `v_59`.

## Row positions and all support margins

Keep 1832 row targets, comprising the 1830 homogenized original rows,
the guard `u delta-x^2`, and the special target `delta^2`. The new values are

    v_* = 21607,
    D_step = 4v_*+1 = 86429,
    T_first = 1833 D_step+2v_* = 158467571,
    t_r = T_first+r D_step,     0<=r<1832,
    t_* = 316719070,
    K = t_*+1 = 316719071,
    L = 2^32 = 4294967296.

They satisfy the complete support conditions used by the prior proof:

    D_step > 2v_*,
    T_first-2v_* > v_*,
    2T_first-2v_* > t_*,
    3K+2 = 950157215 < 2^30 < L.

Every residual coefficient occupies a complementary position
`t_r-(v_i+v_j)`, where either factor may instead have weight zero. These
positions are nonnegative. Distinct rows have disjoint support intervals
`[t_r-2v_*,t_r]`; different monomials of one row have distinct positions.
For an ordinary residual, retain the coefficient `2a/c`, where `a` is
its integer coefficient and `c` is its multinomial coefficient in the
square of the coordinate code. Thus its row target is still twice that
residual. The special row places coefficient 1 at `t_special-2` and
still produces precisely `delta^2`.

No other row can contribute to a given row target: each product of a
coefficient term and an ordinary quadratic code monomial has weight
within `2v_*` of its own row target, and the row spacing is larger than
`2v_*`. Each coefficient term has weight at least `T_first-2v_*>v_*`,
so the low coordinate tests are automatic zeros. A product involving a
dummy coordinate has weight at least `2T_first-2v_*>t_*`, so no dummy
coordinate can influence any row target. These are precisely the support
facts required for the homogeneous decoding argument.

There remain 1892 encoded non-input coordinates and 1893 coordinates
including the input. The strict coefficient-sum bound `1900b` is unchanged.
With `D(B)` denoting the newly positioned signed coefficient polynomial,
choose the fixed power of two `z>=2` strictly above its absolute
coefficients, put `Z=2z`, and define the new fixed indices by

    ell_0(B) = sum_{i=0}^{59} B^(v_i)+sum_{r=0}^{1831} B^(t_r),
    e_0(B) = z sum_{j=0}^{K-1} B^j+D(B),
    V = ell_0(Z)+e_0(Z) Z^L,
    H > max(2Z^(2L+1),4^(t_*+3) Z 1900^2,3L,16),

where `H` is a power of two. The indices `Z,V,H` are fixed effectively
from the represented set, independently of the queried input. Their
construction is unchanged apart from their new support positions and
exponent; they remain supplied parameters in both complexity conventions.

All canonical degree estimates and the high-mask uniqueness argument
continue to hold. In particular `e,C<B^K` and `L>3K+2` give `2eC^2<q`
after `q=B^L` is decoded. The possible alias `(B-4)m` has degree at most
`t_*+1`, so evaluation of its digit polynomial at 4 is still strictly
smaller than `B-4` by the displayed bound on `H`. Thus the same proof
forces the alias to vanish. The target coefficient argument still
forces every ordinary residual to zero and `delta=1`.

## The exponent may be even

The published 107-operation Pell block requires no oddness assumption
on `L`. Its signed Pell congruence uses the odd index `J=2r+1`, which
is unchanged. Its other norm and index congruence use

    kappa^2(a^2-1)+1=mu^2,
    kappa=L+Delta(a-1).

The elementary congruence `psi_a(t)=t modulo(a-1)` holds for every
nonnegative integer `t`. The proof in `PELL_RELAXED_RADIX_PROOF.md` uses
only `0<L<J<a` to recover `kappa=psi_a(L)`; the fixed bound `3L<B<=n<=r`
still guarantees that range. Necessity chooses this same value of
`kappa`. Its quotient `Delta=(psi_a(L)-L)/(a-1)` is a positive integer
because `a>1` and `L>1`; the gap `c>kappa` follows from `J>L`.

The exponent comparison also remains unchanged:

    B^(3L)<=B^B<=n^n<=U^r<a.

Consequently the exponent congruence still yields `q=B^L`. Neither the
Pell parity argument nor the binary digit masks require `L` odd:
`B` is a power of two, so `q` and `n=q^8` remain powers of two for every
positive integer `L`. The odd-root factorization uses the odd Pell
parameter `P=2Q+1` and the index `r+1`; it is independent of the parity
of `L`. Thus the entire sufficiency and positive-witness necessity
arguments apply to the new exponent.

## The complete count

The 107-operation schedule already computes `am1=a-1` for the shared
Pell coefficient `(a-1)(a+1)`. Move this computation before the E14
congruence and replace its two instructions

    a4=4a,             a4m5=a4-5

by

    a4=4am1,          a4m5=a4-1.

The result is identically `4a-5`, and the number of core arithmetic
instructions remains 107: 59 multiplications and 48 additions when
subtractions are expressed as reversed additions with supplied integer
auxiliaries. The only literal numerals remaining are `1,2,4,L`.

Starting with 1, compute

    two = 1+1,
    four = two*two,
    s4 = four*four,
    s8 = s4*s4,
    s16 = s8*s8,
    L = s16*s16.

This uses one addition and five multiplications, for six instructions.
Substituting these registers at every occurrence of a literal gives a
complete certificate with only literal 1 and exactly 113 arithmetic
instructions: 64 multiplications and 49 additions. It has the same
34 positive unknowns and 22 equality tests. The JSON contains this full
strict primitive certificate as well as the 107-operation core schedule.

No optimality of the encoding or overall count is claimed. For this
particular exponent, however, six numeral instructions are necessary:
starting from 1, the largest positive integer obtainable after five
additions or multiplications is at most 65536. The displayed six-step
chain reaches `2^32`.
