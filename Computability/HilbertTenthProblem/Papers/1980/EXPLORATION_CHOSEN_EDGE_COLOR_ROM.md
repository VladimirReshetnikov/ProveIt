# Chosen-edge color convolution: a twelve-operation route and a remaining flag hole

Choosing one program edge per row removes the old ambiguity in which an
unchosen destination remains as ordinary junk at the main destination port.
There is a precise conditional local verifier with two fixed convolution
tables. Its eliminated route costs **12 operations: 7 multiplications and
5 additions**, two more than the retained cyclic route.

This does not yet justify dropping a zero mask. The incoming table has its
own globally legitimate cross terms outside the common color block. A
coefficient-one term can be absent in a different compatible row and absorb
the same backward nozero perturbation as before. The companion
`../verification/explore_chosen_edge_color_rom.py/.json` checks this hole
exactly. This note claims neither a complete replacement certificate nor a
new universal operation count.

## 1. Fixed edge symbols and the two color tables

Let the fixed graph have edge set E and state set S, with every edge
advancing a fixed serial phase. Associate edge e with an exponent a_e.
Choose those exponents as a common integer step times a fixed integral
Sidon set. The step is a multiple of ell and exceeds the entire color
block, including its trailing padding. Thus all distinct nonzero
differences `a_e-a_i`, not just the exponents themselves, are separated
by at least that step. Require `3^ell > 2|E|`. Scaling a fixed Sidon set
achieves these conditions at no runtime cost. This separated-block realization needs only pair-sum
uniqueness; a B3 set can also be used.

For each state s define a Boolean fixed color with a common unit bit and
one state-specific bit:

    color(s)=1+3^(ell*(s+1)),
    Jcode=sum_(j=0..|S|) 3^(ell*j).

Take d=max a_e, g=3^d. The two fixed tables contain

    Kout = sum_e 3^(d-a_e) [Jcode-color(dst(e))]
           + sign and nozero label monomials,
    Kin  = sum_e 3^(d-a_e) color(src(e)).

The sign and nozero ports are placed in disjoint bands above all color
cross terms, with enough separation for the full edge-coordinate span.
Their coefficients are hs and hz. They belong only to Kout and describe
the source of its active edge. Kin has unit coefficient one, so
`Kin=1 mod3`.

For current edge e and following edge f the desired row equation is

    Kout*3^a_e + Kin*3^a_f
      = g*Jcode + Vrow + hs*signplus(e) + hz*nozero(e).       (1)

Forbid the whole common color block in Vrow, including its ell-grid
padding, and forbid both label ports. Dense off-grid forbidding elsewhere
is harmless. A fresh high fixed bit can still force the frame to exceed
all fixed products.

## 2. What the local verifier proves when the flags are typed

In the common color block the left side is exactly

    Jcode-color(dst(e))+color(src(f)).

Thus (1) with zero junk throughout that block holds exactly when
`dst(e)=src(f)`. If the states differ, there is a missing bit at one
state color and an extra bit at another. Neither can disappear through
the forbidden padding. For a compatible pair, phase advancement gives
e!=f. Sidon difference uniqueness makes every nonzero shifted Kout color
block disjoint from every shifted Kin color block. Each remaining
coefficient is zero or one. The separately placed label bands have the
same property. Consequently the canonical Vrow is Boolean and avoids
all forbidden positions.

There is also a conditional whole-word one-hot argument. Suppose C is
already a Boolean word supported on the edge positions, V has its stated
forbidden support, and the sign/nozero words are already Boolean row-head
words. Let q=R^u, with R a sufficiently large power of three. Once the
cyclic shift below is recovered, N is the same supported word shifted
by one row. The common unit of the color block receives no Kout term
and receives exactly one from each edge in that row of N. Since its
coefficient is at most |E|<3^ell, the forbidden padding forces this
count to equal one. Cyclic shifting then gives one edge in every row
of C as well. Compatibility follows as above.

This argument does not type an omitted flag. An untyped D can place
hz*D contributions in other rows or in these color positions, invalidating
the premises of the row argument. That dependency must not be reversed.

## 3. Elimination, boundary recovery, and the exact ledger

For a cyclic edge history with fixed initial edge code I, define

    R*N=C+I(q-1).

Eliminating N from the summed version of (1) gives

    (R*Kout+Kin)C + Kin*I*(q-1)
      = R[V+g*Jcode*H+hs*Kplus+hz*D].                       (2)

Here H is the usual row-head repunit. The fixed products Kin*I and
g*Jcode are single compiled numerals. Since q-1=twice_J already exists,
the exact primitive schedule is

| Operation | Value |
|---|---|
| multiplication | rk=R*Kout |
| addition | coeff=rk+Kin |
| multiplication | body=coeff*C |
| multiplication | terminal=(Kin*I)*twice_J |
| addition | lhs=body+terminal |
| multiplication | color=(g*Jcode)*H |
| multiplication | sign=hs*Kplus |
| multiplication | zero=hz*D |
| addition | out1=V+color |
| addition | out2=out1+sign |
| addition | out3=out2+zero |
| multiplication | rhs=R*out3 |

The comparison lhs=rhs is free. The preceding route uses 6M+4A; this
one uses 7M+5A. The checker executes both symbolic schedules and verifies
their residuals. If F is the uneliminated row-sum residual and
E=C+I(q-1)-RN, the new residual using twice_J is

    R*F+Kin*E-Kin*I*(q-twice_J-1).

There is no unpaid N divisibility condition after power recovery.
Reducing (2) modulo R, and using gcd(Kin,R)=1, gives C=I mod R.
If 0<C<q and 0<I<R, this reconstructs the positive integer
N=(C+I(q-1))/R<q. It is exactly the cyclic rotation of C's rows.
The checker verifies three finite cyclic words explicitly.

The route count does not include proving all its range hypotheses,
constructing a complete packed mask, or proving a new omitted-flag theorem.
Deleting a mask field therefore cannot yet be credited against these
two extra operations.

## 4. An incoming-table hole survives globally safe forbidden padding

Consider an actual compatible edge pair (e,f). Choose another edge u
outside {e,f}, and a lookup edge v!=u. At the common-unit cross column

    c=d+a_u-a_v,

neither actual table product has a term: uniqueness of nonzero Sidon
differences would require its active edge to be u. But on a compatible
pair (eprime,u), the Kin lookup for v supplies exactly one bit at c.
That is ordinary junk, outside the common color block. Whenever such a
predecessor eprime exists, a fixed forbidden extension preserving every
correct pair cannot forbid c.

The exact maintained example has states of phases 0,1,2,1 and edges

    0:(0,1), 1:(0,3), 2:(1,2), 3:(3,2), 4:(2,0).

Its edge coordinates are [234,252,288,360,450]. All 25 current/following
edge pairs are checked; precisely the six compatible pairs pass. For
the actual pair (2,4), the column

    c=450+252-234=468

is absent. It is present with coefficient one in the correct pair (4,1),
as Kin's lookup-edge-zero common unit. It is on-grid and outside every
forbidden position. Adding 3^468 to the actual row's V preserves both
V and its complete support test as Boolean words.

The zero output exponent is 2268 and the selected width is m=2432.
Put h=632. Then the exact identity

    hz*3^h=R*3^468

moves a perturbation from the preceding row to this hole. The change

    Dnew=Dold-Delta, Vnew=Vold+hz*Delta

preserves V+hz*D. It can therefore occur while C and N themselves
remain correct compatible words. The previous interval repair is
available as well: for a preceding false-zero source 2*3^h and the
following source 3^(h-1)-1, split each source into equal Boolean tracks.
Increasing T by (R-3)Delta/6 makes the first guard row emit one carry;
the next guard row normalizes to R/3+3^(h-1). Both guards remain
Boolean, and 4*3^h<R. The checker verifies those exact local identities.

This is a precise local obstruction to inferring D typing from the
new color verifier. It is not a full false accepting history for this
five-edge graph: that would also require its numerical counter path,
zero endpoints, positivity, all global source bounds, and kernel
interface. Nor does this example classify every possible table-padding
strategy. It establishes that the proposed separated cross-junk/color
construction alone has another globally legitimate unused column.

## 5. Result and evidence boundary

The maintained regression passes 25 exact edge-pair tests, three cyclic
shift examples, both complete operation schedules, the exact elimination
identity, and the on-grid flag-hole/two-row guard calculation. The
conditional compatibility construction is useful, but it has not
removed the omitted-flag soundness obligation. No frozen certificate
has been changed and no new universal bound is claimed.
