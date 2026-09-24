# Four-cell lifting with exactly preserved period lattices

Every finite-alphabet relation on a 3-by-3 window has an effectively
constructed four-cell presentation on **left, center, right, next**,
without changing the coordinates or any period. The alphabet consists
of vertical triples. Overlap constraints make every globally valid
triple configuration exactly the lift of its middle projection.

This is a bijection of valid configurations that preserves the entire
period lattice, including diagonal periods and torus dimensions one or
two. It therefore transfers the independently padded marked-tableau
theorem to a four-cell finite relation without any macrocell scaling.
The alphabet and rule still depend on the machine and its finite input.
No arithmetic operation count or fixed raw-input universal certificate
is claimed.

The [checker](../verification/explore_four_cell_period_lift.py) and
[receipt](../verification/explore_four_cell_period_lift.json) give bounded
exact evidence separately from the general proof below. The existing
marked-tableau source is imported without changing it.

## 1. The local construction

Let `A` be a nonempty finite alphabet, and let

    R subset A^{3 by 3}

be a local relation. A configuration `a:Z^2->A` is valid when its window
centered at every `(x,t)` belongs to `R`. Window coordinates are ordered
by vertical offsets `-1,0,1` and horizontal offsets `-1,0,1`.

Take the new alphabet `B=A^3`, with a symbol written
`b=(b_-,b_0,b_+)`. Define the four-cell relation

    R4(left,center,right,next)

by precisely these requirements:

1. The 3-by-3 array whose columns are `left,center,right` belongs to `R`.
2. `next_-=center_0`.
3. `next_0=center_+`.

The third coordinate of `next` is unrestricted by this particular local
test; it is governed by the tests at later centers. This is a finite
local relation, not a claim that `next` is a deterministic function of
the three current symbols.

The construction is effective. There are `|A|^3` possible triple symbols,
and each allowed original window determines its three column symbols
uniquely and permits exactly `|A|` choices for the last coordinate of
`next`. Thus `|R4|=|R| |A|` as a set of ordered quadruples. Equality among
actual cells in a small torus is imposed by evaluating this same relation
at the identified coordinates; the construction does not assume that
the four positions are distinct.

## 2. Global bijection and its inverse

Define the vertical lift

    L(a)(x,t)=(a(x,t-1),a(x,t),a(x,t+1))

and the middle projection

    pi(b)(x,t)=b_0(x,t).

If `a` is `R`-valid, its lift satisfies the first `R4` condition because
the three current triples are exactly its original 3-by-3 window.
It satisfies both overlap equations by their definitions. Hence `L(a)`
is `R4`-valid, and `pi(L(a))=a`.

Conversely, suppose `b` is `R4`-valid everywhere, and put `a=pi(b)`.
The overlap equation at `(x,t-1)` and the other overlap equation at
`(x,t)` give

    b_-(x,t)=b_0(x,t-1)=a(x,t-1),
    b_+(x,t)=b_0(x,t+1)=a(x,t+1).

Thus `b=L(a)` exactly, including both outer components of every triple.
The window condition in `R4` now proves that `a` is `R`-valid. In
particular, no extraneous triple track survives in a global solution.

The maps `L` and `pi` are therefore inverse bijections between the two
sets of valid configurations. The conclusion is also valid when either
set is empty.

## 3. The exact period lattice is unchanged

For a configuration `a`, define

    Per(a)={(u,v) in Z^2:
              a(x+u,t+v)=a(x,t) for every x,t}.

Both `L` and `pi` commute with every translation of `Z^2`. A period of
`a` is therefore a period of `L(a)`. Conversely, a period of `L(a)` is
a period of its middle projection `a`. Consequently

    Per(L(a))=Per(a).                                   (1)

This is equality of the full subgroups, not just preservation of two
chosen rectangular periods. It includes minimal axis periods, diagonal
periods, and the index of a full-rank period lattice.

For every pair `W,H>=1`, the construction gives an inverse bijection
between valid configurations on the `W`-by-`H` torus. All formulas are
evaluated modulo the dimensions, and the proof in Section 2 is unchanged.
At height one, every valid triple is `(a,a,a)`. At height two, its first
and third components are equal to the other row's middle component.
These are consequences of the same overlaps, with no extra cases or
discarded solutions. Widths one and two are treated by the same repeated
horizontal coordinates in the original and lifted windows.

In particular, if a family has a valid torus for every sufficiently large
width and height independently, its four-cell presentation has exactly
that same property, with the same thresholds and no period multiplier.

## 4. The marked-tableau marker becomes one fixed triple symbol

Use the alphabet and local relation of the
[marked periodic Turing-machine tableau](EXPLORATION_MARKED_PERIODIC_TM_PADDING.md).
Its boundary symbols are unique: write `V` for the vertical boundary
symbol with bits `(v,h)=(1,0)`, and `X` for the intersection with
`(v,h)=(1,1)`. Neither carries a tape or initialization payload.

In any valid original configuration with `X` at `(x,t)`, the vertical
boundary bit equals one at both `(x,t-1)` and `(x,t+1)` by propagation.
The horizontal boundary bit at both positions is zero: one neighbor is
excluded by the nonadjacency clause at `(x,t)`, and the other by that
clause at `(x,t-1)`. Since the boundary symbol with pair `(1,0)` is
unique, both neighbors are exactly `V`. Therefore

    a(x,t)=X  iff  L(a)(x,t)=(V,X,V)                    (2)

on valid configurations. The reverse implication follows immediately
from the middle projection. Define the one fixed lifted marker

    X4=(V,X,V) in A^3.

Even when the torus height is two, the two occurrences of `V` refer to
the same adjacent row and (2) remains correct. A height-one configuration
cannot contain `X` under the original nonadjacency rule; the lift neither
creates nor removes a marked witness in that case.

An unmarked valid configuration remains unmarked. Replacing the
existential occurrence of `X` by occurrence of `X4` is thus exact; it
does not replace the acceptance predicate by unmarked local validity.

## 5. Transferred halting and consecutive-padding theorem

The marked-tableau theorem effectively associates to each deterministic
Turing machine `M` and finite input `w` a finite alphabet, a 3-by-3 local
relation, and the marker `X`, with these properties:

* a totally periodic valid configuration containing `X` exists exactly
  when `M` halts on `w`;
* in a halting instance, valid marked tori exist for every width `W>=W0`
  and every height `H>=H0`, with the choices independent.

Apply the construction above. By the global bijection, exact period
identity (1), and marker identity (2), the same statements hold for the
four-cell relation and marker `X4`, with the same `W0,H0`. No simulation
time dilation, alphabet-to-macrocell conversion, or period enlargement
is involved. Soundness still rests on the original marked finite
rectangle with exact initialization, no head escape, and a halting top
row; the lift adds no way to evade those conditions.

Choose `h` so large that `h+1>=W0` and `h>=H0`. The resulting
`(h+1)`-by-`h` torus can be indexed cyclically through

    (x mod(h+1),t mod h) -> -hx-(h+1)t mod h(h+1).

Reduction modulo the two consecutive dimensions proves that this map
is a bijection. If the cyclic word is `b_i`, its four-cell constraints
have exactly the form

    R4(b_{i+h},b_i,b_{i-h},b_{i-h-1}).                   (3)

The marker occurs at some cyclic index. Conversely, for any positive
length `N` and stride `h`, a cyclic word satisfying (3) pulls back by

    b(x,t)=b_{-hx-(h+1)t mod N}

to a valid totally periodic four-cell configuration. The index map is
surjective: `(x,t)=(i,-i)` maps to `i`. Hence an occurring cyclic marker
is attained in the pullback, and the original machine halts. Soundness
does not require imposing `N=h(h+1)`; that is a completeness choice.

This proves a uniform reduction to the **marked finite-table four-cell
cyclic problem**, with the finite alphabet and relation compiled from
`M,w`. It does not produce one fixed small rule with a paid raw-input
arithmetic compiler. Symbol coding, relation constants, marker tests,
word geometry, and the full positive arithmetic interface remain
separate obligations. Nor does this transfer establish the same padding
property for Rule 110 or Life.

## 6. Exact finite evidence

The checker tests all 4,096 binary four-triple tuples under both possible
membership values of their original window. Exactly 1,024 satisfy the
overlap constraints, covering all 512 original binary windows twice.

It exhausts **537,736 arbitrary triple fields** over ten small torus
shapes, including widths and heights one and two. Exactly 202 satisfy
overlap; these are precisely the lifts of the 202 corresponding ordinary
binary fields. Every translation residue is checked for equality of the
two period groups. Positionwise window reconstruction is checked on all
those original fields, followed by 1,616 torus checks for eight selected
generic local predicates. The general equivalence for an arbitrary
predicate follows from the proved equality of each reconstructed window.

The imported tableau builder supplies four distinct halting examples,
including a zero-step halt with minimal height two. For each example,
25 independently padded tori are lifted, giving **100 marked padded
tori**, 100 rectangular repetitions, and 100 rejected inconsistent
triple corruptions. Each marked cell has exactly the fixed triple
`(V,X,V)`, and all translation residues preserve the period comparison.
Twenty consecutive-dimension cyclic presentations check (3) directly.
An original valid unframed configuration remains locally valid but has
no lifted marker.

Running without `--write` recomputes the receipt and requires exact JSON
equality. These finite examples corroborate the implementation and
conventions; Sections 1--5 prove the arbitrary-alphabet, arbitrary-period,
and halting-reduction statements.

Independent scoped mathematical/source review confirms the inverse
overlap reconstruction, equality of full period lattices, the unique
lifted marker, and the signs of the consecutive cyclic indexing. A fresh
independent default run reproduces the saved receipt. The finite-table
dependence on both machine and input is retained in the result's scope.
