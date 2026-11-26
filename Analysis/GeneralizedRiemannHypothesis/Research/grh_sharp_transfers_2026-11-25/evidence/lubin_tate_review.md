# Lubin–Tate extension: independent mathematical check

## Statement

Let K/Q_p be finite, O_K its integers, π a uniformizer, q its residue-field
cardinality, and v normalized by v(π)=1. Let F be a one-dimensional
Lubin–Tate formal O_K-module. Let Z_h be the coordinates of its points of
exact π^h-order. Put e_h=(q−1)q^(h−1), r_h=1/e_h.

For h0>=1 and ρ>=r_h0, the exact minimum radial Gauss variation
G_ρ(g)−G_0(g) of a nonzero Cp polynomial that satisfies
v(g(z))>G_ρ(g) at every z in Z_h, h0<=h<=H, is

    (H−h0+1) q^(1−h0).

Hence an integral polynomial with G_ρ<=B admits a successful primitive
torsion specialization at an index

    h0 <= h <= h0 + floor(q^(h0−1) B).

The same endpoint holds separately in every coordinate of an arbitrary
finite-dimensional bounded integral power series, and for aggregate packets.

## Known structural inputs and sources

1. The π^h-torsion O_K-module is isomorphic to O_K/π^h. Fixing a generator
   t_h identifies its primitive points with the units a mod π^h via [a](t_h).
   Kedlaya, Notes on class field theory, Lemma 4.6.12:
   https://kskedlaya.org/cft/sec_lubin-tate.html

2. Primitive points have v-coordinate r_h. They are the roots of an
   Eisenstein polynomial of degree e_h. The same Kedlaya source,
   Corollary 4.6.13 and proof. Also Serban, An infinitesimal p-adic
   multiplicative Manin–Mumford Conjecture, JTNB30(2018), §3.1 pp404–405:
   https://www.numdam.org/item/JTNB_2018__30_2_393_0.pdf

3. Unit linear coefficient formal isomorphisms preserve valuation on the
   open unit disc, so this holds for any integral Lubin–Tate coordinate,
   not just the convenient πT+T^q model. See Kedlaya Remark4.6.11.

Normalize by π explicitly; when K is ramified, v(p) is not 1.

## Exact metric derivation

The integral formal inverse is [-1](Y). The formal difference

    F(X,[-1](Y)) = (X−Y) U(X,Y)

has U in O_K[[X,Y]] and U(0,0)=1. Divisibility follows because substitution
X=Y vanishes; the constant term follows from linearization X−Y.
At points of positive valuation, U has valuation zero. Thus ordinary
coordinate difference and formal-group difference have equal valuation.

For distinct units a,b mod π^h,

    v([a](t_h)−[b](t_h))
      = v([a−b](t_h))
      = r_(h−vπ(a−b)).

The last equality follows because [a−b](t_h) has exact π^(h−vπ(a−b))
order. This is precisely the cyclotomic distance identity with p replaced
by q.

## Why the proof transfers exactly

The unit residue tree has q−1 first-level classes and q children at every
later level. Therefore a least-occupied branch contains at most
floor(m/e_j) marked points at depth j. Its shell maximum is

    U_h(m) = e_h^(-1) Σ_(j=1)^(h−1) e_j floor(m/e_j),   m<e_h,

with U_h(e_h)=infinity.

Balanced prefix enumerations exist: choose a residue-field digit
representative system, let the nonzero first digit run fastest, then the
second digit, and so on. Every consecutive block of e_j representatives
contains every unit class mod π^j once. This substitutes for ordered
integer unit exponents and attains the same floor-sum bound.

All subsequent ingredients are purely radial: ordinary polynomial root
factorization, Gauss multiplicativity, strict ultrametricity off a shell,
and the identity with M_h=e_(h−h0+1),

    U_h(M_h−1)
       = ((h−h0)M_h−(q^(h−h0)−1))/e_h.

The same greedy lower bound forces M_h roots per blocked shell, at cost
M_h/e_h=q^(1−h0). The same balanced-root polynomial attains this cost.
Coordinate induction and uniform truncation require only positive
valuation of the finite grid and integral coefficients, so they transfer.

## Scope / novelty

A search over all retrieved 31 prior report archives found no Lubin–Tate
version of the sharp selector. This extends the exact arithmetic statement
to local formal groups beyond cyclotomic torsion. It does not prove a new
Manin–Mumford classification (Serban already treats Lubin–Tate groups), nor
does it construct any missing Selmer or automorphic interpolation data.

