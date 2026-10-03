# Removing every idle position from an accepting projective path

For every nonempty macro table, the canonical hub idle can also be
omitted. Together with [frozen padding](group_projective_frozen_idle_padding.md),
this leaves exactly one positive selector hat per actual macro edge.
The full power-of-two lane geometry remains unchanged.

The illustrative ten-letter table now costs **244 certificate / 261
polynomial operations**, with polynomial split **113M+148A**, six
comparisons, **36 positive witnesses** and exact degree **3504**.
This removes three additions and one witness from the264-operation
parent. The new polynomial is an exact specialization of that parent;
equivalence of accepted ordinary inputs additionally uses the complete
path theorem and fresh positive histories. No numerical universal
alphabet is instantiated, and the separate75/88 bounds are unchanged.

## 1. Why the last idle selector is unnecessary

Let n be the sum of the nonempty macro-code lengths, with n>=1. The
parent has live edge hats Ehat_0,...,Ehat_n, where edge0 is the canonical
hub idle and edges1 through n are actual macro edges. All padded idle
hats have already been fixed to one. Specialize further to

    Ehat_0=1, hence E_0=0.                              (1)

Soundness follows by restoring this positive constant in the parent
source: every new positive zero is a parent positive zero at the same
ordinary input. Section2 proves the exact source identity used here.

For completeness, the parent full theorem gives an accepting physical
path from `(1,u,1,u)` to `(0,1,0,1)`, with `u=alpha*x+beta+1`. Delete
all canonical hub idle steps. Each such step has identity physical
action and both endpoints at the hub, so the remaining path is still
a concatenation of whole macros with the same endpoint. It cannot be
empty: the initial first coordinate is one and the required final
first coordinate is zero. Thus its new duration is positive.

Rebuild its histories at that shorter duration. The
[padded-program completeness proof](group_projective_padded_program_margin.md#2-positive-soundness-and-completeness)
explicitly permits any sufficiently large dyadic height D for an
accepted macro word, with no prescribed duration. Choose D greater
than u and one plus every absolute physical state coordinate. Set
the radix B=16D and P=B^T at the new positive duration T. The fixed
program margin remains valid. The genuine history fields, selected
output hats and positive joint-bound slack satisfy all outer bounds.

The new selector fields form a one-hot partition of the same kind of
repunit, with every idle selector zero. Their packed word is a subset
of the full m-lane origin mask. Apply the parent's joined prescribed
AND converse at this actual new scale, then its positive coordinate
maps and unit merges. This gives every remaining positive native
witness and a new complete zero at the original ordinary input.

This normalization can change duration, radix, histories and native
Pell coordinates. It is an equality of existential input predicates,
not a same-tuple map on every parent zero. No finite fixture replaces
the imported positive native extension. For an empty macro table the
implementation retains the parent unchanged; no empty active sum or
constant-scale degree claim is introduced.

## 2. The exact checksum and two paid packing choices

The canonical idle hat has no physical port or state-flow coefficient.
Its only consumers outside the private controller packing are the hub
sum and final checksum. The source audits those consumers explicitly.
Replace the repunit definition by

    J=sum_(e=1)^n Ehat_e-n.                            (2)

This is exactly the parent's definition after (1). It saves one
addition in both possible layouts. If edge0 is the only live hub edge,
delete the last addition of its hat to the other groups. If length-one
macros supply other hub edges, delete the first addition of edge0 to
their sum and start that sum from the next edge hat. In either case
the corresponding subtraction constant changes from n+1 to n. Every
changed private checksum sum decreases by one; the computed J and
all its downstream values stay identical. The earlier partial checksum
shared with sparse flow is untouched.

Write R_j(P)=1+P+...+P^(j-1). The controller word becomes

    Hc=sum_(e=1)^n (Ehat_e-1)P^e
      =P*(sum_(e=1)^n Ehat_e P^(e-1)-R_n(P)).         (3)

These are identities for every integer assignment, including negative
P. No radix or Boolean hypothesis is used in (2)-(3).

The first paid packing plan keeps the parent's entire audited packing
source, replacing the last idle hat by the fixed constant one. It costs
the same as before, and is always an available fallback. The second
uses (3): Horner-pack the n live hats, subtract R_n, and multiply by P.
It reuses the existing dyadic powers and repunits, constructing any
missing R_n by the parent's binary-split identity

    R_(2^j+r)=R_(2^j)+P^(2^j)*R_r.

Every nontrivial product and addition is charged; multiplication by
R_1=1 is only a register copy. With

    A_R(n)=popcount(n)-1,
    M_R(n)=A_R(n)-[n>1 and n odd],

the factored packing costs `n+M_R(n)` multiplications and `n+A_R(n)`
additions/subtractions, including the final multiplication by P.
For n=1 these counts are one multiplication and one subtraction.

Choose the cheaper complete plan, breaking ties by multiplication
count and then a fixed lexical order. If C_old_pack is the actual
parent pack cost and C_new_pack the chosen cost, the total saving is

    delta=1+C_old_pack-C_new_pack>=1.                  (4)

Near a power of two, constructing R_n can be more expensive than the
specialized original pack. Keeping that fallback is essential to the
uniform saving claim. This is a choice between two explicit sources,
not a claim of globally minimal packing arithmetic.

The source audits every removed packing consumer and comparison,
checks each reused power/repunit definition, and topologically sorts
the replacement DAG. The output Hc, computed J, all retained residuals
and complete final polynomial are exactly the parent's values with
Ehat_0=1. Only the deliberately changed private checksum sums differ.

## 3. Complete ledgers and exact degree

The comparison list and finalizer are unchanged, so certificate and
polynomial save the same delta operations and one positive witness.
For the joint variant, use the previous notation C, s, theta and Delta,
where Delta is the padding-only saving. The new counts are

    certificate C+3-s-theta-Delta-delta,
    polynomial  C+23-3chi-s-theta-Delta-delta,
    comparisons 7-chi, positive witnesses n+27-chi.

The same rewrite is audited on four-field, unshifted six-field,
shifted-X and strong-unit parents. Keep all original m-based exponents,
mask powers and fixed-numeral costs when applying these formulas.

For the ten-letter example, n=10 and m=16. The parent packing costs
11M+13A. The factored plan uses the existing R_8 and P^8 to construct
`R_10=R_8+P^8*(P+1)` in1M+1A; its total is11M+11A. Together with
the checksum addition, this saves three additions:

| Mask reuse | Computed P | Certificate / polynomial | Polynomial M / A | Comparisons / witnesses | Degree |
|---|---|---:|---:|---:|---:|
|Yes|Yes|244 / 261|113 / 148|6 / 36|3504|
|No|Yes|245 / 262|114 / 148|6 / 36|2928|
|Yes|No|244 / 264|114 / 150|7 / 37|1774|
|No|No|245 / 265|115 / 150|7 / 37|1486|

All exact parent degrees persist. To see why, specialize the parent
highest forms by setting the leading part of Ehat_0 to zero. The new
`J*=sum_(e=1)^n Ehat_e*` remains a nonzero linear form. The native
highest factors depend on the removed idle only through J*, so they
survive, and computed P still has highest form `16D*J*` of degree two.

The parent's proof that all four outer history highest forms survive
used a free idle variable. Here it is enough that at least one survives.
Let d_i* be the signed physical-port difference for coordinate i. For
computed P the four history highest forms are

    -16(D*)^2*(J*+d_i*), i=0,...,3.

At positive live leading weights, each J*+d_i* is nonnegative. Each
physical edge enters only one of the four d_i*, with sign plus or minus,
so `sum_i(J*+d_i*)>=3J*>0`. Thus their sum of squares is a nonzero
polynomial. For supplied P, a nonempty macro table has at least one
nonzero signed-port polynomial because its edge variables are distinct.
The remaining native and joint-unit highest forms survive as in the
padding-only proof. No equation at a zero is substituted to lower the
literal source degree. The empty-table fallback keeps its old degree.

## 4. Executable evidence

The [source](group_projective_idle_free_paths.py) and
[receipt](group_projective_idle_free_paths.json) record150 option ledgers
and a full default source/finalizer. They compare every retained
register outside the changed checksum fragment, every residual and
the whole output on3,600 assignments, including1,200 signed assignments.
Both packing plans are independently replayed against the direct sum
in (3), even when unchosen. Tables include an empty list, single-edge
macros, several hub edges, longer paths and near-power packing cases.

Four genuine reflected target-word fixtures use all eight single-shear
macros and erase inserted idle positions. They rebuild positive shifted
histories and all selected output hats at the shorter duration, and
check every outer history/flow comparison, the joint-bound unit and
the full joined AND relation for both compiler switches. The native
Pell coordinates in these fixtures are explicit placeholders; their
full positive extension follows from the cited theorem. These are
stronger than arbitrary source identities but are not materialized
complete native zeros.

Normal execution compares the deterministic receipt; `--write`
regenerates it. The previous sources remain unchanged and runnable.

Independent full proof/source review and a fresh default replay passed
without findings. Another240 signed specializations on16 independent
tables compared directly with the earlier shared-flow source after
restoring all idle hats to one. They covered24 fallback and36 factored
configurations, including direct checksum and packed-word identities.
The author's writer and fresh default replay also passed.
