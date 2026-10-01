# Native unit products give prescribed AND83 and complete history components

The [computed-field AND90](native_binary_computed_fields.md) has an
**83=43M+40A** polynomial successor, with **15 positive witnesses**, five
comparisons and69 certificate operations. Its total degree is **at most124**.
An ordinary-strong alternative costs **84=42M+42A**, with six comparisons,
67 certificate operations and degree at most86. Both retain the complete
prescribed AND relation, including its positive native extension.

The same generic helper gives **216=94M+122A** for packed Wang motion
and **130=60M+70A** for packed toggles, with28 and21 witnesses respectively.
These remain complete local history components. Their missing instruction
control, ordinary-input coding or planar ant motion are not supplied.
There is no new universal operation bound or change to the75/87 route.

The [source](native_binary_norm_units.py) and
[receipt](native_binary_norm_units.json) preserve every parent artifact.
The ordinary-strong version gives a full positive-zero bijection through
a first-root coordinate change. Strong normalization instead preserves
the projection onto all coordinates except five native auxiliaries;
completeness rebuilds those auxiliaries. These two claims are deliberately
distinct. Neither version asserts identity with the old SOS polynomial
on unchanged off-zero assignments.

## 1. The actual native equations and three safe signs

Start from a guarded compatible packet after any paid computed-field
substitutions. The emitted examples use the parent's four-field or
six-field options, with or without its positive-scale change. Its
complete parent embedding and pretyping q,F3 positivity remain required;
a mere naming convention is not an arithmetic-domain proof.

Write X,Y for the paid positive scales, E=XY, V=XY^2, and

    Delta=a^2+4a+3=(a+2)^2-1,
    T=i*c^2, J=2r+1, U=j*c-J.

The letters a,c,k,r may be supplied or computed according to the chosen
parent. Their positivity is proved before equations by the computed-field
packet. In particular X,Y,k>0 even before any native interpretation.
Three original comparisons are

    d^2=Delta*c^2+1,
    T^2*(U^2-y^2)=1-y^2,
    T^2=Delta*(f^2-1).                              (1)

Let K=Delta*(f^2-1), whose gate is already paid. Reuse the two old
right-side gates to define

    N1=d^2-Delta*c^2,
    N3=K*(U^2-y^2)+y^2.                             (2)

The strong comparison T^2=K is still an ordinary comparison in this
version. It restores the old auxiliary coefficient at every zero.
Away from that comparison N3 is a changed polynomial, with exact
correction

    N3 = 1 + old_auxiliary_residual
             - old_strong_residual*(U^2-y^2).       (3)

The signs in(2) are safe on arbitrary integer assignments, without any
native equations. Delta is0 or3 modulo4. Therefore N1 is a square or
sum of two squares modulo4 and cannot be-1. Since f^2-1 is0 or3 modulo4,
K is0 or1 modulo4. Hence N3 is congruent to y^2 or U^2, and cannot be-1.
This explicitly checks the actual K coefficient; it does not silently
apply a sign lemma for the different T^2 coefficient.

The original checksum register sum(F_i)+1 is private to its comparison
with q. Reuse that gate to define the fourth field factor

    Qc=q-sum(F_i).

No off-zero sign restriction is claimed for Qc. Its old comparison is
exactly Qc=1.

## 2. A positive first-root gap at unchanged gate cost

The first native equation is

    (E^2+X)*(kY)^2=tau*(tau+1),
    equivalently V*(V+1)*k^2=tau*(tau+1).            (4)

Replace positive tau by positive g and define

    N0=g^2+4Vk*(g-k).                               (5)

The six deleted private gates for(4) cost4M+2A. Their replacements are

    g_square=g*g,
    root_base=E*(kY),
    signed_gap=g-k,
    gap_cross=root_base*signed_gap,
    four_cross=4*gap_cross,
    N0=g_square+four_cross.

These also cost4M+2A, including multiplication by the fixed numeral4.
Here root_base=Vk by literal polynomial identity. No gate computing
V or a division is being supplied for free.

The coordinate maps at positive zeros are

    g=2tau+1-2Vk,
    tau=Vk+(g-1)/2.                                (6)

For an old zero, (2tau+1)^2=1+4V(V+1)k^2>(2Vk)^2. Its positive root
therefore makes g>0. Conversely N0=1 implies g odd, since N0 is g^2
modulo4; then positive V,k,g make tau in(6) a positive integer solving(4).
The maps are inverse. Off zeros, the second formula may be half-integral;
the checker explicitly includes even positive gaps to preserve this
scope distinction. It uses exact rational arithmetic for those identities.

N0 cannot be-1 modulo4. Form

    W=N1*N3*N0*Qc.                                  (7)

If W=1 over the integers, all four factors are units. The three independent
sign exclusions force N1=N3=N0=1, and then Qc=1. With the retained strong
comparison, all old comparisons are restored through(6). Conversely any
old positive zero gives these four factors1 and all retained comparisons0.
Thus this version is a bijection of complete positive zero sets, including
all outer parameters and history coordinates, with tau renamed to g.
The product in(7) costs exactly three additional multiplications.

The source reconstructs the compatible computed-field parent before
rewriting, audits every deleted/repurposed register's source and comparison
consumers, and rejects declared external exports. These guards recursively
inspect register leaves inside dictionaries, lists and tuples, including
interfaces containing optional None entries. It preserves the ratio
slacks and all outer comparisons. A topological sort adds no copy gates.

## 3. Optional strong normalization and its precise converse

A further one-operation polynomial saving uses the
[normalized-strong construction](pcp_normalized_strong_history_units.md),
but checks its premises against this actual source. Keep the positive
supplied spelling i with a new meaning, and put

    t=i*c^2, Q=Delta*t^2, Kstar=Delta*Q,
    Ns=f^2-Q,
    N3star=Kstar*(U^2-y^2)+y^2.

The new product is Wstar=N1*N3star*N0*Qc*Ns. The separate strong
comparison is removed. The old f^2-1 register becomes Ns and the old
K register becomes Kstar. Only Q and the extended product require new
gates: two multiplications. Removing one comparison saves3 finalizer
gates, for a net saving1=2A-1M.

For arbitrary integers, Ns=f^2-Delta*t^2 cannot be-1 modulo4. At a
new zero the integer product Wstar=1 therefore gives Ns=1. Set

    i_old=Delta*i>0.                                (8)

Delta>0 follows from a>0 before any equation. Then the old strong
comparison becomes

    (i_old*c^2)^2=Delta*(f^2-1)=Kstar.

The old N3 equals N3star, and all other factors/residuals agree. This is
a positive embedding into the ordinary-strong unit parent, whose full
soundness has just been proved. In particular no rank or bit conclusion
is used to obtain Ns=1. Off zeros, the exact correction is

    old_strong_residual=Delta*(1-Ns),
    N3star-N3_old=old_strong_residual*(U^2-y^2).       (9)

For completeness, start from any positive ordinary-strong parent zero.
Its full native theorem gives A=a+2, c=psi_A(J), with r odd and
J=2r+1 congruent3 modulo4. Keep all coordinates except f,i,j,o,y.
The source audits that q,a,c,r,root_base, every other norm factor,
all other comparisons and all public outer interfaces are independent
of those five auxiliaries. Thus their reconstruction cannot disturb
an outer bound, motion equation, input port or first-root gap.

Let C=chi_A(J), Delta=A^2-1 and choose

    m=2cJ, f=chi_A(m), i=psi_A(m)/c^2,
    T=Delta*psi_A(m),
    y=psi_T(J), U=chi_T(J)/T,
    j=(U+J)/c, o=(U+c)/f.                            (10)

These are positive integers. For i, expand
(C+c*sqrt(Delta))^(2c): the first odd term contains2c^2 and each later
odd term contains at least c^3, proving c^2 divides psi_A(m).
For U, odd J makes chi_T(J) divisible by T. Its quotient is an integer
polynomial L_J(T^2) with constant term (-1)^((J-1)/2)*J=-J. Since c
divides T, this gives U=-J modulo c and proves j integral.

For o, T^2=Delta*(f^2-1) gives T^2=1-A^2 modulo f. The polynomial identity

    L_J(1-A^2)=(-1)^((J-1)/2)*psi_A(J)=-c

proves U=-c modulo f. One may verify this identity for all odd J from
the initial cases J=1,3 and the skipped recurrence: L_(J+2)(z)
=(4z-2)L_J(z)-L_(J-2)(z), while the signed odd subsequence of psi_A
has coefficient2-4A^2 after z=1-A^2. Positivity of j and o follows
from their positive numerators and denominators.

The Pell identities now give Ns=1 and
T^2*(U^2-y^2)+y^2=1, while U=jc-J=of-c. All other values remain
unchanged. This constructs a complete positive new extension with the
same outer coordinates. Normalization is therefore a projection
equivalence after five fresh auxiliaries, not a bijection on all supplied
positive tuples and not a weakened divisibility or rank hypothesis.

## 4. Two complete finalizers and actual costs

Let R1,...,Rh be the retained ordinary residuals and let W denote the
chosen product. Both

    (W-1)^2+sum Rj^2,
    W*(1+sum Rj^2)-1                                (11)

have exactly the same integer zeros: W=1 and all Rj=0. For the unsquared
form this follows because its second factor is an integer at least1.
No off-zero sign of W is assumed. Both finalizers cost eM+(2e-1)A for
e=h+1 comparisons. Every subtraction, square and multiplication is paid.

If C,e,w are the computed-field parent's certificate, comparison and
witness counts, ordinary units give C+3,e-3,w and polynomial cost
C+3+3(e-3)-1, saving6 operations. Strong normalization then gives
C+5,e-4,w, saving7 operations in all. The root coordinate is renamed,
not omitted. The following actual ledgers use the prior positive-scale
change; the receipt also retains its absence.

| Context | Fields | Strong | Certificate | Eq | Witnesses | Polynomial | Product degree bound | SOS degree bound |
|---|---|---|---:|---:|---:|---|---:|---:|
|AND|Four|Ordinary|67|8|17|90=44M+46A|53|66|
|AND|Four|Normalized|69|7|17|89=45M+44A|69|118|
|AND|Six|Ordinary|67|6|15|84=42M+42A|86|108|
|AND|Six|Normalized|69|5|15|**83=43M+40A**|124|216|
|Motion|Four|Ordinary|191|11|30|223=95M+128A|533|642|
|Motion|Four|Normalized|193|10|30|222=96M+126A|731|1078|
|Motion|Six|Ordinary|191|9|28|217=93M+124A|1602|2020|
|Motion|Six|Normalized|193|8|28|**216=94M+122A**|2112|3632|
|Toggle|Four|Ordinary|108|10|23|137=61M+76A|213|258|
|Toggle|Four|Normalized|110|9|23|136=62M+74A|287|438|
|Toggle|Six|Ordinary|108|8|21|131=59M+72A|584|736|
|Toggle|Six|Normalized|110|7|21|**130=60M+70A**|778|1340|

All degree claims are conservative upper bounds on the actual source,
including every relation parameter and witness. Propagation uses no
zero-set equation. When d is computed, a guarded ordinary polynomial
identity cancels the a^2*c^2 term in
(X+ac+ga*(4a+3))^2-(a^2+4a+3)c^2; the source checks all defining rows
before using this improvement. Factor bounds add in the product;
residual squares contribute twice the largest residual bound. Standalone
affine polynomial slices provide separate lower-bound checks, without
promoting an inexact upper envelope to an exact degree claim.

## 5. API, replay and retained limits

`rewrite(old,prefix=None,normalized=False)` accepts a compatible
computed-field packet and preserves its outer source. `normalize(packet)`
is the optional second step. `build(context='and',scaled=True,
computed='six',normalized=True)` emits the83 default; contexts `motion`
and `toggle` apply the same helper. `polynomial_source` selects the
unsquared product by default, with `sum_of_squares=True` for the other
finalizer. Degree metadata is calculated freshly rather than importing
an unrelated history exponent formula.

The receipt contains24 actual context/scale/field/strong schedules and
1,536 complete factor, residual and both-finalizer identities,768 signed.
The ordinary checks include192 positive even-gap inputs whose restored
old roots are explicitly half-integral off zeros. There are4,096 residue
sign checks, eight exact fresh five-auxiliary constructions,128 exact
positive first-root bijections and eight standalone affine degree slices.
A nested-interface fixture is accepted, while four nested private or
rebuilt-auxiliary exports are rejected by the source guards.
The canonical fixtures use small native parameters; they are not full
AND or history zeros. Complete positive extension is proved above.

Independent root review covered the full proof and source, followed by a
fresh default replay. A separate direct-formula executor checked384
complete factor/residual identities and both finalizers,192 signed,
across all six context/normalization combinations, with48 complete
output dependency closures. The final recursive interface guards were
also reviewed and the receipt replayed after their addition. No
mathematical or source findings remain.

The motion relation still lacks instruction control and an ordinary-TM
input map. Its existential endpoint projection remains monotone tape
extension with positive dyadic heads. The toggle relation still admits
every nonnegative endpoint pair and lacks planar turning/motion, periodic
input hardware and acceptance. These unchanged scope limits prevent
interpreting the local216 or130 counts as complete universal bounds.

```sh
python3 native_binary_norm_units.py
```
