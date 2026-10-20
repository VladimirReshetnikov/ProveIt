# Single crossed equality helpers without a primitive symmetry row

## Result and exact scope

Keep original rho1--rho6 and rho8, full gated membership vacuity, MP, and
generalization of closed theorems. Delete rho7, and replace the canonical
equality-vacuity helper by either of the following families:

1. **Full gated crossed family:**
   `C1(a,b,c) = Eq(a,b) -> All_c Eq(b,a)`, for `c != a,b`.
2. **Asymmetric canonical crossed family:**
   `Cκ(a,b) = Eq(a,b) -> All_κ(a,b) Eq(b,a)`, for `a != b`, where
   `κ(a,b) > max(a,b)` and `κ(a,b) != κ(b,a)` for distinct endpoints.

Both admit the exact baseline membership-defined equality interpretation.
Together with the unchanged K core and the original source gate, they
therefore have the existing K/ZFC ordinary consistency calibration. This
does **not** assert that primitive `Eq(a,b) -> Eq(b,a)` is derivable.
Recovering every primitive equality theorem is unnecessary: the complete
comparison calculus is interpreted using a membership-defined relation.

The distinction matters. Searching only for a proof of primitive symmetry
can miss a smaller complete source theory. The finite certificates below
admit no primitive symmetry, rho7, Eq-vacuity, universal elimination,
arbitrary substitution, or alpha-conversion leaves.

## Unchanged logical prerequisites

Use `F=Rel(0,0)=1`, `not A=(A -> F)`, negative conjunction
`A and B = not(A -> not B)`, and `Ex_i A = not All_i not A` exactly as in
the baseline. The classical propositional bridge uses **rho8 and rho6**:
rho8 gives K/S/Peirce; `Comp_Prop230.v: thm_F` gets explosion from K and
rho6; `thm_DNE` gives double-negation elimination. Thus the TAUT leaves in
the auxiliary certificates do not depend on the deleted equality row or
on a K axiom. No closedness assumption about raw label 0 in F is made.

Closed GEN and rho2 give universal monotonicity; contraposition gives
existential monotonicity. Rho1 gives `Ex_i Eq(i,i)`, which is enough to
derive seriality `All_i A -> Ex_i A` by quantified implication and the
existential consequence of rho2. Applying this to `All_i A` and then using
rho6 gives the uniform theorem

    All_i All_i A -> A.                                      (D)

Full membership vacuity gives fresh-vacuity for membership-only formulas
by the existing structural proof: negation uses existential monotonicity
and rho6, implication uses a classical split, and the quantifier case uses
rho4. Therefore, if i is syntactically fresh in a membership-only A,

    A -> All_i A.

Generalize this closed theorem at i and use rho2, then (D), to obtain

    All_i A -> A.                                           (F)

This restricted fresh-box elimination is available without Eq symmetry
or Eq-vacuity. It is not unrestricted universal specialization.

## Full gated family: reverse membership congruence

Let `e=Eq(a,b)`, `f=Eq(b,a)`, and let t be any third label. Choose
`h=max(a,b,t)+1`. A crossed helper gives `e -> All_h f`. The original
rho3/rho5 row in the reverse endpoint order gives

    f -> (Rel(b,t) -> Rel(a,t)),
    f -> (Rel(t,b) -> Rel(t,a)).

Lift either closed implication at h. For the respective membership
implication A, obtain `e -> All_h A`. The chosen h is fresh in A, so (F)
gives `e -> A`. Hence the system has both reverse congruence laws
conditional on e, for every third label, even without a theorem e->f.

The original forward laws and these reverse laws yield both directions
of quantifier-free membership Leibniz replacement by induction on
propositional constructors. They supply exactly the previous Source116
proofs of quantifier-free specialization and safe auxiliary transport.
General quantified substitution is not an induction clause here.

## The interpreted equality and existence bridge

For a safe z distinct from a,b, define

    Bminus(a,b,z) = (R(z,a)->R(z,b)) and (R(z,b)->R(z,a)),
    Bplus(a,b,z)  = (R(a,z)->R(b,z)) and (R(b,z)->R(a,z)),
    Ez(a,b,z)     = All_z Bminus(a,b,z) and All_z Bplus(a,b,z),
    E(a,b)        = Ez(a,b,EqCode(a,b)).

This is **the same E** as the baseline. At `z=EqCode(a,b)`, the crossed
helper supplies `e -> All_z f`. The forward and newly derived reverse
membership congruences conditional on f imply both `Bminus(a,b,z)` and
`Bplus(a,b,z)`. Lift them at z and combine the results to get

    Eq(a,b) -> E(a,b).                                      (B)

For a=b, E(a,a) is already a theorem obtained by generalizing membership
identity tautologies. No diagonal crossed helper is necessary for this
case. Existential monotonicity and rho1 then give

    Ex_a E(a,b).                                            (X)

The existing membership-only Source116 construction now gives full
E-vacuity, both E-congruences, and the translated rho7 Euclidean law,
including all endpoint and auxiliary collisions. Each old axiom has a
closed translated proof, and the interpretation commutes with MP and
GEN. This is the complete comparison-calculus interpretation.

## Asymmetric canonical family: exact collision handling

With just `Cκ(a,b)`, reverse membership congruence conditional on Eq(a,b)
can initially be derived only when the third label t is different from
`κ(a,b)`. The same proof above works with `h=κ(a,b)`, and (F) applies
precisely under this freshness condition. The certificate explicitly
rejects this forbidden collision; it does not assume unrestricted reverse
congruence for primitive equality.

For the direct bridge (B), choose `k=κ(a,b)` and `l=κ(b,a)`. In the
off-diagonal case, both exceed a,b and l!=k. The consequences of
`f=Eq(b,a)` at third label k therefore use its own helper binder l, which
is fresh in those membership implications. Thus f implies both membership
profile bodies at k. Cκ(a,b) and quantified monotonicity give

    Eq(a,b) -> Ez(a,b,k).                                  (Bκ)

Transporting this to the fixed Eq-code auxiliary gives the same E as
before. The remaining point is to provide that transport without assuming
unrestricted primitive-equality Leibniz replacement.

For quantifier-free membership replacement from x to y, require
`κ(x,y)` to be absent from the labels of the matrix before and after
replacement. The restricted reverse congruence laws then suffice for the
same propositional induction. It is always possible to ensure the
condition by taking one of x,y above every other label in the matrix:
the canonical helper code exceeds both endpoints, hence every such matrix
label.

To transport Ez(a,b,z) to Ez(a,b,w) for arbitrary safe z,w, pass through

    v=max(a,b,z,w)+1.

The replacement pairs (z,v) and (v,w) both meet the explicit helper
freshness test. Quantifier-free specialization and membership-only
fresh-vacuity give each transport step. No alpha rule is assumed.
For E-congruence at a possibly colliding third label c, first transport
to a binder above a,b,c and the fixed internal binder; the specialization
from that binder to c meets the same test. The E-vacuity and E-Euclidean
proofs use the identical fresh-detour discipline.

Thus (Bκ), (X), and the full translated equality laws are established
without a circular appeal to primitive symmetry. The diagonal E bridge
still uses membership identity directly, so diagonal helpers are absent
from the complete certificate.

## Binder examples and source coverage

The following functions meet the off-diagonal conditions:

* `RelCode(a,b)` and `RelCode(b,a)`;
* `a+2b+1` and `2a+b+1`;
* `EqCode(a,b)` and `EqCode(b,a)`;
* `ImpCode(a,b)` and its argument reversal, off the diagonal;
* `CantorPair(a,b)+1` and its argument reversal.

Equality-code choices may be useful because an equality code already
computed for the helper can serve as its binder. Affine choices avoid a
native pairing operation. No particular compiled state saving follows
from these mathematical facts: continuation sharing and stack lifetime
must be measured. The symmetric `a+b+1` helper does not satisfy this
asymmetric proof, although it remains valid for the earlier H and C2
frontends.

The canonical family needs only off-diagonal pairs. Under the original
gate `c != a,b`, its endpoint roles may therefore be any of (a,b), (b,a),
(a,c), (c,a), (b,c), (c,b), with the binder calculated from the selected
endpoints. If c is an endpoint, select the unused parameter distinct from
c to cover each off-diagonal pair. In contrast, the full gated C1 proof
uses arbitrary fresh helper binders and its source coverage must preserve
that freedom; merely changing endpoint roles without rechecking the gate
is not justified.

## The unchanged K adapter

The interpreted equality E is exactly the baseline definition. Hence the
K matrix/code adapter in `k_equality_helper_extension.md` applies without
changing its translation: interpret the named matrix first, pad it by
double negation, and then choose the actual private/native matrix code.
The resulting fresh code passes the original gate. In the modified joint
bundle, the K core and the crossed helper are separately projected using
the retained rho8/rho6 propositional bridge, so this extraction does not
presuppose the equality interpretation it is used to establish.

The other consistency direction uses standard equality: each emitted
helper binder is fresh from both endpoints. Thus the new source theories
have the original K/ZFC ordinary consistency calibration, formalizable in
ZFC using the finite proof constructions. No new machine-table or
proof-assistant endpoint is asserted by this note.

## Reproducible checks

`gated_crossed_helper_certificate.py` checks the full gated variant.
`canonical_crossed_helper_certificate.py` checks each of `rel`,
`reverse_rel`, `affine_a`, `affine_b`. All use only the local stdlib proof
representation in `combined_helper_certificate.py`. Every proof is
exported, reloaded, and checked independently. The exact rule sets reject
T, C2, SYM, rho7, Eq-vacuity, general substitution, and alpha conversion.
The canonical checker also enforces every numerical helper and every
restricted-renaming collision condition. The files `*_receipt.json`
contain the current proof hashes. `research_reproduce.py` rebuilds all
nine exploratory proof modes using the scripts alone and checks those
hashes against embedded retained values.
