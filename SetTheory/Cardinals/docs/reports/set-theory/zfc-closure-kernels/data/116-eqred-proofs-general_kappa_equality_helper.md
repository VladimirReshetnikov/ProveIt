# General constructor-binder equality helper

## Exact theorem and supported source variants

Let kappa be a function from pairs of natural-number labels to labels. Assume
only

    a != b  implies  kappa(a,b) != a and kappa(a,b) != b.       (K)

No restriction at all is imposed on kappa(a,a). Replace the original full
gated primitive equality-vacuity family by

    Eq(a,b) -> All(kappa(a,b), Eq(a,b)).                       (Hk)

Keep original rho8, rho1--rho6, full membership vacuity, and exact native
CP/GIC. Either retain original rho7 or replace it by primitive symmetry
Eq(a,b) -> Eq(b,a). Both resulting ordinary proof theories have the external
consistency calibration with ZFC proved in
`membership_defined_equality_calibration.md`.

This is an ordinary logical-theory theorem. An effective source implementation
also needs the chosen kappa builder, exact row coverage and bundle extraction;
the theorem does not itself verify a changed enumerator or runtime compiler.
No general V, replacement K/S rows, own-formula-code equation, or relation
between kappa and a GIC matrix/output code is required. K/S here are derived
propositional rules from the retained classical basis, as in the parent proof.

If the helper is stored inside the old gate c!=a,b, choose any c distinct
from a,b to obtain each (Hk). It is not necessary to choose c=kappa(a,b);
that choice must specifically be avoided at a diagonal collision.

## 1. Old rho7 bootstraps symmetry even with a colliding diagonal binder

Fix x and put z=kappa(x,x), d=Eq(z,x), e=Eq(x,x). Original rho7 gives

    d -> (d -> e), hence d -> e.

Closed existential monotonicity, which uses only K/S, rho2 and closed GEN,
together with rho1(z,x), gives Ex_z e. The helper (Hk) at (x,x) gives
`e -> All_z e`; a second existential monotonicity gives
`Ex_z All_z e`. Finally rho6(z,e) gives e.

Every displayed formula is valid syntax for z=x. No fresh-variable step,
universal elimination, alpha-conversion, primitive Eq-vacuity or general V
occurs. In particular, when x=z=0, rho1 is exactly Ex_0 Eq(0,0), and rho6
is exactly `(Ex_0 All_0 Eq(0,0)) -> Eq(0,0)`.

With Eq(x,x) now a theorem, rho7 instantiated as

    Eq(x,y) -> (Eq(x,x) -> Eq(y,x))

gives primitive symmetry. The primitive-Sym source variant can omit this
whole bootstrap; its E interpretation does not need primitive reflexivity.

## 2. Fixed defined equality and its bridge

Keep the definition of interpreted equality unchanged:

    E(a,b) = E_ab^weq(a,b),

where E_ab^z is the conjunction of the two universally quantified
bidirectional membership-indiscernibility conditions. The fixed auxiliary
weq(a,b) is always distinct from a,b.

If a!=b, condition (K) makes z=kappa(a,b) a safe auxiliary. The existing
finite Eq-to-E proof uses only the helper at this chosen z, symmetry,
rho3/rho5 and closed GEN/rho2. It therefore proves

    Eq(a,b) -> E_ab^z.

The already proved, membership-only safe-auxiliary transport proves
`E_ab^z -> E_ab^weq(a,b)`. Compose them to obtain Eq(a,b)->E(a,b).
There is no demand that kappa(a,b)=kappa(b,a), nor that either be an equality
code, nor that the separately defined auxiliary commute with substitution.

If a=b, both matrices defining E(a,a) consist of implications of each
membership atom to itself. Their bidirectional negative conjunctions are
propositional theorems; closed GEN at weq(a,a), followed by conjunction
introduction, gives E(a,a). K then gives Eq(a,a)->E(a,a). This argument uses
no helper and no primitive equality fact. Thus it works when kappa(a,a)=a,
including the exact wim(0,0)=0 case.

For EVERY pair, including a=b=0, existential monotonicity at label a now
transforms Eq(a,b)->E(a,b) into

    Ex_a Eq(a,b) -> Ex_a E(a,b).

Apply rho1(a,b). This establishes the interpreted equality-existence row
without any existential introduction, general substitution, or hidden
freshness premise. All remaining E laws and the complete comparison-theory
interpretation are exactly those already proved in the parent note.

## 3. Reverse consistency direction

The full original calculus proves (Hk):

* For a!=b, condition (K) makes it an old Eq-vacuity instance.
* For a=b and kappa(a,a)!=a, it is also an old Eq-vacuity instance.
* For a=b and kappa(a,a)=a, old equality reflexivity gives Eq(a,a), closed
  GEN gives All_a Eq(a,a), and K gives the helper.

Equivalently, every diagonal helper is true in standard equality semantics,
regardless of the chosen binder. The primitive-Sym replacement is an old
logical theorem. Thus the reverse source-theory comparison is unaffected.

## 4. All proposed constructor builders qualify

Write P(a,b)=(a+b)(a+b+1)/2+b. The native builders are

    wim(a,b)=4P(a,b)
    wrel(a,b)=wel(a,b)=4P(a,b)+1
    wall(a,b)=wal(a,b)=4P(a,b)+2
    weq(a,b)=4P(a,b)+3.

P(a,b)>=a,b, and P(a,b)=0 only at (a,b)=(0,0). Every positive-tag builder
therefore strictly exceeds both arguments. The implication builder also
strictly exceeds both whenever (a,b)!=(0,0), because then 4P>P>=a,b.
Swapping the arguments preserves these conclusions.

Consequently all seven proposed alternatives are admitted:

    wrel(a,b), wrel(b,a), wall(a,b), wall(b,a), weq(b,a),
    wim(a,b), wim(b,a).

The existing weq(a,b) helper is the control case. Both implication builders
have the sole collision kappa(0,0)=0, explicitly covered above. No candidate
is excluded.

## 5. Scope and regression evidence

`check_general_kappa.py` independently checks each generated proof node
against its K/S, rho1/2/3/5/6/7, symmetry, MP, closed-GEN or exact (Hk) row.
It covers every proposed builder, zero and large diagonal labels, primitive
reflexivity/symmetry/transitivity, direct off-diagonal Eq-to-E^kappa bridges,
and fixed-safe-auxiliary diagonal E/ExE. The collision is tested literally;
no numeric freshness assertion is silently inserted at (0,0).

These finite checks supplement the uniform proof above. They do not certify
source byte edits, generic/specialized state counts, or machine behavior.
