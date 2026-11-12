# Independent audit of guarded root-deterministic introduction

## Verdict and scope

The guarded-core argument is mathematically viable after the proposed
case-fragment-first repair. The dependency order below does not use
predecessor, equality reflection, or full equation induction prematurely.
Both formula composites can be proved for the **guarded canonical formula
language**.

The verdict does not extend to the entire unrestricted administrative
language of the short checker. Its mixed ordinary reading proves soundness
of arbitrary certificate steps, but does not give a full formula round trip
for unguarded atomic D formulas. The canonical-input/goal contract must be
explicit, and should not be called a theorem about the whole administrative
calculus.

Use the inherited native formula language `A ::= equation | D A` for this
claim, with Q as reusable clauses or administrative closures. An arbitrary
unguarded atomic Q as an additional canonical formula constructor would
require another introduction/round-trip argument not supplied here.

## Conventions

Write `C(n,a,b)=I(n,a;u.b)`. For an equation `E(y)` with sides `s(y),t(y)`,
put

    G_y E := C(y,0,s(y)) = C(y,0,t(y)).

The two computation equations prove `G_0 E` without assumptions, and
`G_(Sz) E` is interderivable with `E(Sz)` by equality transport.

Canonical atomic D matrices have this literal guarded shape with the
closure-bound variable as control. Compound D matrices are unrestricted,
subject recursively to the canonical condition. Atomic introductions use
progress only; compound introductions use cases only.

For a fixed equation E independent of fresh u,v, let

    L(E) := D_(u,v) G_v E.

## 1. Padding is available before any case principle

`E |- L(E)` follows by atomic progress introduction: its successor goal is
equivalent to E, already retained, so its local induction assumption is
ignored. Conversely DE opens the clause for `G_v E`; its zero antecedent is
a computation theorem; Use at 1 yields E. Thus `E -||- L(E)` is obtained
without any numerical cases or equation induction.

Define `Pad(E)=L(E)` at an equation and `Pad(A)=A` at a compound formula.
Every Pad image is compound and is uniformly interderivable with its input.

## 2. Embed the entire old case-only fragment C0

Let C0 be the old native calculus with all case introductions and with no
progress introduction. Define recursively

    T(E)=E,
    T(D B)=D Pad(T(B)).

T commutes with capture-free numerical substitution, up to the agreed
renaming of its fresh dummy binders. All D bodies introduced by this
translation are compound, except the guarded inner D used by L.

Computation and transport translate directly. For a case introduction,
unwrap its new Pad base, use the translated old premise, and wrap the
resulting successor formula before applying compound case introduction.

For DE, the actual opened clause has the Pad versions of its antecedent and
instances. It simulates the desired unpadded translated old clause by
wrapping its input, applying Use, and unwrapping its output. This is an
ordinary derivation transformation for uses of a retained clause; it does
not need an implication connective or an already-proved Q congruence rule.

This embeds every C0 derivation. The inherited C0 reconstruction of
intuitionistic logical rules, coverage, and explosion therefore transfers.
The inherited source explicitly proves that these constructions need only
case introduction, not progress induction.

## 3. Canonical A is interderivable with T(A), already at this stage

Proceed by external induction on A. Equations are unchanged.

For a compound D matrix B, the induction equivalence for B lifts through D
using compound case introduction: open the old D clause, convert the new
base to the old one, specialize the old clause at a successor, and convert
back. Both introduction matrices have compound roots.

For an atomic guarded matrix B=G_y E, T(D B)=D L(B). The two directions are
explicit:

* `D B |- D L(B)`: open the B clause, introduce the compound matrix L(B),
  unwrap its local zero assumption, use the B clause at the successor, and
  wrap the result.
* `D L(B) |- D B`: open the L(B) clause at its fresh witness. B(0) is a
  computation theorem, so L(B(0)) follows by padding. The opened clause
  supplies L(B(Sz)), and unpadding supplies B(Sz) with no local progress
  assumption needed. Apply atomic progress introduction with that witness,
  ignoring B(z), and close DE.

The second direction is exactly where the canonical zero-true guard is
used. It is false in general for unguarded matrices.

Consequently the translated logical macros can take arbitrary canonical
operands: replace an operand by T(operand) using this equivalence when
needed. No induction-strength circularity occurs.

## 4. Recover contextual equation induction

Assume `Gamma |- E(0)` and `Gamma,E(z) |- E(Sz)` with the usual fresh z.
Construct a progress step for `B(y)=G_y E(y)`.

Under `Gamma,B(z)`, use the already transferred coverage of z. In its zero
case, the original step at 0 and the supplied base prove E(1). In its
successor case z=Sk, B(z) unwraps to E(Sk), and the original step specialized
at Sk gives E(S(Sk)). Equality transport yields B(Sz) in both cases.

This use of cases is now legitimate despite the retained assumption B(z):
coverage/disjunction elimination retains the context and adds an equality
case. It is not an invalid application of the raw fresh-variable NC rule.

Atomic progress introduction gives `D_(u,y) B(y)` with dummy u. DE, the
theorem B(0), and Use at Sn give E(Sn). Combine these successor instances
with the supplied E(0) by numerical cases to obtain E(t). Thus full
contextual literal-equation induction is recovered before invoking the
inherited arithmetic bootstrap.

## 5. Both guarded formula composites

Interpret canonical D ordinarily as `exists x (B(x,0) -> forall y B(x,y))`.
Interpret ordinary logic back using the T-translations of the inherited
logical macros.

For the ordinary-to-native-to-ordinary composite, T preserves the ordinary
meaning by structural induction, since Pad(E) is ordinarily equivalent to
E. The inherited macro semantics therefore give the ordinary formula
round trip.

For the native-to-ordinary-to-native composite, take the old C0 paired
composite theorem and translate its derivation by T. This gives a native
equivalence beginning with T(A). Compose with the canonical A<->T(A)
equivalence from section 3. This proves the native formula round trip.

The inherited scalar/iPRA arithmetic bridge now applies, including both
function composites by recursion uniqueness. Numerical domains are whole,
equality is actual, and the numerical isomorphism remains the identity
graph x=y. No new retraction, quotient, or standard-model-only assertion is
introduced.

## 6. Administrative soundness and its strict limitation

For an unrestricted administrative D with literal equation matrix E, read
it instead as

    H(E) := exists x forall y (E(x,y) -> E(x,Sy)).

Read compound D by the ordinary conditional-universal meaning, and read Q
ordinarily. Atomic progress introduction is directly sound for H. Atomic
DE is sound because equation induction converts H(E) to exists x Q_y E.
Compound case introduction is sound by coverage. Transport respects this
reading because numerical substitution preserves each formula's root.

When E is canonically guarded, its zero instance is a theorem. Equation
induction and elementary logic then prove H(E) equivalent to exists x Q E,
so this administrative soundness theorem yields the intended ordinary
soundness for canonical final sequents.

It does not yield a full administrative round trip. Let E(y) be y=1 with
dummy witness x. The old ordinary D E is true in standard natural numbers,
because E(0) is false. H(E) is false, because E(1) holds and E(2) fails.
The deterministic calculus is still sound under the old ordinary reading
as well (each of its rules is an old rule). Therefore it cannot derive,
from an assumed unguarded D E, a canonical encoding of H(E). This supplies
a concrete obstruction to claiming that the whole administrative language
is definitionally equivalent to the H reading.

## Required reporting qualifications

1. State the canonical grammar/encoding contract next to the checker-size
   claim. Distinguish the kernel's arbitrary administrative certificates
   from its guarded user-facing final propositions.
2. Do not claim a full round trip for arbitrary raw Q/D syntax.
3. The proof above is a written derivation audit, not a new Lean/Rocq
   verification. The existing Lean development verifies the inherited
   baseline, not these new transformations automatically.
4. Cite the inherited ordinary bridge and scalar arithmetic proofs as
   inherited, while attributing the root-deterministic guarded restriction,
   C0 embedding, and canonical composite argument to the new construction.
