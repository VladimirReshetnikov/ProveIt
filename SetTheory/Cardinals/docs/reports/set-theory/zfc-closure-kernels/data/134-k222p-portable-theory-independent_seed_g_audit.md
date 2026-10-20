# Independent audit of the primary seed/G 222-state construction

## Result and scope

The seed/G composition is logically sound as an ordinary mathematical
reduction, subject to the explicitly inherited K230/K224 and seed-native
calibration. The two literal table folds also passed a second independently
written checker, `independent_fold_audit.py`, which imports neither the
constructor nor the earlier fold checker. Its receipt is
`seed222_independent_folds.json`.

This review does not claim a newly compiled Rocq or Lean theorem. It does
not turn finite numerical examples into a universal logical proof. The
uniform mathematical derivation, exact source binding, inductive runtime
certificates, and inherited calibration are distinct premises.

## Why the two source reductions compose

The G replacement is parametric in the set-theoretic core. Write

    G(a,b,c) = E(c,a) -> (E(c,b) -> Q_kappa(a,b) E(a,b)),
    H(a,b) = E(a,b) -> Q_kappa(a,b) E(a,b).

The closed derivations of reflexivity, H, equality-box elimination, and the
literal old Euclidean equality row use G, rho1, rho2, rho6 and the retained
classical propositional bridge. They do not use K, the seed request, IR,
the gate, or any interpreted equality axiom. The converse derivation of G
uses only the literal old equality row and H. Therefore this replacement
is applicable to both the original K bundle and the seed bundle.

The seed packet uses a different conjunction order from the original G
packet. In the exact seed notation, put

    C = Q_c (H_closure -> not W),
    B_old = not (RV -> (H -> C)),
    B_new = not (RV -> C).

Here the seed core is `not C`. The required transformations are precisely
the Boolean tautologies

    B_old -> B_new,
    B_old -> H,
    B_new -> (H -> B_old).

The new source checker uses these exact ordered bundles, rather than
silently identifying them with the original G packet's different literal
codes. For every pair (a,b), selecting gate parameter
`c = max(a,b)+1` supplies an old helper instance. This selection is
independent of the third parameter of G. Conversely, G derives H for
every pair, recovering every old gated seed bundle. Induction replacing
axiom leaves thus gives equality of all native theorem sets between the
old seed calculus and the new seed/G calculus.

The independent G row must remain ungated. Its source position is the
original seventh logical slot; only the K bundle retains the old gate.
The complete primitive-word and control-flow checks verify this distinction.

## No circular equality argument

For each x let z=kappa(x,x), e=E(x,x), and d=E(z,x). G(x,x,z) gives
`d -> Q_z e` by contraction. Existential monotonicity and rho1(z,x) give
`exists_z Q_z e`; rho6 gives e. Thus reflexivity precedes, and does not
use, the deleted helper.

Now G(a,b,a) and reflexivity give H(a,b). Retained seriality and rho6
give `Q_i Q_i A -> A` for arbitrary A. Quantifier monotonicity applied to
the closed H theorem gives `Q_i e -> Q_i Q_i e`, with
i=kappa(a,b), so `Q_i e -> e`. Composing with G recovers the literal old
equality row. The argument does not assume uniform single-quantifier
elimination. Generalization is applied only to closed derivations.

The TAUT bridge remains an inherited dependency: rho8 yields the
implicational classical basis, and rho6 supplies explosion from native
F=1. Treating the distinguished numerical code 1 as logical falsehood in
these proof templates is justified through that bridge, not by assuming
that the raw atom R(0,0) is syntactically closed.

## Seed-code edge cases are unchanged

The new source preserves the seed core, the identity `matrix code = private
label = c`, and the gate `c != a,b`. Consequently the existing seed-native
audit remains necessary and applicable:

* D(0) is a closed tautology; the private-label claim is free freshness,
  not absence of all bound occurrences of label zero.
* D(1)=R(0,0) has no occurrence of private label 1.
* At a=b, the distinct-role abstraction lemma is unavailable. The seed
  audit instead splits on existence of a matrix witness and uses the
  exact shadowing behavior of the repeated bound name. An empty container
  works in the no-witness case; a singleton witness container works in
  the other case.
* In the lower consistency translation, membership-defined equality is
  translated first. The padded matrix code and fresh private binder are
  then chosen, so fresh auxiliaries introduced by the translation are
  included in the freshness argument.

No new instance of any of these edge cases is introduced by G absorption,
because the proof first reconstructs the exact old seed theorem set.

## Literal machine folds

The independent audit uses parent K-table SHA-256
`e287d8685bcd75a93d8f01e24b9217381f487a7a970183c8fc2dbec439cc01f8`
and final K-table SHA-256
`34af110829938ba4e88574e86f43515d725612305321f7b56391aea604a1d1db`.

The first fold identifies K185 with K118. Its only nonempty entry facts
are: K118 scans zero, and the cell one step right of K159 is zero. These
facts are initiated at start K0 on every binary tape and preserved by
every literal parent transition. The impossible K118/read1 branch is
excluded by this proved invariant, rather than by a finite execution log.

The second fold identifies K174 with K159 and needs no nontrivial entry
facts. In both folds every changed old branch is implemented by a
strictly positive finite block that restores the complete tape and
reaches the mapped one-step endpoint. Unspecified tape cells are never
read by the proof trace; they are arbitrary. Every other transition is
checked literally under the state map. The resulting machine has exactly
222 reachable working states and 444 rows.

This proves halting equivalence with the 224-state parent for every
initial tape from their common initial state. The independent source
runtime proof and exact blank initialization identify the parent/final
machines with the intended proof search. A long nonhalting sample would
not supply this identification.

## Overall proof boundary

The conclusion follows by composition:

    binary machine halts
      iff the exact seed/G numerical calculus derives 1
      iff the original seed numerical calculus derives 1
      iff ZFC is inconsistent.

All new proof manipulations are effective transformations of finite
derivations, finite exact table simulations, or inductions over arbitrary
natural register values and finite spare lists. The result is an ordinary
mathematical proof formalizable in ZFC, with the inherited calibration
recorded explicitly. No proof of Con(ZFC), unconditioned nonhalting, a
state-count lower bound, or a newly completed proof-assistant endpoint is
established or needed.
