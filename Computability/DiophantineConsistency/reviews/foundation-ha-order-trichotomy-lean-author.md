# Actual HA trichotomy — author receipt

Author: `circuit_reduction`; author validation, not independent review. The
entire new main, checks, build and freeze drivers were read before execution.
Only new owned files and private links were written. No frozen source,
shared object, vendor file, umbrella or Git state was changed.

| Source under `Lean/DiophantineConsistency/` | Lines | SHA256 |
|---|---:|---|
| `FoundationHAOrderTrichotomy.lean` | 171 | `bdfaf5139b109776e696b0269f9a68cabfa7461cd416600373ec3fcea690a6f3` |
| `FoundationHAOrderTrichotomyChecks.lean` | 101 | `e8a8713acd4a1968e6bdb8ebd5599173542839c8e5077b4a1bd24ebe6f5b814b` |

Both final fresh builds passed with `-M6000 -j1 -DElab.async=false` and a
512 MiB reserve. The final main log is empty. All 25 final axiom reports
use at most `propext` and `Quot.sound`: no choice, custom axiom or `sorryAx`.
The private overlay is `/tmp/foundation-ha-order-trichotomy-8ir912og/lib`.
Fresh main object:
`e1b450d49c21ffda5711e1407878324f5be51574dcd9ccbac778c7633db47555`.
Fresh checks object:
`6c025b2ba1fb8216960f30d5050538f99d795362e818f5bd47ab072d40e6f54c`.
Dependency replay manifest SHA256:
`7718cbdf3cfbe3510cac94f15f519c016dafcab39292152abb12e5210b36dfd1`.
Freeze snapshot: `312077c9f601490c105f4f055a6822e7f5f8bda3`.

The exact final source endpoint is
`FoundationHAOrderTrichotomy.ltTri : HA.Proves
(sentence PeanoMinus.Axiom.ltTriᴺ)`.
Its literal body is checked by `rfl`, with the actual source's right-associated
disjunction, quantified variables in slots 1 and 0, and two final universal
closures. The inner negative disjunction encoding is retained as-is; adding
an extra double negation changes the formula, as a structural negative
control verifies. No Foundation implication conversion is required here.

The ordinary theorem `trichotomy s t` proves
`ltFormula s t ∨ (s = t ∨ ltFormula t s)` inside HA for arbitrary terms,
including overlapping free parameters. It is obtained by actual formula
induction on `body = ∀ y, tri x y`. The base uses the already proved
constructive `zero_le`. In the successor case, an actual zero/successor
decomposition of `y` is eliminated. The zero branch has the explicit strict
order witness `x`. In the successor branch the induction hypothesis is
shifted twice through the universal and existential binders, instantiated
at the new predecessor, and transported across the supplied successor
equality. Successor preservation of strict order uses exactly the original
predecessor witness and the actual HA `succ_add` equation; equality uses
successor congruence. The complete finite axiom and assumption contexts are
retained in both binder eliminations. This is not a proof by induction in a
standard natural-number model.

The finite logical helper `encoded_three` then maps the proved three-way
disjunction into its literal nested negative encoding. Its type permits any
relative axiom predicate and context. It uses implication introduction,
disjunction elimination, conjunction elimination and double-negation
introduction, plus the accepted two-way encoded-disjunction helper. It is
not a replacement negative-translation algorithm, and it uses no DNE,
semantic totality or classical proof-to-HA oracle.

Focused checks cover the zero/successor induction substitutions, the twice
shifted induction hypothesis and its actual predecessor instantiation,
the unchanged strict-order witness, nonlinear free-term instances, equality
transport under an extra open context, zero/successor/equality branches,
arbitrary relative axioms, and a disjunction of nested quantified formulas.
All public proof helpers and the final source endpoint have axiom reports.

Two rejected main drafts are retained, with their complete source copies,
logs and invocations. Both failures concerned only elaborating `succ_zero`:
first the capture-safe witness substitution needed normalization; then the
`Proves` wrapper needed explicit unfolding. The third main run and first
checks run passed without diagnostics. The replay bundle under
`reviews/foundation-ha-order-trichotomy-author-replay/` records all four
invocations and both read drivers; rejected runs are not represented as
successful validations.

The private cache reuses the same 96 authenticated prerequisites as the
separate multiplication and irreflexivity leaves, including 76 Foundation
modules, through the frozen Witnesses parent. It imports neither new leaf.
All selected source, object and trace hashes, inherited pins, parent
manifest, compiler and package identities were rechecked before/after
execution and at freeze. No new Foundation dependency or prerequisite
build was needed. Only the present two leaves were freshly compiled;
no full dependency-closure replay is claimed.

This completes the separately authored remaining named order-axiom images.
Their composition with the full arithmetic/induction theory, and the final
HA proof of the current equation/consistency equivalence, remain separate
theorems. This receipt does not claim either endpoint.
