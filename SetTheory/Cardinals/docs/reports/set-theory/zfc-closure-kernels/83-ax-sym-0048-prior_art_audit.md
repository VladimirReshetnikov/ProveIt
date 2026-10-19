# Independent logical/prior-art audit

## Primary sources read

- <https://wiki.bbchallenge.org/wiki/Logical_independence>, retrieved
  18 October 2026. The history table lists the 254-state result dated
  13 October 2026 and points to a Rocq proof. Its headline still says
  `N_ZF <= 432`; that headline is stale relative to its own history table.
- <https://github.com/jeff87654/busy-beaver/tree/zf-254/ZF/m254>.
  GitHub plugin resolved branch `zf-254` to
  `c132d7eae8158cd3a9850ea3eb7251158c3dd821` in this session. The README,
  actual `coq/e2e/E2E254.v`, set-theory definition and design notes were read.
- <https://github.com/VladimirReshetnikov/ProveIt/blob/main/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/README.md>.
- <https://github.com/VladimirReshetnikov/ProveIt/blob/main/Computability/BusyBeaver/Research/ZFC/candidate-prefix246/README.md>.

The GitHub web-retrieval path failed on the source files; the GitHub plugin
successfully supplied their complete contents. These are primary repository
sources, not independent reproduction of their proof builds.

## Exact 254 theorem

The prior-art README identifies Mira-Cult as the designer of the machine
and source theory, Jeff Ketchersid as the author of the end-to-end Coq proof,
and Wade's compiler framework as a dependency. The literal machine SHA-256
is `d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb`.

`E2E254.v` has actual Qed-terminated declarations

    zf254_halts_iff_SIR
    zf254_halts_iff_ZF
    zf254_halts_iff_ZFC

The last target is the library's closed-scheme ZF theory plus its literal
Choice axiom. Inspecting `Std_iface.v` shows that this literal ZFc predicate
omits Foundation: its base has equality, Extensionality, Empty Set, Pairing,
Union and Power, followed by closed Separation/Replacement and Infinity.
The separate RegCon interpretation supplies the Foundation consistency
comparison. Therefore the final standard-ZFC comparison should retain that
bridge, rather than claiming Foundation occurs in the literal E2E axiom set.
The composed chain, with that qualification, is

    literal TM <-> register program <-> proof enumerator
      <-> code-level calculus derives 1 <-> SIR refutes
      <-> ZF refutes <-> ZFC refutes.

The README reports all three `Print Assumptions` results as closed under the
global context, and its `check.py` recompiles the full source closure and
compares the literal transition table. This audit inspected source and
documented assertions; it did not itself run that Coq build.

## Theory and sensitive invariants

SIR is ordinary first-order logic with equality, CP, global-image collection
and raw irreflexivity. CP and GIC are:

    CP: forall p exists V,
          p in V and forall x in V,
            x subset V and exists W in V,
              forall z (z subset x -> z in W).

    GIC(phi): forall B exists C,
          (forall a in B forall y,
              phi(a,y) -> exists y' in C, phi(a,y'))
          and (forall y in C exists x, phi(x,y)).

Irreflexivity is crucial to the relative-falsity alias `1 = Rel(0,0)` and
the degenerate a=b bundle instances. The c!=a,b gate is essential. The
code's atom orientation is direct membership, not its converse.

For one direction of equiconsistency, a represented bisimulation quotient
of SIR supplies ZF without the original raw relation being extensional.
The quotient construction does not transfer raw irreflexivity for free;
the ProveIt `quotient_ir_obstruction.md` already gives a concrete definable
counterexample. For the other direction, the actual Coq development
relativizes SIR to L and removes Regularity using a separate relative
consistency theorem. Earlier design files retain obsolete "remaining work"
sections; the actual completed E2E module and current README supersede them.

## Distinguishing the targets

The 252-state ProveIt README reports a closed external Lean equivalence to
its literal ZFC proof predicate. It explicitly leaves PA internalization
open. The 246-state candidate README reports an ordinary mathematical
argument in ZFC, while its exact-machine Lean endpoint and PA-internal
equivalence remain open. The conditional 246 runtime theorem retains
coverage and initial-related-frame hypotheses; later finite checks must be
composed to discharge those hypotheses.

The user's present requirement is provability of the nonhalting/consistency
equivalence *in ZFC*. This is distinct from both an external Lean/Rocq
metatheorem and the stronger internally coded PA proof requirement. A
finitary proof can be described as formalizable in ZFC if its actual
simulation and theory-calibration argument is given; the mere presence of
an external theorem does not itself provide a serialized internal proof.

Finally, consistency alone excludes a ZFC proof of nonhalting once the
equivalence is proved in ZFC (Gödel II). To exclude a ZFC proof of halting
as well, an appropriate arithmetical soundness assumption is needed. A
consistent but Sigma_1-unsound theory can prove a false halting statement.
The machine-equivalence objective does not require conflating those two
independence directions.

## Existing routes that should not be relabeled as new

- Equality elimination using two-sided observational profiles:
  `raw_psc.md`, `logical_engine_completeness.md`.
- The failure of reduced equality-free C/G logic, including only fresh
  injective renaming or same-variable instantiation: `typed_countermodel.md`.
- Removing successful MP's dummy push: `mp_dummy_push_partial_cost.md`.
- Relative-falsity obstruction to replacing rho6 by its dual:
  `dual_quantifier_gap.md`.
- Rebracketing/exact-word Re-Pair and conjunction changes with complete
  original row order: `full_grammar_experiment.py`,
  `layout_grammar_experiment.py`.

The additional complete-row permutation lane and its exact compiler
transfer are developed separately in `axiom_row_permutation.md`.
