# Exact Foundation PA consistency endpoint

The current root is ProveIt `8d31445d858761a8f6150c2e5012adae8895e932`. The root investigator checked its Git tree entry for `lib/FormalizedFormalLogic-Foundation`:

`160000 commit 32e1a0956a8622fad067328ca1959729a7634428`.

This is exactly the current Foundation revision explicitly named by the revised AX11H written adapter. The imported PA196/PA209 vendor trees are historical source snapshots; they must not be silently substituted for this current theory.

## Definitions checked in the current source

In `Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRAPA196Consistency.lean`:

1. `paConsistency` is Foundation's actual arithmetic consistency sentence for its classical `PA` theory.
2. `paRefutation = provabilityPred PA bottom` and `paConsistency = not paRefutation` definitionally.
3. `mappedPARefutation = Semiformula.lMap embedding paRefutation` maps that classical sentence into the primitive-recursive code language.
4. `nativePARefutation = native mappedPARefutation` reads the mapped NNF syntax with intuitionistic connectives.
5. `nativePAConsistency = not nativePARefutation` is the desired ordinary negative consistency sentence.
6. `translatedPAConsistency` is instead the Goedel-Gentzen image of the mapped classical consistency sentence. The file distinguishes it from `nativePAConsistency`; their comparison requires a backward double-negation bridge.

The standard-natural-number theorem in that file checks the source consistency coding. Its comments explicitly say that it neither identifies the independent PA196 FFL coding nor defines a machine halting sentence.

## Checked bridge and conditional endpoint

`Computability/BusyBeaver/Research/PA/pa194/ipra/PA194RefutationBridge.lean` proves `mapped_refutation_iff`: in a PR-language structure whose arithmetic reduct satisfies current I-Sigma-1, evaluation of `mappedPARefutation` is equivalent to existence of an internal Foundation `Proof PA d code(bottom)`. The witness may be nonstandard. The statement contains no machine run.

`PA194Endpoint.lean` derives the negative equivalence from two explicitly supplied native proofs:

- native PA refutation implies double-negation of the exact PA194 halting sentence;
- the exact halting sentence implies double-negation of native PA refutation.

`PA194PRAAssembly.lean` obtains those native implications from two explicitly supplied classical PRA reductions, using the machine-independent PA witness certificate and the Goedel-Gentzen transfer. Its final theorem still has the hypotheses

`PRA proves mappedPARefutation -> haltClassical` and
`PRA proves haltClassical -> mappedPARefutation`.

No such hypothesis was silently discharged by reading, compiling, or replaying the comparison artifacts. The current primary README says these machine-specific reductions remain open.

## What the revised AX11H argument supplies in writing

The exact source `Computability/BusyBeaver/Research/PA/docs/pa194_ax11h_research_2026-11-14_2/proof/foundation_paeq_completion.tex` has a separate section binding the current Foundation predicate. It names the same current Foundation pin, distinguishes current and historical PA theory predicates, and gives an adapter rather than asserting they are identical.

The syntax uses Foundation's square pairing, not the TM's Cantor pairing. The falsity code is 13. The logical proof constructor equations are compared directly. The current induction recognizer's canonical closure convention and the changed finite axiom receive explicit adapters. The resulting written theorem supplies a total primitive-recursive function mapping current Foundation PA refutations to ordinary-PAeq refutations in every current I-Sigma-1 model, including internally nonstandard proof codes.

That is the correct endpoint for the independent ordinary-PAeq-to-numerical-calculus compiler and the I-Sigma-1/iPRA transfer. The revised AX11H physical/source/calibration files then claim the full written iPRA equivalence. They do not supply a new end-to-end Lean proof for AX11H or discharge the separate primary PA194 Lean assembly by assumption.

The comparison therefore uses a precise distinction: the source sentence and its generic bridges are formalized components; the inherited AX11H full calibration is a substantial written mathematical argument; the new machine's logical emitter and physical execution are separately checked interfaces. This note checked their names and dependency alignment, not every clause of Foundation's current metatheory or a fresh kernel build of the full endpoint.
