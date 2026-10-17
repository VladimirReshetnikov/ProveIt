# Proof boundary of candidate-permutation252

Pinned source: ProveIt `43026ff42f0939f09b9e95495248cfadcad38e38`.

## Finding

The maintained endpoint is an external Lean theorem, not an exported proof in
the repository's internally represented ZFC calculus. It is therefore wrong
to describe the existing Lean object itself as a kernel-checked *ZFC proof*.
For the user's present requirement, however, the open PA internalization is
not the relevant mathematical obstacle. The displayed proof has an ordinary
set-theoretic formulation using only set-sized structures, countable syntax,
finite derivations, recursion on omega, quotient sets, definable submodels,
and the first-order completeness theorem. These are all available in ZFC.
An ordinary ZFC-formalizability argument is materially weaker than supplying
the already-studied all-internal PA proof-code translation.

This note gives the exact metamathematical criterion and explains the
set-sized interpretation of the maintained construction. It does not export
a formally checked object-language ZFC derivation or claim that every Lean
proof automatically translates into ZFC.

## Set-coded comparison theorem

Work *inside ZFC*. Let S and T be recursive first-order theories in countable
languages. Fix explicit natural-number encodings of their finite formulas
and finite derivations. Augment proof codes with bounded accepting-computation
witnesses for any recursive axiom tests, so that `Prf_S(p, Bot)` can be chosen
primitive recursive (analogously for T). Without that coding convention, a
recursive proof predicate suffices for the same argument. Let M be a fixed finite Turing
machine with blank initial configuration; `Halt_M(t)` says that its recursively
defined configuration after t steps is halting. Suppose ZFC proves:

1. `exists t in omega, Halt_M(t)` iff `exists p in omega, Prf_S(p, Bot)`;
2. every nonempty set-coded S-model gives a nonempty set-coded T-model;
3. every nonempty set-coded T-model gives a nonempty set-coded S-model.

Then

`ZFC proves Nonhalt(M) iff Con(T)`.

Proof: formalized completeness gives
`Con(S) iff exists nonempty set-coded model of S`, and the same for T.
The two model constructions give `Con(S) iff Con(T)`. Negating the finite
witness equivalence in (1) gives `Nonhalt(M) iff Con(S)`, and composition
finishes. This uses no assumption that S or T is consistent. It also does not
assert that either consistency statement holds. All quantifiers over proofs
or times are over the metatheory's own omega, not an externally fixed list of
standard numerals.

For a recursive theory it is enough to take the completeness model on a
subset of omega: a Henkin term model is countable. An arbitrary set-sized
model construction can subsequently be replaced by a countable elementary
submodel if desired. Countability of the output is unnecessary for the
consistency implication.

The same proof permits a finite chain of syntactic and semantic comparisons.
The model constructions do not have to preserve carriers, and no uniform
effective transformation of refutation codes is required by this ZFC proof.

## Application to the maintained source

The finite chain is:

1. literal blank-tape binary machine M252;
2. actual finite register-program execution;
3. existence of a finite C254 derivation of numeric falsity F=1;
4. a finite refutation of NativeAx;
5. a finite ZF refutation;
6. a finite ZFC refutation.

The exact native theory has the universal closures of one CP container
sentence, every native-formula GIC instance, and irreflexivity
`forall x, x in x implies Bot`. Logical equality is present. Foundation,
Choice and Extensionality are not extra native axioms.

The inspected declarations provide the following interfaces:

* `NativeTheory254.c254_refutation_iff`: C254 F iff NativeAx refutable.
* `ZFNative.native_of_zf`: every ZF model satisfies NativeAx on the same
  carrier; containers arise from internal ranks and GIC from Collection.
* `WFModel.quotient_models_ZF` and `WFTheory.c254_refutation_iff_zf`:
  the CP/GIC quotient followed by its internally well-founded part is a
  nonempty ZF model. Internally well-founded is a definable predicate inside
  the arbitrary model, not a claim of external well-foundedness.
* `ChoiceCalibration254.constructible_models_ZFC`: the internally
  constructible subtype of every ZF model is a ZFC model. Its Choice theorem
  is proved from its internal V=L; Choice is not imposed on the original
  ZF-model's relation.
* `ChoiceCalibration254.constructible_nonempty`: an explicit empty ordinal
  gives an inhabitant. This matters because first-order semantics use
  nonempty domains.
* `ChoiceCalibration254.zf_refutation_iff_zfc`: ordinary finite-refutation
  comparison by soundness/completeness and the L-model construction.
* `BinaryZFC252.nonhalting_iff_zfc_consistency`: the closed composed external
  endpoint about the actual binary machine.

Every source object mentioned here admits a set-sized representation:

* `Form`, proof trees and command trees are finite trees coded by omega.
  Inductive `Prop` derivability means the least finite-rule closure, hence
  existence of a finite coded derivation. The coding lemma is proved by
  induction on derivations, in both directions.
  Some auxiliary named-syntax adapters additionally carry functions
  `Nat -> Nat`; those objects must not be called natural-number codes.
  They are nevertheless set-coded objects, since `omega^omega` is a set
  and finite trees with labels from a set form a set. ZFC can use these
  auxiliary objects while the actual endpoint retains its finite `Form`,
  numeric derivation and machine-trace codings. The PA proof-code project
  needs the separate finite-support adapter documented in the source.
* A tape configuration is a state, an integer head, and a finite subset of
  integers marking the one-cells. Its deterministic step and omega-iteration
  are set functions. This accounts for arbitrary internally finite times,
  rather than only bounded sample runs.
* For a carrier D, a structure is `(D,E)` with `E subset D x D`.
  All valuations form the set `D^omega`. Satisfaction of coded formulas is
  defined by recursion on finite syntax; it is a satisfaction predicate for
  a *set structure*, and does not violate Tarski's undefinability theorem.
* A quotient carrier is a subset of P(D), and a subtype is a subset of D.
  Power Set, Separation and Replacement provide these actual sets.
* Full GIC and the Separation/Replacement schemes quantify over the set of
  finite formulas. The maintained lemmas are uniform in `phi : Form`; no
  inference from a collection of external standard instances is necessary.
* L is taken internally to a set-coded model. Its definable domain is a
  subset of that model's carrier. The construction does not require a set
  containing the ambient universe of all sets, and it does not assume that
  the given model is externally well-founded.

The Lean universe parameter can therefore be removed by giving these direct
set-coded definitions. The audit of axiom names alone would not establish
this: the justification is the concrete mathematical reconstruction above.

## Precise reporting language

Suitable: "The reduction proof is formalizable in ZFC by set-coded syntax,
finite traces, and set-model completeness. The supplied machine comparison
inherits the existing externally checked Lean endpoint. This package does
not contain an exported proof in the internal ZFC calculus."

Unsuitable: "Lean's use of only propext, Classical.choice and Quot.sound
automatically gives a ZFC proof," or "the PA gap has been closed."

If a new M251 is obtained, it still needs a universal finite-trace comparison
with M252 (or independent soundness and completeness). A long agreeing run,
graph reachability, or agreement on sampled register frames is not that
comparison. A set-coded proof of a finite inductive simulation certificate
would transfer the present ZFC-formalizability argument directly.

## Exact primary-source links inspected

All links below use the pinned commit.

* https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/README.md
* https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Research/ZFC/pa_internalization.md
* https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NativeTheory254.lean
* https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ZFNative.lean
* https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFModel.lean
* https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFTheory.lean
* https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ChoiceCalibration254.lean
* https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/BinaryZFC252.lean
