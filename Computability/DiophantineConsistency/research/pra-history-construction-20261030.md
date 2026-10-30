# Constructing the primitive-recursive history code

The remaining witness for Foundation's `PR.Blueprint.resultDef` is a code `s` satisfying the actual `cseqDef` and the requested `memRel` entry. The existing bounded `cseqDef` theorems assume this code and the local blueprint bounds; they do not construct it. Foundation's `PR.Construction.CSeq.exists` obtains the history using IΣ₁ induction, so that theorem cannot simply be used for arbitrary candidate-PRA models.

`PRAHistoryPairCode.lean` supplies the first concrete component of the intended constructor. Its explicit `pairCode` uses the candidate-PRA less-than characteristic, addition, multiplication, and selection to compute Foundation's exact `pair` in every candidate-PRA model. The proved sentence `PRA_proves_pairCodeGraph` asserts that the result satisfies the actual mapped Foundation `pairDef`; the theorem does not depend on IΣ₁.

`PRAHistoryExpCode.lean` supplies a second component: its explicit primitive-recursive code starts at one and doubles at each step. Candidate PRA proves that its value satisfies Foundation's exact `exponentialDef`. The proof uses Foundation's IΣ₀ base and successor properties, the candidate-PRA bounded-formula characteristic compiler, and open induction applied to the recursive code. Foundation's IΣ₁ existential-totality theorem is not used. In particular, this is all-model correctness for the actual graph rather than only standard-natural computation.

The later length and insertion codes, combined with pairing, now provide a
candidate-PRA sequence append constructor for the exact `seqConsDef` graph.
The recursive iterator has checked base and step equations for supplied
codes, but preservation of the actual `cseqDef` invariant remains open. The
blueprint's zero and successor graphs, its size bounds, and the concrete
refutation predicate remain separate obligations. No proof of the complete
history witness or HA equivalence is claimed here.

## Direct syntax-checking alternative

`AnnotatedRefutationPR.refutationProgram_primrec` is an explicit primitive-recursive checker, but it checks a separate annotated sealed-ZFC certificate and natural-deduction calculus. Foundation's `Derivation.blueprint` uses its own HFS/Gödel encodings and sequent calculus. Its standard-natural checker theorem and `PRAFiniteFunctionCodes.exists_code_of_primrec` do not establish correctness in nonstandard candidate-PRA models and do not identify the actual Foundation core. Reusing that checker would need an internally proved encoding and calculus translation in addition to its code semantics.

A direct characteristic for the actual Foundation core can instead be built bottom-up. Candidate-PRA graph correctness is required for the Foundation pairing and projections and bit operations; the pairing, exponential, insertion and append components now have such proofs. Next come all-model codes for UFormula/UTerm recognition and BV, with equivalence to the corresponding actual Foundation Δ₁ graphs, followed by codes and all-model graph correctness for negation, free-variable conversion, substitution, set shift, and the concrete ZFC axiom predicate. The final checker must establish the bounded ten-rule disjunction for both the actual sigma and pi core formulas, including their common correctness, in candidate PRA. The existing `PRADerivationCoreSigmaBound` still assumes a formula-set bound and a rule-tail bound, and its pi counterpart has separate explicit assumptions, so those certificates do not yet supply that characteristic.

`PRAHistoryFixpointCollector` now provides an explicit PR collection loop with a model-uniform invariant: after `n` iterations its bitset contains precisely the indices below `n` selected by the supplied Boolean core code. This invariant is proved by quantifier-free induction using a compiled characteristic for the actual bounded bit graph. Its assumptions include candidate-PRA certificates for the core code's Boolean range, the insertion code's actual graph, and the bit characteristic. It does not itself establish the actual derivation core characteristic or the full fixpoint successor graph.
