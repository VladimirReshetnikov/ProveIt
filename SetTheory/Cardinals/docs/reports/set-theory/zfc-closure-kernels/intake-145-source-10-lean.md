# AtomicEquality independent intake review (batch145)

Read the complete197-line delivered `formal/AtomicEquality.lean`, README.txt, PROVENANCE.json and report sections on two-sided equality, finite proof transport and formal status (report.tex:390-625). Original extraction `/tmp/zfc-intake-145-zfno7ajz/01-zfc_small_machine_research/zfc_small_machine` was not modified. Only a separate file copy was compiled, and nothing was imported into the research Lean library. No manifest/integrity or line-ending checks.

## Compilation

Pinned compiler: Lean4.32.0, commit8c9756b28d64dab099da31a4c09229a9e6a2ef35, Release. The copied file imports only Init and compiled successfully in0.58s with the explicit scratch root. Exact command and seven axiom reports are in review.json and lean-check.txt beside this note. A first invocation from the repository without --root was rejected by Lean's external-file root check before compilation; adding the scratch root resolved that environmental invocation constraint. It was not a source failure.

All seven principal theorems report **no axiom dependencies**:

- indiscernible_refl
- indiscernible_symm
- indiscernible_trans
- membership_congr
- satisfaction_invariant
- equalityFormula_correct
- equality_erasure_correct

No sorry, custom axiom or semantic oracle occurs. atomicSetoid and push_related are also proved/defined without admissions; the file only prints the seven listed audit roots.

## Semantic audit

No defect found in the statements, proofs or advertised formal boundary.

Indiscernible(R,a,b) at lines24-25 is exact agreement of both columns and rows of arbitrary binaryR. The first four theorems establish its equivalence properties and membership congruence. Nothing assumes Extensionality, CP/GIC, irreflexivity or incoming-profile congruence. This relation can identify distinct raw objects.

The formula syntax is a standalone de Bruijn language with membership, primitive False, conjunction, implication, biconditional and universal quantification. Sat at78-85 uses push(a,v)(0)=a and push(a,v)(n+1)=v(n). satisfaction_invariant at103 is genuine induction over every formula in this language and every pointwise Indiscernible-related valuation. Under a universal binder it compares the same arbitrary bound object on both sides; reflexivity proves the extended valuations related. Empty underlying types are harmless (statements about valuations are vacuous there); the file does not infer model existence from them.

The equality atom erasure at144-147 inserts one universal binder and shifts BOTH original indices to i+1,j+1. Hence the new index0 names only the local comparison object; index0 in an original equality atom correctly becomes1. The outer all case of eraseEquality recursively uses this same operation under the already-pushed environment. equalityFormula_correct at149 checks that exact binder semantics for arbitrary i,j/valuations, including equal indices and nested outer binders. No capture flaw was found.

equality_erasure_correct at168 has RHS SatWithEquality(R,Indiscernible(R),v,p), with the equality relation supplied as a semantic parameter. It does NOT compare the erasure with literal Lean equality on an arbitrary raw structure. That stronger statement would be false: on two distinct objects with empty membership, Indiscernible is universal while actual identity is not. The comment at167 and report.tex:610-612 explicitly retain this distinction. The actual theorem is useful and correct.

## What is not formalized

No free-variable/renaming/substitution algorithm or substitution-commutation theorem; no first-order proof datatype/calculus/soundness/completeness/derivation translator; no CP/GIC axiom definitions or matrix-skeleton compatibility theorem; no actual Quotient construction or quotient satisfaction theorem; no ordinary ZFC calibration, proof-code arithmetic internalization or machine compiler. The de Bruijn semantic binder lemma supports capture-safe equality replacement, but must not be described as verified arbitrary capture-avoiding proof substitution. Exists/Or can be defined by the classical basis, but their syntax/calculus is not separately implemented here.

The report's primitive-recursive proof-translation/PA formalizability and source-theory equiconsistency remain ordinary mathematical arguments, not consequences newly proved by this file. Those arguments match the standard two-sided equality-erasure method already audited for source09; no mathematical issue found in the displayed fixed-template argument. Imported source calibration and its regularity/Choice bridges must retain their own attribution/status.

## Current overlap and provenance

Report baseline is ProveIt17d0f2eaa650901cda59764dfcc4661c199e49c8, with requested pins b07d1a27b,83ef1da6b,67086c8d,6594795e and later references fa6fcaf0/29efd22e; upstream297ab8df7. This is pinned provenance, not a statement that all current gaps remain.

`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RawPSCProfile.lean:22-23` already defines the SAME two-sided relation as Full(mem,x,y):=Same(mem,x,y) AND forallz(memx z iff memy z). Its full_refl:34,full_symm:37,full_trans:40,full_mem_congr:44 already prove the first four semantic facts. RawPSCProfile uses it for twin-singleton decoding/Separation/Union under specific PSC resources. The delivery does not supply that bootstrap; conversely our RawPSCProfile does not yet contain the delivery's standalone all-formula satisfaction-invariance and equality-erasure syntax theorem. Those last three are genuinely additional checked semantic components in their own syntax, requiring an explicit adapter before reuse with existing SetTheory.Form.

`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-144-source-09.md:3` already records the ordinary two-sided equality-elimination argument for nonextensional CP/GIC in the previous delivery. The present report gives a more explicit formal semantic component and compiler/control experiments. It should not be credited with originating the relation or first resolving an unchanged current mathematical gap. Its own attribution calls the construction standard equality-free model theory.

Incoming-only Profile.Same, hereditary saturation's interpreted equality, and bisimulation Eqv are different relations with different hypotheses. No incoming-profile CG theorem should be erased merely because this full-profile relation is automatically congruent. No deletion of runtime equality rows follows from the source-theory erasure.

## Recommendation

Place the delivered Lean file as unedited source material through the intake procedure. Its seven successful no-axiom reports are verified intake findings. Preserve its precise semantic nonclaims and distinguish its standalone syntax from the current research modules. Do not copy it into the Lean library during placement; a later explicit SetTheory.Form adapter/proof-transport development is a separate research change.
