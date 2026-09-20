# Sources and current-status audit

Audit date: **20 September 2026**.

## The explicitly open target

Pierre Popoli, Jeffrey Shallit and Manon Stipulanti, **Additive Word Complexity and Walnut**.

- Full preprint inspected: https://arxiv.org/html/2410.02409v1
- Abstract/version record: https://arxiv.org/abs/2410.02409
- PDF: https://arxiv.org/pdf/2410.02409
- Published version: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSTTCS.2024.32
- DOI: https://doi.org/10.4230/LIPIcs.FSTTCS.2024.32
- LIPIcs 323 (FSTTCS 2024), Article 32, 32:1–32:18.

**Theorem and remark numbering in this package refers to the full arXiv v1 preprint.** The abstract record inspected listed only v1, submitted 3 October 2024.

Theorem 18 gives the possible additive-complexity values `{3,4,5}` for positive Tribonacci-word lengths, proves each occurs infinitely often, and supplies a 76-state Tribonacci DFAO. Remark 19, on printed page 10, explicitly leaves their respective proportions open. That part of the PDF was also inspected as a page image. We interpret the target as natural density over integer lengths and prove that stronger precise formulation.

The prior range theorem, automaticity, and the state count are credited to this source, not presented as new results. The machine supplied here is independently reconstructed; its serialization is not claimed to coincide with the authors' original file.

## Co-decomposition background

Ondřej Turek, **Abelian Complexity Function of the Tribonacci Word**, Journal of Integer Sequences 18 (2015), Article 15.3.4.

- Journal landing page: https://cs.uwaterloo.ca/journals/JIS/VOL18/Turek/turek3.html
- Journal full text: https://cs.uwaterloo.ca/journals/JIS/VOL18/Turek/turek3.pdf
- Preprint: https://arxiv.org/abs/1309.4810v2

This supplies the prior co-decomposition framework and its automata application. Section 3 of the new article proves the particular coverage, independence and digit-update claims directly. The code was written independently for this task and is not copied from a third-party repository.

## Later related work checked

Jean-Michel Couvreur, Martin Delacourt, Nicolas Ollinger, Pierre Popoli, Jeffrey Shallit and Manon Stipulanti, **Effective Computation of Generalized Abelian Complexity for Pisot Type Substitutive Sequences**.

- Latest listed version inspected: https://arxiv.org/html/2504.13584v2
- Abstract/version record: https://arxiv.org/abs/2504.13584
- v1: 18 April 2025; v2: 22 April 2025.

This concerns more general abelian-type complexity automata and related Tribonacci properties. It is cited as related work and as part of the status audit, not as a proof of the present densities. Text searches for `proportion` and `density` in v2 returned no matches. Absence of those terms is not by itself proof that no related result exists; the audit conclusion remains limited.

The search also surfaced Jeffrey Shallit's **The Tribonacci constant and finite automata**, arXiv:2510.10834. Its abstract concerns synchronization/automaticity of a floor sequence and a characteristic Sturmian word, not the additive-complexity density target. It is not used in the proof.

## Search queries

Focused searches included the following literal combinations, together with the primary pages above:

- `"Tribonacci" "additive complexity" "density"`
- `"Tribonacci" "additive complexity" "proportion"`
- `"Tribonacci" "additive complexity" "densities"`
- `"Remark 19" "Tribonacci" "proportion"`
- `"Tribonacci" "0.279527"`

No later resolution of the selected question was found in the checked results. This is a bounded literature audit, **not** a guarantee of first discovery. A previously published or unpublished solution could have escaped retrieval.

## Source-derived versus new content

Source-derived: definition and study of additive complexity; known range `{3,4,5}` and prior 76-state DFAO; the explicit proportion question; co-decomposition as a method.

Independently developed and verified here: the serialized additive-output quotient, the exact eigenvector aggregation yielding the proposed densities, the exact spectral certificate, the uniform prefix-cylinder estimate for every integer cutoff, and the counting/GF artifacts and verification code.

No article in the supplied manifest is used as a theorem in the proof. That file serves only as an exclusion catalogue; its proof claims are not independently endorsed by this package.
