# Primary sources and source-model conventions

Consulted 20 September 2026. No third-party paper PDF or font file is included
in the archive. The article and experiments can be read and run without
accessing these external sources.

## Marek Szykuła, Synchronizing Automata: Open Problems

- arXiv: https://arxiv.org/abs/2608.24245
- PDF: https://arxiv.org/pdf/2608.24245
- Published reference: EPTCS 451 (2026), pages 33-47.
- DOI: 10.4204/EPTCS.451.3.
- Version consulted: v1, 25 August 2026.
- Relevant material: Section 2.3, Conjecture 8 and Figure 3, printed page 37
  (PDF page index 4). The diagram was inspected as a rendered page.

This is the source for the family and selected open synchronization clause.
The printed transition cases do not give b(q_0), and omit one transition at
q_(3k+5). Figure 3 gives b(q_0)=q_1 and the endpoint's nonloop return arrow.
The complete definition in article.tex makes both choices explicit.
The credited Dżyga thesis was not examined; no claim about its exact contents
or historical priority is based on an imagined reading of that thesis.

## Korea Superintelligence Labs / Machina Mathematica

- Landing page: https://ideosphere.ai/papers/cwa-series
- Archived version: https://ideosphere.ai/papers/cwa-series-v1.pdf
- Source snapshot on landing page: 2026-09-07 03:53 UTC.
- Status listed by source: AI-generated and AI-reviewed preprint;
  independent human review open.

This prior note gives the all-k short merging word and the one-letter
correction, and reports finite threshold checks to k=60, synchronization to
k=40 and the pair-diameter formula to k=16. Both its abstract and its scope
statement explicitly leave synchronization for every k and the universal
threshold lower bound open. Those records are the priority boundary used in
this draft. The note's reported Lean dossier was NOT built in this session.
Our own finite certificates were computed from the transition model and
verified independently, not extracted from that dossier.

## Enkai Zhang, triple rendezvous preprint

- https://arxiv.org/abs/2609.19173
- HTML consulted: https://arxiv.org/html/2609.19173v1
- Version: v1, 14 September 2026.

This paper concerns a different family and a different invariant: merging
some triple, rather than merging a designated state or resetting all states.
Its appearance prevents conflating similar 4n/3 numerical expressions with
a solution of the present family-specific problem. The present article uses
none of its results as a lemma in the synchronization proof.

## Literature-search limitation

A targeted search and these explicit open-status statements support selecting
the problem. They are not a proof that no other author has already found an
all-parameter construction. The article states its theorem and proof directly
and leaves priority, independent review, and possible improvements open.
