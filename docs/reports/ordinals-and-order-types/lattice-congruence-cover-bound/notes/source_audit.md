# Source and exclusion audit

Checked: 20 September 2026.

## Primary target

Gábor Czédli, *Accumulation points of congruence densities of finite lattices*.

- Abstract/version history: https://arxiv.org/abs/2603.11454
- Stable version: https://arxiv.org/abs/2603.11454v1
- PDF: https://arxiv.org/pdf/2603.11454
- DOI: https://doi.org/10.48550/arXiv.2603.11454
- Version date: 12 March 2026; 17 pages.
- Target location: printed page 8, the sentence immediately after Lemma 4.4.

Lemma 4.4 assumes at least R_{k-1}(k) upper covers, for k >= 3, to conclude density
at most 2^(-k). The following sentence suggests that only k covers may suffice.
This is the exact target, not a stronger statement silently attributed to the
source. The local term “k-cover question” is ours.

The mathematical formulas on pages 8, 10, and 11 were inspected in rendered
PDF screenshots, not inferred from HTML that omits some formula content.

Other source locations used:
- Section 3: classical principal-label/ideal tools (reproved in our article).
- Lemma 4.3, pages 7–8: the previously proved common-pairwise-join special case.
- Equation (5.1), page 10: exact definition of Skel(L).
- Lemmas 5.2–5.4: structural interpretation by skeletons and chain segments.
- Lemma 5.5: earlier Ramsey-based bound on skeleton size.

## Current source status

Author publication list:
https://www.math.u-szeged.hu/~czedli/m/listak/publist.html

Entry 195 reports acceptance in CUBO on 14 August 2026 and dates the linked
manuscript 12 March 2026. ArXiv listed only v1 on retrieval. The direct author
PDF link and its TinyURL alias failed in the browsing tool; the arXiv PDF was
fully accessible and is the version used for the target and proofs. The
publication-list metadata is not evidence of a later resolution of the remark.

## Related primary context

Gábor Czédli, *Lattices with congruence densities larger than 3/32*.
- https://arxiv.org/abs/2602.04321
- Author PDF consulted:
  https://www.math.u-szeged.hu/~czedli/m/publ.pdf/czedli-cd-3-32.pdf
- That PDF internally states “Version of July 28, 2026”, although the publication
  list's linked-version parenthetical still says June 14. The article cites the
  PDF's own date.
- It gives a classification above density 3/32. Thus low-parameter overlap is
  acknowledged; the present draft does not claim each k=3 consequence as new.

Ralph Freese, *Computing congruence lattices of finite lattices*, Proceedings of
the American Mathematical Society 125(12) (1997), 3457–3463.
- https://doi.org/10.1090/S0002-9939-97-04332-3
- Original author-uploaded text was accessible via ResearchGate; bibliographic
  information is also in the cited Czédli paper and the author's publication
  archive at https://latticetheory.org/assets/Freese/.
- The publisher DOI endpoint was not accessible through the browsing tool.
- Historical attribution of the 2^(n-1) bound; every required tool is proved
  afresh in the draft, so no unexamined external theorem is a proof dependency.

## Search for an existing resolution

Queries included the exact title and combinations such as:
- "congruence" "lattice" "k covers"
- "congruence density" "covers"
- "congruence densities" Ramsey
- "2603.11454" "covers"
- "Czédli" "cover bound"

The relevant results led to the source, its author publication list, and earlier
density papers. No resolution of the all-k suggestion was located. Unrelated
search results and automated secondary paper summaries were not used as
mathematical evidence. This is a bounded literature search, not a priority proof.

## Exclusion manifest

The user-supplied manifest(1).tex (1095 source lines, 71 catalogued packages) was
read in full with the Files tool. All listed problems were excluded regardless
of their independent verification status. None is the finite-lattice
congruence-density cover question or the skeleton bound considered here.
The selection does not extend one of the listed ordinal/poset invariants under
a new name; it concerns congruences of finite algebraic lattices.

The original manifest is not redistributed. It is cited as an input exclusion
list, not used as a source of mathematical results.

## No source files redistributed

The package contains original exposition, code, and generated verification
records. It does not bundle the cited papers, screenshots of them, or font files.
