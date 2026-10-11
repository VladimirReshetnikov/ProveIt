# Source audit and provenance

Retrieval/work date: **10 October 2026**, using the date supplied for this conversation. The audit is targeted, not repository-wide.

## Connected repository

Repository: `VladimirReshetnikov/ProveIt`.

The connected GitHub tool was used for both user-supplied directory URLs. Targeted reads included the root manuscript source (`polylogarithms.tex`), `chapters/10-discovery.tex`, a returned portion of `chapters/04-cyclotomic-quotients.tex`, and the incoming-directory listing. Some large connector responses were truncated. The report does not present those partial returns as complete file audits.

The revised candidate source was read with an explicit pin:

- Path: `Analysis/Polylogarithms/docs/manuscript/chapters/04-S8-candidate.tex`
- Commit: `1aeabfa735c78a30b732405b101009d376d56f18`
- Returned Git blob SHA: `39c85e8ad5b5c288b77f9c1281cb0c8a116b1afb`

It explicitly distinguishes its revised S8 vector from an earlier rejected one, and reports an enclosure containing zero rather than a proof of equality. That status is preserved. Other reads used `main` or search-result snapshots; **the above commit is not falsely assigned to every read**. Repository search later surfaced another commit, so no claim of a frozen whole-repository audit is made.

The incoming directory listed several newer packages, including titles concerning Barnes resolvents, cubic harmonic mixed orders, and commensurate Lerch calculus. Their binary ZIP contents were not successfully inspected through the available retrieval routes. A connected UTF-8 fetch is not a binary-archive reader; fallback downloads failed. Filenames are not treated as proof of overlap or non-overlap. Some contain `2026-10-11`; these are recorded naming observations, not independently established publication dates.

## Directly inspected predecessor from the Library

File: `ProveIt_Reciprocal_Lerch_Convolutions_2026-10-10.tex`

- Library file ID: `file_00000000beec8230aa41fb2b21c1d873`
- Version: 1
- Size: 75,061 bytes
- SHA-256: `5e8d2425fb7f385b46306829f319a67966d2ea526f2e12ceb8b90b5919b6992d`
- Its own source-anchor string: `0c740647c48baec7f0b4192723e977d69917dd52`

The Library search/read tools established the profile definitions, weighted transform, the unequal-shift section, the integral-shift arithmetic theorem, and Q1–Q3. The TEX source was materialized into the working container for mathematical and source comparison. Relevant contiguous locations are approximately lines 80–379 (foundation), 990–1048 (Gaussian odd parts), 1139–1358 (unequal shifts and harmonic collapse), and 1640–1739 (research questions). The full source was available for programmatic reference after materialization; it is not redistributed in this new report package.

The preceding report proves equal-parity cancellation as a **sufficient** condition. Our mixed-parity family is an extension, not a counterexample to its actual theorem. It also contains a Gaussian odd-part/odd-part pairing; the new mixed negative-axis/odd-part pairing is explicitly distinguished in Section 5.3.

Other Library search results were used only to orient the topic, not as unexamined mathematical premises. In particular, titles alone from previous outputs are not taken as established results.

## Public mathematical references

The following primary/authoritative pages were consulted and are cited in the article:

- NIST DLMF: `https://dlmf.nist.gov/25.11`, `https://dlmf.nist.gov/25.12`, `https://dlmf.nist.gov/25.14`, and `https://dlmf.nist.gov/5.5`.
- J. P. Selvaggi and J. A. Selvaggi, 2018 real-convolution article, DOI `10.1155/2018/5941485`; the publisher page supplies the bibliographic metadata and method description.
- C. de Boor, *Divided Differences*, arXiv `math/0502036`; published in *Surveys in Approximation Theory* 1 (2005), 46–69.
- A. Granville's author-hosted account of binomial coefficients modulo prime powers: `https://dms.umontreal.ca/~andrew/Binomial/intro.html`.

The classical ingredients are attributed, and the report supplies its own proofs of the finite interpolation and parity steps. No external research PDF was used as an unseen source for a figure or table.

## Novelty boundary

The report claims explicit extensions relative to the source statements actually inspected. It does not claim that real convolution, residue summation, divided differences, root-of-unity filtering, Bell polynomials, or Lucas–Kummer parity are new. It does not claim exhaustive worldwide novelty of every special-value identity. Full comparison with the uninspected incoming packages remains a stated future task.
