# Integration plan

No remote repository file has been modified. This package is prepared for manual review and integration.

## Suggested destination

Copy the package into a new directory such as:

`Analysis/Polylogarithms/docs/research/conductor-descent-2026-10-09/`

This is a proposed new path, not a claim that the directory already exists. The article is self-contained and may remain a separate research note. A smaller manuscript insertion is supplied in `integration/chapter08_distribution_rank.tex`.

## Manuscript insertion

At the pinned Chapter 8 source, replace the observation labeled `tower:thm:rank` **and its immediately following paragraph** with the insertion. The insertion retains the label, uses the manuscript's existing theorem/proof environments, and requires no new packages or global macros. It states its own matrix convention and gives a complete conductor-basis proof.

Do not leave the old label in place as well, or LaTeX will report a duplicate label. The insertion can be pasted directly; an `input` directive is also suitable after choosing a stable relative path.

Update Chapter 10's distribution-rank research question to cite the theorem. Keep the distinction between the complete presentation proved here and the unavailable historical row lists.

The character-trace material fits naturally into Chapter 2 (cyclotomic transforms) or Chapter 8 (spectral derivatives). It is supplied in the standalone article rather than automatically spliced into the consolidated book. The S4 finite-law obstruction belongs near `gauss:eq:S4-closed` or in Chapter 10's discussion of exact relation matrices.

## Verification before merging

Run `make exact`, `make numeric`, and `make pdf` in the package directory. Then compile the full manuscript with the insertion and check for duplicate labels, bibliography-key conflicts and notation collisions. This package tests the insertion in a small standalone harness, but does not claim to have rebuilt the complete remote manuscript.

The identity catalogue distinguishes proven identities from the retained S4 candidate. Keep that status field if importing identities into another store. Certificate matrices concern formal laws; importing them must not upgrade a numerical-independence claim.

## Authorship and provenance

The note records preparation for Vladimir Reshetnikov's programme with OpenAI ChatGPT mathematical and computational assistance. Adjust editorial authorship according to the repository's conventions. Classical identities and universal-distribution antecedents are attributed in the article bibliography. Do not describe the polynomial rank phenomenon as newly discovered in the literature without a separate priority review.
