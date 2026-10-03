# Approved one-tail/HPP pruning criterion: scope and source audit

## Conclusion

The criterion is already independently approved for **every finite loopless directed relation**, with no transitivity or degree restriction. In particular, it applies to arbitrary directed seven-vertex relations built from a five-core and two sinks. It allows physical overlap p ∈ Q and arbitrary independent nonnegative role activities. Its conclusion is real stability of the signed physical monomer polynomial, negative-real-rootedness of the support polynomial, and rank-ULC normalized at its actual surviving degree.

The approval is a conditional structural theorem: the explicitly constructed side matroid must have HPP. Every new pruned five-core case still requires an independently verified cover, side-matroid construction, and HPP witness. Neither membership in the old preorder catalog nor transitivity is needed; conversely, approval of the old catalog's 27 or six applications does not automatically approve a new graph's side presentation.

## Exact approved version

The following four files are byte-identical, with SHA256

    ce2448516000741395474765aa780bf2767f4dea785c554fc4d467fb18371159

- `../weighted-preorder-gamma/ONE_TAIL_HPP_ROLE_COVER.md`
- `../independent-role-degree-three-result/proofs/ONE_TAIL_HPP_ROLE_COVER.md`
- `../weighted-nontotal7-hybrid-independent-audit/dependencies/one_tail_hpp_side/source_theorem.md`
- `../weighted-nine-side-matroid-independent-audit/criterion_theorem.md`

The old “proposed/awaiting approval” header is historical. The decisive explicit approval is

    ../weighted-nontotal7-hybrid-independent-audit/dependencies/one_tail_hpp_side/approval_receipt.json

Its scope begins with any finite loopless directed relation and pins the theorem hash above. The accompanying `AUDIT.md` expressly reiterates arbitrary directed relations, arbitrary head-cover size, physical overlap, nonnegative roles, and actual-degree normalization. The same receipt is copied as `../weighted-nine-side-matroid-independent-audit/criterion_approval.json`.

The final delivered article `../independent-role-degree-three-result/independent-role-degree-three.tex`, section “Half-plane-property side matroids and the final cases”, states and proves the general criterion under theorem label `thm:oneside`. Its opening sentence expressly says that the criterion works in every degree and without transitivity. The article's `audit/math-approval.json` approves its complete retained ordinary proof, side substitution, true parallel classes, pendant recurrence, physical merge, and published-input restrictions. The final release README explains that some provenance files retain historical draft-status wording. The article's *global* theorem remains about preorders, but that does not narrow this separately stated local criterion.

## What a valid new pruning record must prove

1. Store the original seven-vertex directed row masks and whether all arcs have been reversed. Check the working relation exactly; reversal exchanges tail and head activities.
2. Store p and Q and verify every working arc i → j satisfies i = p or j ∈ Q. An economical choice is the union of heads reached by tails other than p; no minimality is required by the theorem.
3. Construct the rank-|Q| transversal side presentation using one ground element for **every** physical tail, whose neighbors are N(i)∩Q, plus one distinct private dummy with neighborhood {j} for each j ∈ Q. In particular the distinguished tail p itself is included. The private dummies guarantee the claimed rank.
4. Count bases as feasible ground-element subsets once, not once per matching. Independently recount the complete basis set by Boolean matching or Hall feasibility.
5. Simplify only true loops and parallel classes. Empty neighborhoods are loops. Singleton-neighborhood tails are parallel to the dummy at that center. Repeated neighborhoods of size two or more remain separate elements. Restore a parallel class by summing its variables; do not identify repeated multi-neighbor columns.
6. Supply an exact HPP justification for the side or its simplification. If using a published positive fingerprint, store an explicit element permutation and check the entire basis set after mapping, not only rank, basis count, or another invariant. Dualizing a nine-element rank-five side for lookup in the rank-four list is valid.
7. An unsuccessful sufficient classification/lookup is **unknown**, not a proof of HPP and not automatically a counterexample. Leave that graph in the certificate domain unless a different complete witness succeeds.

The ordinary stable-side proof, including closure at zero activities, is the approved dependency. New finite mapping checks prove the new application hypotheses; they do not have to re-prove the general criterion.

## Primary classification and databank checks

Freshly checked primary sources:

- Kummer–Sert, *Matroids on Eight Elements with the Half-plane Property and Related Concepts*, **arXiv:2111.09610v4, 24 October 2023**, section 5, printed pp. 11–12, especially Theorem 5.2; section 6, printed pp. 17–18: https://arxiv.org/pdf/2111.09610v4
- Kummer–Sert supplementary databank, **Zenodo record 6108027, version v2**, DOI **10.5281/zenodo.6108027**: https://zenodo.org/records/6108027

The small classification has five rank-three seven-element exceptions and their rank-four duals. The eight-element sufficient test requires all one-element deletions and contractions to have HPP and then either rank different from four or failure of sparse paving. It does not approve an undecided rank-four sparse-paving side.

For nine elements, only the proved-positive file `n9r4Hpp.txt` is accepted. The paper distinguishes its 4,125 rational-Gram-certified positives from numerical candidates and unresolved entries. The official record's MD5 is `c73d80267112a960df5485f159ab56e0`; it matches the local approved data. Local SHA256 is

    a3c7a6eaebe02ef50998710282542be2751b218a6713853cdd2eecadbe1f1f86

The file is at `../weighted-nine-side-matroid-independent-audit/n9r4Hpp.txt`; I recounted 4,125 lines, each with 126 symbols in {'*','0'}. The precise approved application receipt is `../weighted-nine-side-matroid-independent-audit/approval_receipt.json`, and its source pins/encoding details are in `primary-source-check.json`. The file's ordering is increasing colex order on four-subsets, equivalently increasing subset bit masks; `*` denotes a basis. The earlier independent source audit verified this against Definition 0.1 and the example in the publisher's `Description.pdf`. A fresh fetch of that PDF failed here, but the official databank and official Macaulay2 encoding source were accessible: https://zenodo.org/records/6108027/files/codeDataBase8.m2?download=1

This uses published positive membership as an external mathematical input. It does not rerun the original authors' Gram-certificate production and is not a complete classification of nine-element HPP matroids.

## Audit boundary

This scope/source audit approves using the already proved criterion when a new exact witness verifies its hypotheses. It does **not** yet approve any new five-core pruning record, and does not alter the all-certificate checker or any frozen dependency package. A hybrid final release would need a complete, disjoint ledger covering all 9,608 core classes by either independently checked structural witnesses or exact polynomial certificates.
