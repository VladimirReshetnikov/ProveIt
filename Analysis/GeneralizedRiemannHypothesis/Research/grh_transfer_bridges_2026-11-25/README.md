# Beyond Dirichlet GRH

Research report prepared for Vladimir Reshetnikov, 25 November 2026.

## Main files

- report.pdf: complete report, proofs, source references and assessment.
- report.tex and sections/: all LaTeX source.
- checks/: exact standard-library Python certificates for the new arithmetic examples.
- evidence/: computed outputs, source identities, incoming inventory, and fresh prior replay logs.
- prior/: two unchanged ProveIt CM archives used and independently replayed in this analysis.
- formalization/dependency_plan.md: implementation plan and explicit verification boundaries.
- SHA256SUMS.txt: package file checksums.

## Results added in this analysis

1. Exact compatibility for extending local torsion characters globally, including prescribed splitting, class-group exponent costs and root-of-unity relations.
2. Over Q(sqrt(-23)), minimum conductor norm 151² = 22801 for a nontrivial anticyclotomic 3-power character trivial at decomposition groups above 3 and ramified only at split rational prime pairs. Exactly two minimizers, both order 3.
3. A sharp higher-depth, blockwise confluent criterion for rational independence of unbounded powers.
4. Exact least annihilator support seven for every alpha^(63t), with alpha of CM discriminant -87, and every beta^(182t), with beta of discriminant -152, for t >= 1.
5. A rank/completion-cost tradeoff extracted from the source's covolume theorem.

These are written mathematical proofs and exact certificates, not newly Lean-checked proofs. The finite-group and class-field ingredients are classical; no worldwide priority claim is made.

The global five-term singular-modulus classification is **prior work** in the included ProveIt archive. Its complete certificate suite was rerun. The two powered families above do not prove a six-term classification for the original, unpowered singular moduli.

## Reproduce

Run from this directory:

    python3 reproduce.py

The new checks need only the Python standard library. They use exact integers and finite fields. Their all-exponent conclusions follow from the written theorem, not from sampling exponent ranges.

To replay the previous CM archives too:

    python3 reproduce.py --include-prior

The prior packages also require their documented dependencies, including a C++17 compiler for the residue sieves. No network is required; the original ZIPs are included. The replay extracts them into a temporary directory and preserves their source.

Build the PDF:

    latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

The generated PDF was rendered and visually checked.

## Pinned sources

- lsernau/grh-lean: 72fead102f663d5c7a407964a13dc0cf9d977207
- VladimirReshetnikov/ProveIt: 48efe71a726dddc5a505534edaa4c0fd190416b9

The snapshot contained 41 incoming ZIP archives. We inventoried the corpus, read selected prior reports, and fully reran the two identified CM packages; this is not a mathematical certification of every claim in all 41 archives.

The upstream endpoints concern zeta and Dirichlet L-functions. We did not rerun the full upstream Lean build or kernel replay. No new nonabelian GRH, BSD, Vandiver, or general K-group vanishing theorem is claimed.
