# Computational companion for Report 243

The computations are finite implementation checks and explicit examples. The article, rather than numerical fitting or prefix extrapolation, proves the asymptotic results.

## Reproduction

Python 3.11 or newer and its standard library suffice. From the article package root, run:

    python -B -X int_max_str_digits=640 code/verify_all.py --output-dir /tmp/report243-check-new

The output directory must not exist, its parent must already exist, and it must lie outside the source package. The runner executes each verification script normally and with `-O`, requires byte-identical JSON, compares it with the supplied reference receipts, and regenerates all five CSV files. It writes `reproduction_receipt.json` with the output hashes. A second run needs a different output directory. All commands include `-B` and the explicit 640-digit decimal cap; imported shared code also sets that cap. No network or third-party Python package is required.

The individual scripts accept `--output NEW_EXTERNAL_FILE`; without that option they print deterministic JSON. `exact_counts.py` has bounded `--raw-n`, `--recurrence-n`, and `--triple-n` options. `upper_bound.py` and `positive_rows.py` have a bounded `--max-n` option. Defaults run the full supplied checks. `guard_tests.py` takes only the optional output path. `verify_all.py --no-reference-comparison` regenerates receipts into a new external directory without changing any supplied reference.

## What is checked

- `exact_counts.py`: exact ordinary 100 and 110 counts through n=15 from Conway et al. (2022), Sections 2.3 and 2.4, respectively. The implementation follows the actual sections; the abstract reverses their recurrence-efficiency labels. It compares with the supplied short A202059/A202060 prefixes. Independently, it enumerates all 37,883 ordinary ascent sequences with lengths 0 through 9 and tests every index triple literally, checking both individual classes, the 000/100 subclass, and the common 000/100/110 class. Independent literal extension gives the common-class prefix through n=11. Fast detectors are cross-checked against the literal tests, and are used only where larger example words make cubic enumeration inappropriate.
- `upper_bound.py`: 24,363 class-word encodings, 99,665 run-candidate checks, and 15,276 observed skeletons. Every encoding is decoded from marked positions/labels, run lengths, and conditional candidate ranks. The checks include the exact prefix ascent count, run ceiling, unseen count, unfinished-label set and budget, refined candidate cardinality, skeleton branching, the product/Vandermonde/triangular comparison, and the finite sum bound. An additional 5,050 cases verify the shifted triangular identity through table size 100.
- `positive_rows.py`: all 10,420 triangular weak-composition arrays for 2<=n<=9 and 1<=r<n. Each eligible array is repaired, mapped to a 000/100-avoiding ordinary word, and recovered from its word plus positive row lengths. Doubled-seed words and their inverse are checked against literal 000/100/110 tests. Fresh-record padding checks legality and preservation of all applicable avoidance classes.
- The three fiber estimates are tested separately: original-array to repaired-array fibers (bound 2^r), repaired-array to undecorated-word fibers (bound binom(p-1,r-1)), and distinct pre-padding words to padded words (bound Q+1). The maximum observed fibers are 21, 16, and 4, respectively; the common padding maximum is also 4. Thus these tests include actual collisions, rather than checking only injective examples. Both finite lower comparisons hold for every enumerated parameter pair.
- The small exhaustive array range has Q>=r, so its retained-half check alone would not exercise a genuine cutoff. An independent exact row-sum dynamic program computes entire empty-row histograms for (r,q,Q)=(8,30,5),(12,90,4),(16,128,5). Each has Q<r and a nonzero rejected tail. In each case the histogram totals the triangular count; its expectation agrees exactly with the sum of the row-empty marginal counts, obeys the expectation bound, and retains at least half the arrays. The single-row zero-empty edge case is also checked.
- All-length integer examples are supplied at N=100,250,1000,10000 for both the 000/100 and common constructions. The formulas select dimensions using 60-digit Decimal logarithms; all following counts, repair budgets and slack inequalities are exact integer calculations. Actual arrays, repaired words, doubled words where applicable, inverse maps and padding to exactly N are checked through N=1000. The N=10000 examples check parameter and finite-count inequalities only. These are illustrations, not a numerical proof of eventual all-length behavior.
- `guard_tests.py`: 335 passing rejection and boundary checks, including input types, finite cutoffs, work budgets, malformed encodings/rows/ranks, empty-word and one-row edges, arbitrary-subsequence detection, the entering-ascent convention, decimal input/output caps, subprocess flags under hostile ambient settings, exclusive file creation, source-directory protection and symlink-path rejection. Source inspection requires explicit validation rather than `assert`. These filesystem guards do not claim to be a sandbox against hostile concurrent filesystem changes.

## Explicit stars-and-bars map

A row a=(a_0,...,a_(w-1)) of total ell is written as ell stars separated by w-1 bars. The universe has ell+w-1 positions indexed from zero. Row component a_i contributes the consecutive selected positions

    a_0+...+a_(i-1)+i, ..., a_0+...+a_i+i-1.

These ell positions are the ranks selected from the sorted candidate pool. The inverse scans all ell+w-1 positions and counts selected positions before, between, and after the missing bar positions. `stars_to_ranks` and `ranks_to_stars` implement these two maps. Both directions are exhaustively checked over all widths 1 through 6 and totals 0 through 6, for 3,430 round trips. `recover_rows` additionally reconstructs the actual candidate pools from the decorated word, so testing is not limited to an abstract stars-and-bars identity.

## Outputs and large integers

Reference JSON files: `count_receipt.json`, `upper_bound_receipt.json`, `positive_rows_receipt.json`, `guard_receipt.json`, `reproduction_receipt.json`.

CSV views: `counts.csv`, `upper_bounds.csv`, `positive_rows.csv`, `markov.csv`, `all_lengths.csv`.

Counts larger than 1,800 bits are never converted to decimal. Their receipts give bit length, byte length, and SHA-256 of the minimal unsigned big-endian byte representation, with zero represented by one zero byte. Smaller counts may additionally include their exact decimal value. The integer decimal-conversion limit is never disabled or increased above 640. Word and encoding hashes use their documented deterministic tuple representations of bounded small labels. Receipt hashes do not establish the mathematics; they detect changes in the supplied finite computations.

## Source and scope

The recurrence source is Conway, Conway, Elvey Price and Guttmann, *Pattern-Avoiding Ascent Sequences of Length 3*, Electronic Journal of Combinatorics 29(4) (2022), P4.25, https://doi.org/10.37236/11266. The short common-class reference prefix is attributed in `source_prefixes.json` to https://doi.org/10.37236/12720, Table 2, Class 36, with the empty-word term added. Exact triangular enumeration and its self-modified interpretation are prior results, cited in the article. No third-party paper or private source-review material is bundled in the code directory.
