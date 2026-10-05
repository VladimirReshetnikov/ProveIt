# Batch 101 computational relevance triage

This bounded triage identifies no new Turing-complete substrate, universal-machine simulation, or paid ordinary-integer Diophantine compiler in the declared read scope. The thirteen reports concern counting sequences, generating functions, exact recurrences, asymptotic expansions, and inversion. They are low priority for the current search for a cheaper complete universal integer source. This is a relevance assessment, not mathematical certification of their claims.

The immutable snapshot is `f7c612c72f8729f786cbba6bc3fd20f12e2110a5`, with parent `342a4583efa9c8a4f819c2796259aca176e0f42f`. I read its complete commit message and inventoried all 167 changed paths: 154 additions and 13 deleted incoming ZIPs. The archives were read from the parent snapshot. Their full ZIP bytes are SHA256-pinned in the companion receipt; the central-directory inventory records all 251 non-directory member names, sizes, and CRC32 values. This is not a claim that every member's content or delivered checksum manifest was independently authenticated.

## Exact textual scope

The receipt records thirty read spans totaling 1,166 lines, with full member and individual span hashes: thirteen guide openings, thirteen principal abstracts or scope openings, and four additional interfaces. Line numbers below are one-based and inclusive. Every archive is under `docs/incoming/`; the table gives its exact basename and exact internal member paths. A read ending at line 60 or 85 is a bounded opening unless the receipt says otherwise.

| Archive | Members and lines actually read | Topic identified |
| --- | --- | --- |
| `A196275_Exact_Asymptotics_and_Inversion_Source.zip` | `a196275/README.md` 1–37; `a196275/source/permutomino_asymptotics.tex` 38–40; `a196275/source/permutomino_asymptotics.tex` 339–352 | Permutomino generating function, analytic coefficient asymptotics, and inversion |
| `A215561_Fixed_Alphabet_Asymptotics.zip` | `A215561_Fixed_Alphabet_Asymptotics/README.md` 1–50; `A215561_Fixed_Alphabet_Asymptotics/article.tex` 19–31 | Fixed-alphabet ballot-word asymptotics |
| `A215570_Balanced_Ballot_Asymptotics.zip` | `A215570_Balanced_Ballot_Asymptotics/README.md` 1–43; `A215570_Balanced_Ballot_Asymptotics/article.tex` 18–29 | Five-letter weighted excursions and asymptotic coefficients |
| `A330266_Uniform_Tail_Repair.zip` | `A330266_Uniform_Tail_Repair/README.md` 1–50; `A330266_Uniform_Tail_Repair/repair_note.tex` 1–85 | Uniform factorial-moment tail repair for balanced Smirnov words |
| `Canonical_Vincular_Exponential_Sectors_Source.zip` | `Canonical_Vincular_Exponential_Sectors_Source/README.md` 1–47; `Canonical_Vincular_Exponential_Sectors_Source/article.tex` 30–32 | Analytic exponential sectors of vincular-pattern avoidance |
| `Exact_Vincular_Avoidance_Asymptotics_Source.zip` | `Exact_Vincular_Avoidance_Asymptotics_Source/README.md` 1–45; `Exact_Vincular_Avoidance_Asymptotics_Source/article.tex` 19–37 | Exact EGF, counting recurrence, and asymptotic coefficient algorithm |
| `Fixed_Displacement_Permutation_Asymptotics_Source.zip` | `Fixed_Displacement_Permutation_Asymptotics/README.md` 1–55; `Fixed_Displacement_Permutation_Asymptotics/article.tex` 20–34; `Fixed_Displacement_Permutation_Asymptotics/article.tex` 290–320 | Forbidden fixed displacements and path-length asymptotics |
| `L_Convex_Polyomino_Area_Asymptotics_Source.zip` | `L_Convex_Polyomino_Area_Asymptotics/README.md` 1–58; `L_Convex_Polyomino_Area_Asymptotics/article.tex` 30–32 | Area enumeration and asymptotics for L-convex polyominoes |
| `ProveIt_Fixed_Height_Shifted_Strips_Asymptotics.zip` | `README.md` 1–45; `article.tex` 19–21 | Fixed-height shifted-array asymptotics |
| `ProveIt_Shifted_Strips_Rational_Diagonals_and_Transcendence.zip` | `README.txt` 1–60; `article.tex` 27–29; `article.tex` 138–208 | Finite event sums and rational-diagonal closure |
| `Report231.zip` | `Report231/README.md` 1–60; `Report231/sections/01_scope.tex` 1–85 | Height-four shifted arrays, finite sum, and second-order recurrence |
| `Report232.zip` | `Report232/README.md` 1–60; `Report232/report.tex` 44–68; `Report232/report.tex` 1467–1492 | Joint reciprocal colored-gap constraints in random permutations |
| `Report233.zip` | `Report233/README.md` 1–60; `Report233/sections/01_scope.tex` 1–85 | Height-five shifted arrays, nested sum, and third-order recurrence |

I also lexically scanned 41 TeX members, excluding filenames ending `_standalone.tex`, for `Turing|Diophant|universal|undecid|halting|NP-hard|complexity|algorithm` case-insensitively. The receipt preserves the matching lines. A lexical scan is not a full read of those files.

## Computational boundaries

The closest limited lead is the rational-diagonal report's `article.tex` lines 138–208. At fixed height m it writes counting functions using finitely many event patterns, at most m² pre-event summation coordinates, finite summation endpoints, binomial products, and affine indicator guards. It invokes binomial-sum closure to obtain rational-diagonal/D-finite representations. The same passage expressly declines a small-variable or small-recurrence conclusion. A bound on summation coordinates is not a paid arithmetic-operation count or an existential positive-integer polynomial with a demonstrated universal interpretation. Its closure theorem and full proof have not been audited here.

The fixed-displacement report's “path-length universality” concerns shared asymptotic coefficients for unions of long directed paths with fixed component counts. It is not Turing universality. Likewise, differential algebraicity, non-D-finiteness or non-P-recursiveness of a counting sequence does not itself supply a universal computational substrate. The polyomino report's abstract and guide concern enumeration of a specified class, not a universal tiling or machine simulation.

The A196275 coefficient procedure is finite at a requested asymptotic order; the selected Report232 endpoint explicitly separates finite verification from proving an unknown asymptotic onset and leaves extraction of practical constants/onsets to further work. Neither selected interface gives the ordinary-input, unbounded-history positive-zero equivalence or fully charged integer gates needed by the active compiler problem. No new concrete mathematical defect is asserted on this limited reading.

## Placement and audit limits

Only two placements were checked byte for byte: the new A196275 host's `README.md` equals `a196275/README.md`, and its `article.tex` equals `a196275/source/permutomino_asymptotics_standalone.tex`. The host is under `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a196275-column-convex-permutominoes/`. The modular `permutomino_asymptotics.tex` supplied the abstract/interface spans above; it is not asserted to equal the standalone host article. The receipt pins both verified postimages. This does not authenticate all 154 additions or certify their normalization.

No supplied program, helper, builder, source array, or archived code was executed or imported. Only fresh read-only metadata code ran. No PDF, complete main proof, external literature, delivered checksum manifest, or all-member-content audit was performed; claims in the commit message about correctness are not adopted as independent review conclusions. The repository and Git state were not mutated.

Companion receipt: `/tmp/triage_batch101_f7c612c72_pascal.json`, SHA256 `0208b33e513f917820e934694a55851b1e673c66c6b591648a74660a4f1890cd`.
