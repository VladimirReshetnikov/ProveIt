# Beyond Dirichlet GRH

Read **report.pdf** for the full bookmarked report. The individual papers are also included as PDFs and compilable LaTeX sources. The four papers address different questions and can be read independently.

| Paper | What is proved | Principal input |
|---|---|---|
| cubic/ohara.pdf | Affirmative answers to O’Hara’s Questions A and B. The analogue with the same rational exclusion holds for all sextic fields with normal-closure group A₅ at primes ℓ ≥ 17. A descent lemma gives a version for every odd degree and for the A₄ sextic family. | Rasmussen–Tamagawa Prop. 7.5, McLeman–Rasmussen Thm. 3.1, O’Hara Lemma 5.1 and Prop. 5.2. The cubic result is unconditional. |
| heavenly/heavenly.pdf | Uniform Rasmussen–Tamagawa bounds in every dimension over the two specified sextic families. A necessary list of 29 primes for elliptic curves also applies to every cubic field. | Odd residue degrees in two sextic actions from the earlier ProveIt report, cyclotomic splitting under Dirichlet GRH, local inertia weights and a Frobenius trace sieve. |
| critical-line/critical-line.pdf | All-cutoff limits for paired sharp products, local estimates for individual products, and recovery of a modulus and quadratic twist from signed zero multiplicities. | Dirichlet GRH, the classical explicit formula, and the Mellin residues appearing inside the Lean argument. |
| progressions/syndetic.pdf | Construction of periodic sets with an exact prescribed spectrum of rational ratios for several geometric-progression shapes, with density and gap bounds. | The weighted, modular Behrend construction used inside the Lean proof. |

## Source snapshots and attribution

* [Readable Lean edition](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh), commit `72fead102f663d5c7a407964a13dc0cf9d977207`. The five top-level statements are in `grh/src/Main.lean`; definitions are in `Statements.lean` under that directory. For the analytic reduction see `New/Reduction/MainInequality.lean`, `New/Reduction/OneSidedBound.lean`, and `New/Reduction/Zeros/Criterion.lean`. The weighted progression lemma is in `New/Reduction/Data/Existence.lean`.
* [Andrew Sutherland’s independent verification record](https://math.mit.edu/~drew/shortgrh/) documents the statement comparison, axioms and kernel replays. We inspected the upstream declarations and that record. This archive contains downstream mathematical proofs and finite computational checks. It does not contain a new kernel replay or a Lean formalization of the downstream theorems.
* [ProveIt incoming reports](https://github.com/VladimirReshetnikov/ProveIt/tree/b65aa6229415bdb66d9ce52decc4e997793cd07d/docs/incoming), commit `b65aa6229415bdb66d9ce52decc4e997793cd07d`. The arithmetic paper explicitly uses the ramification argument and sextic permutation actions in `grh-arithmetic-transfers.zip/isogenies.tex`. The source of the range checker is attributed in that paper. Its upper endpoint here is 30,000,000,000,000.
* [O’Hara’s questions and lifting propositions](https://arxiv.org/abs/2609.35642v1), [Rasmussen–Tamagawa’s uniform bounds](https://arxiv.org/abs/1302.1477), and [McLeman–Rasmussen’s fixed-prime theorem](https://doi.org/10.1007/s40993-026-00757-8) are the three ingredients of the unconditional deduction. “Heavenly” means that the curve has good reduction away from the indicated rational prime and its mod-prime torsion field has prime-power degree over the corresponding cyclotomic base, with the same prime in both conditions.

## Reproducing the arithmetic

Run from this directory with Python 3 and a C++17 compiler. Keep Python assertions enabled. Each exact checker has a saved transcript in its own directory. The last command can run serially with the same answer if OpenMP is unavailable; omit the compiler’s OpenMP flag in that case.

```sh
python3 heavenly/check_heavenly.py
python3 heavenly/check_elliptic.py
python3 heavenly/check_split_trace.py
g++ -O3 -std=c++17 -fopenmp heavenly/cubic_tail.cpp -o /tmp/grh-cubic-tail
OMP_NUM_THREADS=6 /tmp/grh-cubic-tail
python3 critical-line/check_prime_jumps.py
python3 progressions/verify_syndetic.py
```

The three Python programs in `heavenly/` enumerate the permutation actions, derive the 29-prime necessary list, and independently check its ten candidates above 211 in the lower range. The C++ program exhausts the remaining finite interval. It prints zero surviving primes without a witness. The analytic inequality covers all integers above the program’s limit. A listed prime still needs a curve that realizes it. The calculation for bounded gaps checks one finite example. The proofs of the infinite statements are in the papers.

To reproduce the floating-point Euler product illustration, install NumPy, mpmath and Matplotlib, then run:

```sh
python3 critical-line/euler_example.py --output-dir critical-line
```

The CSV contains 130 cutoffs through ten million. All limiting constants in the theorem are given analytically as well as numerically. The figure illustrates convergence and plays no role in the proof.

## Rebuilding the PDFs

Use a LaTeX distribution with pdfLaTeX, Latin Modern, AMS packages, geometry, booktabs, float, microtype, xcolor and hyperref. The Euler-product figure is supplied. Run both LaTeX passes, then assemble the report using Python 3 with PyMuPDF installed.

```sh
for source in overview cubic/ohara heavenly/heavenly critical-line/critical-line progressions/syndetic
do
  (cd "$(dirname "$source")" && pdflatex -halt-on-error "$(basename "$source").tex" && pdflatex -halt-on-error "$(basename "$source").tex") || exit 1
done
python3 build_report.py
```

The SHA256SUMS file records the delivered sources, PDFs, scripts, data, and transcripts. To verify the extracted archive, run `sha256sum -c SHA256SUMS` in its top-level directory. Recompiled PDFs may have different hashes because TeX inserts build timestamps.
