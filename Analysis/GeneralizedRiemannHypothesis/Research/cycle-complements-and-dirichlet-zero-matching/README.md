# Cycle complements and Dirichlet zero matching

Research manuscripts and exact finite checks, 27 November 2026.

## Two starting points

**For the conjecture, open `01-cycle-complements/odd_cycles.pdf`.** Sections 1–2 give a proof of Davis and Kohl's Conjecture 3.15 (preprint numbering). The Ehrhart numerator of the stable set polytope of the complement of an odd cycle of length 2m+1 equals its perfectly matchable set polynomial plus exactly one term, of degree m+1. Section 3 shows how the first discrepant coefficient recovers the number of shortest odd cycles in any triangle-free nonbipartite graph. The cycle numerator is real-rooted precisely for even cycles and the two odd cycles of lengths 5 and 7, among lengths at least 4.

**For the arithmetic result, open `02-zero-transport/zero_transport.pdf`.** Pair zeros of two distinct primitive Dirichlet characters by their ordinates in (T,2T], counting multiplicity. Moving a point costs its displacement and omitting a point costs λ per occurrence. For 0 < λ ≤ 1 and λ log T tending to infinity, the minimum cost is asymptotic to (√2 / π^(3/2)) T √log(λ log T). For products of equal degree, the Euclidean norm of the difference of the primitive multiplicity vectors replaces √2. The paper also gives separate formulas for matching the entire smaller list at equal and unequal product conductors.

## Companion results

| Directory | Manuscript | Main result |
| --- | --- | --- |
| 03-hard-distance-matching | `matching.pdf` | A cap of K/log T on every displacement permits matching all but a vanishing fraction precisely when K tends to infinity. A fixed cap leaves a positive fraction unmatched on each side. |
| 04-graph-gamma-vectors | `face_realizations.pdf` | A simplicial complex realizes the Ehrhart gamma vector of the symmetric edge polytope of every graph suspension. Further hypotheses give balanced or flag realizations. The paper specifies the resulting instances of the Nevo–Petersen conjectures. |
| 05-padic-root-counts | `paper.pdf` | The sharp geometric root count in v_p(x−1) > 1/(p−1) for at most t monomials is p²+⌊(t−p−2)/2⌋ for p+2 ≤ t ≤ 2p+1. The maxima have simple-root witnesses. A determinant formula handles each fixed support at all depths above the threshold. |

## Repository and published inputs

The repository snapshot for this investigation is [ProveIt, commit cc919c585f90be8e0fba7a1b90c70afdea39998e](https://github.com/VladimirReshetnikov/ProveIt/tree/cc919c585f90be8e0fba7a1b90c70afdea39998e/Analysis/GeneralizedRiemannHypothesis). The three starting points in its article are the section on recovering characters and zeros, the section on graph towers and Ehrhart polynomials, and the section on factorial-weighted moments for local root counts. The last manuscript also identifies the two repository supplements it extends.

The named conjecture and its bipartite predecessor appear in [Davis and Kohl, Lemma 3.11 and Conjecture 3.15](https://arxiv.org/abs/2207.14759). The main published analytic ingredients are estimates on the arguments of Dirichlet L-functions, including the [Bombieri–Perelli prime approximation](https://doi.org/10.4064/aa-83-3-271-281). Each manuscript supplies its own definitions, proof, sources and range of validity.

The graph results and p-adic results are unconditional. The two Dirichlet manuscripts count imaginary parts of all nontrivial zeros in the strip. Under Dirichlet GRH the same distances describe the zeros as points in the complex plane. Verification of the repository's upstream RH/GRH proof is outside this investigation. The manuscripts are research drafts. The literature search did not locate a prior proof of the cycle-complement conjecture or of the stated transport asymptotic. Mathematical priority and independent peer review remain open.

## Reproduce the checks

Each directory contains the PDF, its complete LaTeX source, a Python verifier and its recorded standard output. All five verifiers use the Python 3 standard library. Run the command from the corresponding directory.

| Directory | Verify | Compare with |
| --- | --- | --- |
| 01-cycle-complements | `python3 verify_cycles.py` | `cycle_checks.txt` |
| 02-zero-transport | `python3 check_transport.py` | `checks.txt` |
| 03-hard-distance-matching | `python3 check_matching.py` | `check_matching.txt` |
| 04-graph-gamma-vectors | `python3 verify_faces.py` | `face_checks.txt` |
| 05-padic-root-counts | `python3 verify.py` | `checks.txt` |

The graph scripts enumerate small graphs or lattice points directly. The two transport scripts check finite matching and flow inequalities, including repeated points. The p-adic script checks residue ranks, Newton indices and squarefree witnesses using exact arithmetic. The asymptotic and all-size statements are established by the mathematical arguments in the manuscripts.

To rebuild a PDF, run pdfLaTeX twice on its source in the same directory. For the cycle manuscript, the commands are

```sh
cd 01-cycle-complements
pdflatex -halt-on-error odd_cycles.tex
pdflatex -halt-on-error odd_cycles.tex
```

A standard TeX Live installation with the packages listed in the source preambles suffices. Bibliographies are embedded.
