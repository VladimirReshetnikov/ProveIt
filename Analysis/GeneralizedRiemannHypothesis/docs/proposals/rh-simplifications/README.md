# Three simplifications of the theta-lift proof of RH

Open **rh-simplifications.pdf** for the complete research note. The three sections can be read independently after §1. Section 2 contains the stronger spanning theorem and its sharpness example. Section 3 gives finite interpolation on roots of unity. Section 4 gives the auxiliary-prime argument using the quadratic large sieve. Section 5 shows how the three results enter RH and Dirichlet GRH.

## Rebuild the PDF

Place the five TeX files in one directory and run the following command there with a standard TeX Live installation.

```sh
latexmk -pdf -halt-on-error rh-simplifications.tex
```

## Reproduce the finite checks

The test for ranks uses SymPy. The torsion, sieve, and source-anchor scripts use Python 3's standard library. From the directory containing this README, run the following commands.

```sh
python3 checks/check_spectral_spanning.py
python3 checks/check_torsion_grid.py
python3 checks/check_sieve.py
```

- The rank check uses exact rational matrices. It checks the trace identity, projected energy, gains in rank for ramified subspaces, and extremal parameter identities. The large extremal models use their exact orbit counts.
- The cyclotomic check computes normalized valuations from the orders of roots of unity. It checks both signs of an interpolation-factor valuation, the denominator bound on all 127 nonempty subsets of a seven-node sample for each of two primes, and 196 bad sets computed from products of linear factors.
- The sieve check compares the two coefficient convolutions and computes the square-pair sum in two ways. It also checks rational choices of the exponents used in the proof.

The scripts test finite calculations. The uniform mathematical arguments appear in the paper.

## Check the standalone Lean lemmas

The file `checks/RankRecurrence.lean` was checked with Lean 4.32.0 using only `Std`. From the directory containing this README, run

```sh
lean checks/RankRecurrence.lean
```

This verifies the scalar recurrence over linearly ordered commutative rings and the exact rational identity that exhibits the limiting constant 19. The two axiom reports list `propext`, `Classical.choice`, and `Quot.sound`. The matrix argument, interpolation theorem, and analytic replacement are proved in the paper.

## Compare with the source

The companion table `checks/source-anchors.tsv` contains immutable GitHub links, declaration names, line numbers, and Git blob hashes. The linked ProveIt snapshot uses the readable package from upstream commit `72fead102f663d5c7a407964a13dc0cf9d977207`. To verify the source table, run

```sh
git clone https://github.com/lsernau/grh-lean.git grh-lean
git -C grh-lean checkout --detach 72fead102f663d5c7a407964a13dc0cf9d977207
python3 checks/check_source_anchors.py grh-lean/grh
```

The source comparison covered 35 declarations in 17 blobs and the pinned Lean and Mathlib versions. The [independent verification record](https://math.mit.edu/~drew/shortgrh/) applies to that upstream proof. Integration of the three replacements into the original Lean 4.35.0 project is a separate formalization task.
