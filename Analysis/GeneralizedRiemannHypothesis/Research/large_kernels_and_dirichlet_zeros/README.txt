LARGE PRINCIPAL KERNELS AND DIRICHLET ZERO MULTIPLICITIES
26 November 2026

rare-kernels.pdf and rare-kernels.tex
  The probability of a large principal kernel.
  Theorem 1 gives the asymptotic probability, conditional uniqueness, and the
  distribution of the exceptional index set when the distance to saturation
  grows. Equation (2) answers the order-n correction question in the preceding
  matrix paper. Theorem 2 handles both parities at saturation. Section 6 gives
  an exact enumeration in every even dimension.

prime-progressions.pdf and prime-progressions.tex
  How many arithmetic progressions resolve a Dirichlet zero?
  Theorem 2 gives two-sided bounds for the smallest separation between
  normalized progression residues of bounded multiplicity vectors. Corollary 3
  gives the optimal number of progressions for a prescribed precision scale.
  The paper gives explicit near-collisions and a sampling design modulo 11.

Rebuilding the papers
  Each .tex file is standalone. With a standard TeX Live installation, run
    latexmk -pdf rare-kernels.tex
    latexmk -pdf prime-progressions.tex

Checking the examples
  From this folder, run Python 3.10 or later with assertions enabled.
    python3 check_orthogonal.py
    python3 check_progressions.py
  Each script uses the Python standard library. The .txt files with the same
  stems contain their expected standard output. The checks use exact integer,
  rational, binary-field, and cyclotomic computations. The general theorems
  have written proofs in the papers.

Source scope
  grh-lean revision 72fead102f663d5c7a407964a13dc0cf9d977207
  ProveIt revision 4d7990202f9f106b2ffe8c209f073ad01d5e1987
  The main matrix paper follows the finite-group compression method and the
  line of work prompted by Vaas's question. Its mathematical proof uses finite
  geometry. The arithmetic paper uses the grouped residue formula to recover
  the multiplicities that occur at a specified point. Dirichlet GRH places
  the relevant nontrivial zeros on the critical line. The papers include
  detailed source references. The new proofs have no Lean formalization.

Previous matrix paper consulted for the distinction from the typical threshold:
  The largest principal kernel of a random binary orthogonal matrix,
  in orthogonal_nullity_and_prime_products.zip
  Archive SHA-256 2f84a915797bae4d9977a812daaf83275fd9deb1f168a32f5b1e522a11a39409.
