# The Lorentz degree in a thin ellipse and three ProveIt extensions

Start with **01_lorentz_ellipse/lorentz_ellipse.pdf**. Its main theorem answers a question of Tamás Erdélyi in the Journal of Approximation Theory (1991), page 197. For each positive even degree n and ellipse width 0 < ε ≤ 1, the smallest finite Lorentz degree of a real polynomial with every zero in the open ellipse of semiaxes 1 and ε is comparable to max(n/ε, 1/ε²), with absolute constants. The upper order is achieved by rational polynomials with simple roots. The paper includes exact values for one explicit counterexample family.

## Papers

| Directory | Result |
| --- | --- |
| 01_lorentz_ellipse | The two-parameter extremal law, the explicit Chebyshev counterexamples, and a computation of their exact representation degrees. |
| 02_positive_filters | The precise central multiplicity needed in a reflected angular band, and the large-order limit for each repeated pair throughout the wider band. |
| 03_padic_roots | A finite exponent-congruence test preserving the full deep-disk profile. In the open exponential disk the sharp root count is p² + floor((t−p−2)/2) for p+2 ≤ t ≤ 2p+1. |
| 04_cayley_walks | A classification of all minimum-outdegree periodic oriented Cayley graphs on finite abelian groups at prescribed spacing, with consequences for uniform mixing and perfect state transfer. |

## Relation to ProveIt

We used revision 41a284d6ef8eb16d783bfc685ab99cc6e1d28daa of VladimirReshetnikov/ProveIt. The lead question arose from the article's test for positive filters with reflected frequencies. In the variable z=(1−x)/(1+x), raising the permitted Lorentz degree multiplies the coefficient polynomial by 1+z. This is the same multiplier that adds a zero at the central frequency in the filter problem.

The other two branches continue the article's questions on p-adic sparse polynomials and on equality in the spectral bound for oriented Cayley graphs. Each paper cites its specific mathematical inputs. All four results are unconditional. The proofs and finite computations in this archive do not require a build of the vendored RH or Dirichlet GRH development. They have not been formalized in Lean.

## Reproduction

Each directory contains its own LaTeX source and all required local inputs. Run pdflatex twice on the paper's main .tex file, from its directory. The ellipse plot is included as a PDF, and figure.py can regenerate it using NumPy and Matplotlib.

The following commands run from the corresponding paper directory.

| Directory | Command | Check |
| --- | --- | --- |
| 01_lorentz_ellipse | python3 verify_ellipse.py | Recomputes exact least degrees using integer coefficient signs and checks the preceding degree. Compare with exact_degrees.txt. |
| 02_positive_filters | python3 check_filters.py | Reproduces filter-table.tex. The finite multiplicities are exact. The limiting slopes are rounded numerical solutions of the proved equation. |
| 03_padic_roots | python3 verify.py | Exhausts canonical supports at the listed small parameters and checks attainable counts with and without exponent compression. Compare with results.txt. |
| 03_padic_roots | python3 disk_roots.py 5 0,1,5,10,15,20,25 | Gives all attainable counts in the open disk for this prescribed support. Use --depth with a rational number for a closed disk of depth greater than 1/(p−1). |
| 04_cayley_walks | python3 check_graphs.py | Checks the classification on twelve host/conductor pairs using exact cyclotomic arithmetic. Requires SymPy. Compare with graph-output.txt. |
| 04_cayley_walks | python3 check_octadic_slices.py | Checks the conductor-eight local alternative on six finite groups. Compare with octadic-output.txt. |

The computations illustrate and check the proofs. The proofs of the infinite families are in the papers.
