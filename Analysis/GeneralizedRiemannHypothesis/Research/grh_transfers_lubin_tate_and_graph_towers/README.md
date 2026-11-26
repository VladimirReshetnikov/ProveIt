# Sharp local bounds from methods in the Lean proof of Dirichlet GRH

Open **report.pdf** to read the ten-page manuscript. The complete LaTeX source consists of report.tex, branches.tex, graphs.tex and discussion.tex.

The graph result gives the exact maximal spanning-tree valuation for four-step rank-two towers at every prime greater than eight. Its seven exceptional primes are 11, 23, 29, 47, 53, 83 and 149. The general bound is attained for an even step count m precisely at primes congruent to 1 modulo 2m. The interpolation result answers the multi-branch equality question for Lubin–Tate recovery modulo any uniformizer power. The last section quantifies a congruence obstruction for a proposed nonabelian zero test and gives the prime-sum bound still required.

## Reproduce the results

Run the following from this directory, using a standard TeX Live installation and Python 3.8 or later. The checkers use the Python standard library. Their corresponding recorded outputs are in checks/. The finite enumeration is small enough to repeat on an ordinary laptop.

```sh
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
python3 checks/check_graph.py
python3 checks/check_graph_independent.py
python3 checks/check_branch_precision.py
python3 checks/verify_jet_matrices.py
python3 checks/check_designs.py
```

| File | What it checks | Recorded output |
|---|---|---|
| check_graph.py | Normalized points on the genus-nine curve, exhaustive small-prime plane maxima, and a six-step integral Laplacian determinant | graph_checks.txt |
| check_graph_independent.py | All 62 small-prime curve counts by convolution and four-step cofactor valuations by modular elimination | graph_independent_output.txt |
| check_branch_precision.py | Pole orders by monic remainders, binomial equality conditions, and comparison with Laurent inverses of literal multiplicative branches | branch_check_output.txt |
| verify_jet_matrices.py | Sufficiency and componentwise necessity on explicit jet observation matrices | jet-matrix-output.txt |
| check_designs.py | Residue-ball minimax cutoffs across 6,128 finite designs and the complete second-precision formula on 231 profiles | design_checks.txt |

## Sources and scope

The file sources/lean_sources.json pins the readable upstream implementation, declarations, source lines, and Git blob identities. The details of independent upstream verification are published at https://math.mit.edu/~drew/shortgrh/. The full Lean build was not repeated for this report. The new mathematical arguments have not been formalized in Lean. The exact scripts reproduce the finite parts.

The incoming archive inventory is at ProveIt commit 1677488425e45c3df14149c804014133798136a5. The file sources/incoming_inventory.tsv records the 55 ZIP names and the scope of comparison. A consistent topic search across 370 TeX members is recorded in sources/incoming_tex_screen.tsv. The two questions answered here were posed in the Lubin–Tate and graph-tower packets cited in the manuscript. The nonabelian prime-sum criterion was already in the McNew density and GRH transfers packet. Publication priority is unverified.

SHA256SUMS lists the digests of the archive contents and can be checked with the following command.

```sh
sha256sum -c SHA256SUMS
```
