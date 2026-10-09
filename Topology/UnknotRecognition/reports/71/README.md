# Cycle-Envelope Kernels for Disk Completion

A research continuation for ProveIt's unknot-recognition programme, 9 October 2026.

**Main result.** If candidate partitions refine `sigma`, future cap partitions refine
`rho`, and their arc-incidence multigraph is connected, its cycle rank
`lambda = r + 1 - blocks(sigma) - blocks(rho)` gives exact binary disk-completion
rank `2^lambda`, with grade-j rank `binomial(lambda,j)`. The bounds are sharp for
every connected envelope, including representative-subset methods.

The article replaces the earlier sufficient small-arc-width condition by a
small-two-sided-cycle-overlap condition. A supplied explicit layered patch grammar
can be searched in `poly(I,B) * 2^(3*lambda_max)` bit time, with safe envelopes
computed in polynomial time. This is not a proof of a general quasi-polynomial
unknot recognizer: a source-complete low-cycle geometric producer is still needed.

## Start here

Read **article.pdf** for the complete proofs and scope. **article.tex** is its
main source; all included TeX table fragments are in `results/`.

```sh
make test        # 42 test methods
make verify      # independent check of the supplied examples
make audit       # larger deterministic finite audit
make example     # regenerate source/certificate/mesh examples
make benchmark   # rerun five-repeat timings; replaces raw timing JSON
make tables      # generate tables from retained JSON, without rerunning timings
make pdf         # two pdflatex passes; does not rerun benchmarks
```

Python code uses the standard library and syntax compatible with Python 3.10+.
Executed environment: CPython 3.13.5. PDF construction requires a standard LaTeX
installation with the packages named in the preamble, including TikZ and cleveref.

A complete abstract search:

```sh
python3 code/grammar.py examples/grammar.json --mode cycle \
  --seconds 30 --output results/new_run.json
```

The other modes are `exact` and `root`. Every mode uses the same safe viability
filter and transition source. The time cap is a resource limit, not a completion
promise. `RESOURCE_LIMIT` is never evidence of infeasibility.

## What is included

`code/envelope_kernel.py` contains the cycle representation, weighted reducer,
source-bound expansions, and unrestricted-root comparator.
`code/checker.py` uses a different nullspace basis, direct minors, whole-graph
envelope construction, and BFS transitions to verify pruning and full searches.
`code/surface_replay.py` constructs and checks literal triangulated surfaces.
`code/grammar.py` implements complete search in the supplied finite language.
The source fixtures, all tests, retained JSON results, CSV, example certificates,
source audit, claim ledger, proof audit, and integration gate are included.

The finite audit verifies 633,531 direct matrix entries over 3,162 envelope
matrices, 1,000 weighted families with 16,904 cap/sector queries, 600 three-way
grammar comparisons, 1,000 random surface pairs, and all 1,412 assignments in 40
small grammars. It also checks a sharp 256-arc example with cycle rank three and
eight representatives.

## Scope boundaries

`FOUND_ABSTRACT_DISK` and `NO_DISK_IN_GRAMMAR` concern only the explicitly supplied
patch language. They are not knot verdicts. Every label is one separated actual
boundary arc, not a compressed multiplicity. A geometric adapter must establish
embeddedness, fixed-type substitution, source binding, complete rule coverage,
and certified essential boundary. Generic two-bit sectors do not supply those
facts by themselves.

The retained measurements are abstract-grammar benchmarks, not maintained
recognizer benchmarks. On three restricted examples, peak tables fall from 16–29
unrestricted representatives to four and median root/cycle search ratios are
1.49–3.04. A single-cap direct scan is faster than either preprocessing route.
All input-list and timing-scope costs are reported in the article and raw JSON.

Reviewed repository revision: `66098968e88bba797143ac1bf7ad0ac4c5f697df`.
No native checkout tests or runtime integration were executed. No remote files
were changed, and no report number is assigned here. Consult `docs/INTEGRATION.md`
before placing the code on a production path. Original delivered material is
provided under MIT-0; upstream and third-party sources retain their own terms.
