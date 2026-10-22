# Reproducing the finite checks

Use Python 3.10 or newer. The scripts use only the standard library and require
no network access. From the bundle directory, run:

```sh
python3 -B code/verify_all.py --output verification_receipt.json
```

The wrapper emits one JSON receipt and returns exit status zero only on `PASS`.
It rebuilds all generated files in a temporary directory, then compares their
parsed JSON exactly with the delivered files. Without `--output` it leaves the
bundle unchanged. It can also be invoked by absolute path from another working
directory. `--root` selects another complete copy of the bundle.

The default run performs all the following checks:

| Check | Executable evidence |
|---|---|
| Source identity | SHA-256 and byte lengths for all files listed in `data/upstream_manifest.json`; four essential arithmetic and machine sources also have independent hardcoded hash pins. |
| Arithmetic packets | Rebuild the 67- and 68-operation polynomials, the 61- and 62-operation six-equation systems, and the two 41-integer-variable forms; compare all six complete JSON packets. |
| Algebra diagnostics | Recompute operation counts and gate liveness, signed integer and rational evaluations against independent formulas, leading-degree diagnostics, boundary inequalities, and integer-substitution/SOS checks. |
| Exact K215 machine | Parse all 430 transitions from the pinned `.tm` file, compare the Lean and Rocq table literals, and reproduce the 95,714-step bootstrap. |
| Blank computation tableaux | Recheck the start and excluded selectors, phase paths, 32 halting control presentations, local overlaps and vertical seams, and rejection of the tested truncated K215 prefix. |
| Window alphabet | Recompute the exact count, including direct local-predicate enumeration for each of the thirteen representative center types. |
| Fixed coefficients | Rebuild the closed finite coefficient recipes and the sparse compiler checks; bind their machine hash, alphabet count, selector order, and four coefficient ports to the freshly checked outputs. |

For faster iteration, `python3 -B code/verify_all.py --quick` skips only the
direct representative enumeration in the alphabet counter. It still recomputes
the cardinality formulas and all other checks. The receipt records this limit.

## Individual entry points

These commands are also available from the bundle directory. In the example,
`/tmp/zfc-check` is an existing writable output directory.

```sh
python3 -B code/build_fixed.py --repo upstream --output /tmp/zfc-check/fixed_blank_67.json
python3 -B code/verify_k215.py --repo upstream --output /tmp/zfc-check/k215_transitions.json
python3 -B code/blank_helical.py --tm upstream/Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm --output /tmp/zfc-check/blank_helical_checks.json
python3 -B code/count_blank_alphabet.py --tm upstream/Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm --output /tmp/zfc-check/blank_alphabet_cardinality.json
python3 -B code/compiler_constants.py --output /tmp/zfc-check/k215_constants.json
```

`build_fixed.py --output` names the main 67-operation output file. It also emits
the companion packets in the same directory, including two optional
45-integer-variable forms. Those optional forms are regenerated but are not
among the six delivered packets compared by the wrapper.

## Scope of a successful receipt

A `PASS` establishes reproducibility of the finite checks and the supplied
algebra diagnostics. The general soundness, completeness, and ZFC consistency
equivalence are mathematical arguments in the report, the new proof notes,
and the copied upstream proof dependencies. Finite tests alone do not prove
those arguments. The wrapper parses Lean and Rocq table literals; it does not
compile either proof assistant or rebuild the full machine proof dependency
graph. No historical upstream script is executed.

The enormous coefficients and window alphabet remain exact closed finite
definitions. The wrapper does not materialize their full expansions, an
accepting K215 computation, or a complete Pell witness, and does not decide
`Con(ZFC)`. A missing optional upstream manifest is explicitly recorded; the
four essential hardcoded source pins are checked in every run.
