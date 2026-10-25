# Trace-linear compact consistency equations

The principal circuit `equations/trace87_degree232.json` is a fixed ordinary
polynomial in **ten strictly positive integers**, of **exact degree 232**, with
an **87-operation evaluator**. Four other operation/degree tradeoffs are
75/402, 76/352, 79/290 and 80/258. Every fixed coefficient is supplied in full;
the largest fixed port has 592,884 bits. No circuit register is an extra
unknown, and no power with variable exponent occurs in any final graph.

The new arithmetic step replaces the auxiliary expression
`f^2(cT-R)-c` by `f(cT-R)-c` because the doubled Pell trace is already the
polynomial `f=1+2a` and is identically 1 modulo c. The complete new argument
is in `PROOF.md`; `section.tex` is an article-ready summary. The main equation
and all definitions appear in both. `coefficient_recipe.tex` prints the entire
finite recipe for the four fixed ports, including its 436-character seed.

The ordinary proof composes with the named inherited native and syntactic
refutation calibration to prove in ZFC that absence of a positive zero is
equivalent to Con(ZFC). It neither assumes nor proves consistency. It is not
a new end-to-end Lean/Rocq certificate or a global minimum theorem. These
equations retain a native/K215 ancestry; the separate direct-calculus route
in the overall research package has a different ancestry and domain.

## Reproduce

Python 3 and its standard library suffice:

```sh
python3 -B verify.py --receipt /tmp/trace-verification.json
python3 -B -O verify.py --receipt /tmp/trace-verification-O.json
python3 -B build.py --check
python3 -B inherited/lucas/parent/rebuild_coefficients.py
```

The verifier checks all actual graph rows by exact polynomial cuts, every
whole leading homogeneous part, all coefficient bytes, parent relations and
source hashes. It rejects eighteen targeted operator corruptions per graph.
It does not infer unbounded Pell facts from finite searches. The generator
reproduces each new graph from frozen JSON; it executes no inherited program.
The final command reconstructs all four whole integers from the finite seed
and tile recipe and compares them to the retained payloads.

`RESULTS.json` gives the complete metric table. `VERIFICATION.json` and its
optimized counterpart contain the exact receipts. `SOURCE_LEDGER.json`
authenticates 105 retained source files from the incoming Lucas-correction
and cofinal-witness packages at the inspected ProveIt snapshot
`b7e35224c04fe1031c0a53f80a395e9b32205022`.

Prepared with AI assistance. Mathematical review by separate collaborating
agents is an internal review, not external human endorsement. All inherited
licenses, proof dependencies and notices are preserved in `inherited/`.
