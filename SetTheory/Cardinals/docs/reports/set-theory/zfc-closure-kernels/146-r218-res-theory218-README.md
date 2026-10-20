# Formalism research after K219

The main deliverables are `formalism218_appendix.tex` and
`formalism218_appendix.pdf`. They consolidate the accompanying mathematical
notes and record the distinction between proved logical statements,
bounded source screens, and open consistency questions.

## Independent finite checks

With Python 3 and the standard library:

```sh
python3 certify_fused_d.py --verify-only
python3 uniform_rho8_obstruction.py
```

The first command verifies the retained 211-node K/S/Peirce and modus
ponens proof. Its native transport uses the predecessor's derivations of
K, S, and Peirce from rho8 alone. The second checks the finite algebra
premises of the uniform obstruction and deterministically regenerates its
JSON receipt. Neither command claims to kernel-check the infinite HC or
terminal-cluster arguments.

Compile the already supplied TeX without Pandoc:

```sh
sh build_pdf.sh
```

`build_theory_appendix.py` reconstructs the consolidated Markdown from
the four mathematical note files and the bounded-search receipts. A
conventional Pandoc installation can regenerate TeX using
`markdown+tex_math_single_backslash` as its input format.

## Exploratory artifacts

The four source-screen scripts and their JSON receipts document the exact
finite layout families. They depend on the predecessor macro extractors,
the published K219 native table and source, and the repaired
`source218/hardware_objective219.py` and frozen engine-row classification
in the research workspace. These are exploratory preserved-row compiler
costs, not compiled Turing-machine proofs or global state lower bounds.

The native-zero detachment scripts are proof-discovery tools. Their
recorded bounded failures establish no nonderivability theorem. The
uniform fourth-parameter obstruction is instead supported by its explicit
full-model mathematical argument.

**No altered-calculus source here satisfies the 218-state goal.** An
accepted decoder-only reduction retaining the published source inherits
the existing logical calibration, independently of all open theory
proposals in this directory.
