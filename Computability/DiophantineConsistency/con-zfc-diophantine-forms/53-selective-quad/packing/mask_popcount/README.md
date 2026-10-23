# Selective sparse-borrow ten-integer consistency equation

One completely fixed polynomial in ten unrestricted integer unknowns, exact degree **21,111,400**, with a **659-operation** division-free arithmetic circuit. Its lack of integer solutions is equivalent in ZFC to Con(ZFC), using the explicitly stated inherited machine/compiler and Sun arithmetic theorems.

The new source layer combines:
- Selective isolation of the 136 source terms, without demanding a full Sidon set.
- One-bit padding only at marked target cells, with a proof that incoming borrows are harmless.
- A carry-to-binomial threshold calibrated to the exact population of the fixed mask.

Compared with package 40's ten-integer 237,520,456-degree/782-operation construction, this reduces degree by a factor greater than 11.25 and uses 123 fewer operations (15.7%). The equation does not beat other variable/domain tradeoffs on every metric and no global minimality is claimed.

## Read and reproduce

- `report.pdf`, `report.tex`, `section.tex`: full new source proof and explicit final equation.
- `generated/signed10_b2.json`: literal polynomial DAG.
- `INSTANCE.json`: active coefficient and source binding.
- `generated/source_records.json`: finite fixed-coefficient recipes.
- `data/`: complete parent system and four compiler-port payloads.
- `SOURCE_PINS.json`: 12 exact files verified at ProveIt commit `124c07c0b77a9e20e84676514d8b1ff78536ea3f`.
- `upstream/`: inert copies of the finalizer, parent and coefficient adapter proofs.
- `generated/INDEPENDENT_CHECKS.json`: exact source, circuit and degree certificates plus finite control tests.

With Python 3.10+ and its standard library:

    python3 reproduce.py

This rebuilds the circuit, verifies byte-identical output, and runs an independent checker that does not import the builder. The checker reconstructs the shifted source exactly, verifies 71,808 isolation interactions, checks 52 local polynomial identities and the 35-term norm identity, validates payload/source hashes, audits gate liveness/counts, and certifies exact degree using three nonzero modular leading coefficients. The independent checker also works with `python3 -O independent_check.py`.

For modular evaluation, in variable order f,g,h,k,l,w,x,y,z,m:

    python3 evaluate.py --modulus 1000003 1 1 1 1 1 1 1 1 1 1

A modular zero is not an integer-solution certificate. The evaluation count excludes construction of fixed coefficient leaves; it is not bit complexity.

To rebuild the PDF, run `pdflatex -interaction=nonstopmode -halt-on-error report.tex` twice from this directory. The included PDF needs no TeX installation to read.

## Proof boundary

The new unbounded mathematical arguments are supplied in `section.tex`. The existing compiler/K215 endpoint and Sun's number-theoretic theorems remain imported mathematical dependencies. Their source pins and exact invocation are identified. The package is self-contained for its finite reproduction and defines all coefficients without a network connection; it is not a self-contained reproof of all inherited theorems, a fresh Lean/Rocq certificate, or a decision of consistency.

The source is the original package-31 parent, shifted coordinatewise from positive to nonnegative inputs. Do not splice in package-45's different transport row. `MF_source` is already shifted, and all four ports must remain one coherent tuple. Historical bindings within preserved source files do not supersede `INSTANCE.json`.
