# Proof-Producing Finitary Interface Graphs for iPRA

This packet develops a general framework for compiling fixed finitary mathematical constructions into object-level derivations of intuitionistic primitive recursive arithmetic (iPRA).

## Main artifacts

- `paper/ipra_pfig_framework.pdf` - compiled research report.
- `paper/ipra_pfig_framework.tex` and `paper/sections/*.tex` - LaTeX sources.
- `lean/PFIG/*.lean` - source-oriented Lean formalization blueprint against ProveIt's `ConciseIPRA` API.
- `lean/FORMALIZATION_PLAN.md` - module dependencies, theorem targets, and completion order.
- `reference/pfig_reference.py` - exact finite reference implementation.
- `reference/test_pfig_reference.py` - regression/property tests.
- `metadata/THEOREM_LEDGER.md` - claim-by-claim status.
- `metadata/difficulty_matrix.csv` - obstacle/resolution audit.
- `metadata/SOURCE_AUDIT.md` - repository snapshot and inspected files.
- `validation/` - test and PDF build records.

## Principal contribution

A fixed finite proof graph is normalized to a query-specialized state machine:

1. a backward pass computes the finite precision/resource demand of every node;
2. a forward pass executes exact transducers, bounded loops, bounded searches, and finite relational viability;
3. the entire pass is encoded as one primitive recursion with one quantifier-free invariant;
4. local `Prf PRAAx` certificates are composed into the terminal object-iPRA derivation.

Relational outputs need not be globally selected. They are either searched at a fixed finite horizon or eliminated by a stable observer. Coherent infinite names are obtained only under explicit shrinking-diameter and motion-tail moduli.

## Status

- Human-readable mathematics: developed in the 76-page report.
- PDF: compiled and visually audited page by page.
- Python reference: all nine tests pass in this artifact.
- Lean: blueprint only; no claim of compilation or kernel checking in this artifact.
- Existing ProveIt object-level combinators: cited from repository snapshot `34816faca8aa605999290b41d26210753b5c3b38`, but not rechecked here.

## Reproduction

From the packet root:

```sh
python3 -m unittest -v reference/test_pfig_reference.py
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error ipra_pfig_framework.tex
```
