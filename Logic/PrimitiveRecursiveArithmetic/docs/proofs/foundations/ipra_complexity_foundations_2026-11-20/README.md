# Computational complexity in intuitionistic primitive recursive arithmetic

Research package prepared for Vladimir Reshetnikov, 20 November 2026.

Start with **ipra_complexity_foundations.pdf**. The complete editable source is
`tex/report.tex`, with its included section files. The report develops the
mathematics, specifies the first-order arithmetic readings, and gives the
definitions and concrete proof obligations for a complete Lean formalization.

## Main results developed in the report

- Boolean compilation of fixed bounded formulas and bounded induction in iPRA.
- Coded binary words, finite machines, explicit clocks, bounded simulation,
  polynomial bounds, transducers, and reduction composition.
- First-order presentations of P, NP, coNP, L, NL, PSPACE, NPSPACE and EXPTIME.
- Constructive verifier/branch equivalence, closure constructions and the
  standard containment chain.
- Cook–Levin through local circuit unrolling and Tseitin CNF, with explicit
  extension/restriction of witnesses, including preservation of unused inputs.
- SAT in P iff the numerical P=NP sentence, as a conditional compiler theorem.
- Finite configuration bounds, cycle removal, Savitch simulation,
  NPSPACE=PSPACE, and inductive-counting NL=coNL.
- TQBF PSPACE completeness using a single recursive formula occurrence.
- An explicit exponential-time diagonal language and a primitive-recursive
  mismatch input for every polynomial machine descriptor.
- Finite circuit counting with a bounded-search hard truth-table family,
  #P witness counts, fixed polynomial-hierarchy levels, and finite randomized
  computation with integer error amplification.

The report does not settle P versus NP or the other unresolved neighboring
class equalities. The classical results are reconstructed for the stated
arithmetic setting, not claimed as newly discovered complexity theorems.

## Exact formal verification status

`lean/` is an independently checked semantic companion, compiled with
**Lean 4.19.0**, using only bundled **Std**:

- 31 named theorems;
- six audited proof-bearing definitions;
- 12 checked examples;
- no `sorry` placeholders, custom axiom declarations, `sorryAx`, or
  `Classical.choice` dependencies in the audit.

Some proofs use the standard ambient Lean axioms `propext` and `Quot.sound`.
The complete audit is in `verification/lean-build-and-axioms.log`.

**The major complexity theorems have not yet been compiled to actual
object-language iPRA derivations.** The human-readable arguments give the
constructors, finite bounds and permitted induction invariants. The checked
Lean core validates component mathematics. `lean/OBJECT_IPRA_ROADMAP.md`
and report Sections 9–10 give the remaining numerical coding, operational
cost, and proof-lowering obligations. The exact final repository target is
`([] : List (Fm PTm 0)) ⊢[PRAAx] φ`.

The inspected ProveIt revision is
`83421593771f877bc1ae98f4229eb35507bff05b`. Its root toolchain is Lean 4.32.0.
The upstream project was not rebuilt in this task; the standalone package
does not import it. See `SOURCE_AUDIT.md` and the source-blob manifest.

## Files

| Location | Purpose |
| --- | --- |
| `ipra_complexity_foundations.pdf` | Complete mathematical report |
| `tex/` | LaTeX source, bibliography, and all included sections |
| `lean/` | Checked semantic core, examples, axiom audit, pinned toolchain, roadmap |
| `code/graphs.py` | Reachability, Savitch recurrence, bounded paths and nonreachability certificates |
| `code/circuits.py` | Bounded single-tape simulation, circuit unrolling, Tseitin CNF, witness transport |
| `code/test_*.py` | Finite differential, exhaustive and corruption tests |
| `CLAIMS.json` | Machine-readable theorem and verification-status ledger |
| `SOURCE_AUDIT.md` | Source selection and repository reuse decisions |
| `verification/` | Successful build/test logs, PDF checks, upstream source manifest |
| `SHA256SUMS` | Integrity hashes for every other archive member |

## Reproduce

### Lean

Install the pinned Lean toolchain, then run:

```sh
cd lean
bash check.sh
```

The package has no downloaded Lean dependencies beyond the toolchain's Std.
The build prints every audited declaration's axiom dependencies and checks
the examples. Object-theory integration must use ProveIt's own pinned
environment; do not replace the repository toolchain with this one.

### Python

Requires Python 3.10 or newer; no third-party packages.

```sh
python3 -m unittest discover -s code -v
python3 code/circuits.py
```

The combined suite contains 16 tests. Graph checks cover all 530 directed
graphs on 1–3 vertices and 4,674 source/target pairs. Circuit checks include
small complete truth tables, unused-variable multiplicity, independent
machine/circuit comparisons, and rejection of corrupted auxiliary values.
These finite tests are evidence about the implementations, not formal
proofs of the general complexity theorems. The Python graph code materializes
tables and is not claimed to use logarithmic work space.

### PDF

With a normal TeX Live installation providing pdfLaTeX, Latin Modern,
AMS packages, hyperref, xurl, microtype, ragged2e, listings and the usual
table/layout packages:

```sh
bash build_report.sh
```

Set `PDFLATEX` to an alternative executable path if necessary. The script
runs three passes and writes the report PDF at the package root. The
`build/` directory is reproducible temporary output.

## Foundational conventions worth retaining

1. Input languages range over valid binary word codes `x >= 1`; reserved
   code 0 is outside that universe.
2. Primitive-recursive definability does not imply polynomial time.
3. The universal evaluator always has an explicit machine-step clock; no
   total universal evaluator for arbitrary PR syntax is assumed.
4. Bounded induction is lowered to quantifier-free Boolean induction.
5. Semantic Lean verification is distinct from `Prf PRAAx` derivability.
6. A negated unbounded agreement statement is not automatically an explicit
   mismatch witness. The diagonal construction provides the witness itself.
7. Randomized presentations positively identify the intended language;
   one-sided logical implications alone can lose constructive content.
