# Finite mathematical interfaces in iPRA

## Start here

Read **[paper/report.pdf](paper/report.pdf)**, a 35-page research report with complete human mathematical arguments, a comparison with the existing repository frameworks, executable definitions, and a staged Lean formalization plan. The LaTeX entry point is **[paper/report.tex](paper/report.tex)**.

The report is based on the ProveIt snapshot
`b0f6f535ffc16324683fef2c263260a88ae03755`:
<https://github.com/VladimirReshetnikov/ProveIt/tree/b0f6f535ffc16324683fef2c263260a88ae03755/Logic/PrimitiveRecursiveArithmetic>.

This is a targeted extension of nine earlier framework packets and selected difficulty reports. It is not an audit of every mathematical argument in the repository's 60-packet collection, and it does not assert general Siegel, Faltings, Mordell--Weil, or prime-distribution results in iPRA.

## Main results and their exact scope

1. **Finite interfaces and proof transport.** Mathematical objects are represented by coded finite observations, bounded validity and comparison predicates, primitive-recursive operations, local arithmetic contracts, and explicit execution resources. The report proves a restricted compilation principle that consumes iPRA proofs of the local contracts and bounded invariants. Booleanization and this general compilation principle are human metatheorems; a complete verified compiler for every such construction is not included.

2. **Changing-parameter recursion compiled to actual PR syntax.** For fixed primitive-recursive symbols `D`, `b`, and `F`, the new Lean compiler constructs a symbol satisfying the parameter-changing recurrence

   ```text
   X(0,k) = b(k)
   X(n+1,k) = F(n,k,X(n,D(n,k))).
   ```

   It uses a backward demand schedule and forward replay. The syntax and its semantic recurrence laws are kernel checked. A generic term-to-symbol compiler and the backward-pass defining equations have actual checked `Prf PRAAx` derivations. The full internal two-pass recurrence is an explicitly stated remaining proof target.

3. **Primitive-recursive fuel for fixed-dimensional lexicographic descent.** For a nondecreasing primitive-recursive coordinate envelope `h(x,t)`, set `F_0(x,s)=s+1` and obtain `F_(d+1)(x,s)` by iterating `F_d(x,.)` exactly `h(x,s)+1` times from `s`. The report proves the exact controlled-chain bound and constructs `h` automatically from finite simulation of a total one-step map. For each externally fixed dimension `d`, the resulting execution bound is primitive recursive. Explicit Lean PR syntax and denotation proofs are checked; the chain and termination theorems remain Lean targets. A full human diagonal argument shows why arbitrary input-dependent dimension cannot be included in the general PR claim.

4. **Complete affine rational plane-intersection lists.** A bounded shear makes both polynomials have constant nonzero leading coefficient in the eliminated variable. The finite Sylvester determinant gives a degree-product bound; a Vandermonde argument accounts for repeated projection fibres. Bounded rational-root scans then return every rational common point and an effective coordinate-height bound. The successful domain is an explicit nonzero-resultant test. Unsupported inputs are distinguished from a proved empty intersection. Concrete Lean and Python definitions are included; the general Lean correctness proofs are targets.

5. **Finite auxiliary envelopes without a witness selector.** If every target point has a good auxiliary polynomial in a proved finite degree-and-coefficient-height box, exhaust that box and its complete intersection lists. This gives a complete target list and height bound without selecting an auxiliary for each point. The coverage hypothesis remains a mathematical obligation. A separate halting-time example proves that a cardinality bound alone cannot uniformly produce a list or height bound.

## Files

| Path | Contents |
|---|---|
| `paper/` | LaTeX source, compiled PDF, bibliography, build script |
| `lean/` | Ten standalone Lean modules, toolchain declaration, build script, detailed README |
| `lean/validation/` | Compiler logs, source comparison, theorem axiom audit, precise formalization status |
| `code/` | Three exact-arithmetic Python reference programs |
| `verify.py` | Runs all included finite Python diagnostics |
| `validation/` | Python results, final LaTeX logs, PDF metadata and visual QA record |
| `CLAIMS.json` | Per-result human-proof, executable, and Lean status |
| `provenance/` | Pinned source inventory, repository packet catalog, comparison and reuse notes |
| `MANIFEST.sha256` | SHA-256 checksums of all other delivered files |

## Formal verification status

The standalone development compiled with **Lean 4.32.0** using `Std`. Its ten modules comprise eight new modules and two reused dependencies. Eleven selected theorem declarations were axiom-audited; their dependency union is `{propext, Quot.sound}`, with no `sorryAx` or `Classical.choice` dependency. These are Lean metatheoretic dependencies, not additional axioms of the embedded iPRA calculus.

Four new checked declarations have an actual object-theory derivability conclusion: `TermCompiler.symbol_correct`, `TermCompiler.transport_equation`, `DemandCompiler.object_backward_zero`, and `DemandCompiler.object_backward_succ`.

There are **28 explicitly unproved target propositions**: seven object-iPRA targets and 21 host targets, of which four concern lexicographic bounds, three rational roots, and fourteen plane elimination and auxiliary envelopes. Targets are definitions of propositions, not added axioms or proofs containing `sorry`. Compiling their definitions does not prove them. The full Mathlib-backed repository integration build was not run.

See [lean/README.md](lean/README.md), [lean/validation/STATUS.json](lean/validation/STATUS.json), and report Section 7 for definitions, exact theorem statements, dependency order, and the route from host correctness to internal arithmetic proofs.

## Rebuild

From this directory:

```sh
python3 verify.py
LEAN_BIN=/absolute/path/to/lean-4.32.0/bin/lean bash lean/build.sh
bash paper/build.sh
```

The Python programs need only the standard library. Lean 4.32.0 and a working TeX Live installation are external build dependencies; neither toolchain is bundled. The PDF script can construct a private format from the installed TeX sources if an ordinary `pdflatex` format is unavailable. Set `TEX_WORK_DIR` to an absolute temporary directory to control that fallback's location.

The recorded checks comprise 55 exact maximal controlled chains, 23 fuel monotonicity comparisons, eight resetting runs, five exact plane-intersection classifications with independent bounded-box scans and edge cases, and one exhaustive small auxiliary-box example. These are finite executable diagnostics. Universal correctness is supported by the human proofs; it is not inferred from testing.

To verify file integrity before rebuilding:

```sh
sha256sum -c MANIFEST.sha256
```

Rebuilding intentionally replaces generated outputs and logs, so their original checksum entries may then differ.

## Attribution and boundaries

The semantic backward-demand construction is reused unchanged from the earlier `ipra_finite_demand` packet. The object kernel is the earlier standalone arrangement of the repository's syntax, deduction, and PRA files; its source sections were compared with the pinned repository. New contributions and inherited results are separated in the paper and provenance notes. The reused ProveIt material is accompanied by its MIT-0 license in `lean/LICENSE`.

No remote repository files were modified. The archive is a standalone research deliverable, not a claim that the remaining target propositions have been integrated or proved in the upstream project.
