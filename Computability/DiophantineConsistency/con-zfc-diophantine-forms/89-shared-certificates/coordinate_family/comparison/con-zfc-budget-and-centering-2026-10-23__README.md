# Pell translations and coefficient budgets for Con(ZFC)

Research package prepared for Vladimir Reshetnikov, 2026-10-23.

Repository baseline: `VladimirReshetnikov/ProveIt`, commit
`2605669a532342f153b13eb6b4a0af4b54f5fa37`, including the wave-10 packages.

## Finished equations

| Packet | Domain | Variables | Exact degree | Live arithmetic operations |
|---|---|---:|---:|---:|
| `integer/generated/octic26.json` | unrestricted integers | 26 | 8 | not optimized |
| `integer/generated/decic24.json` | unrestricted integers | 24 | 10 | not optimized |
| `integer/generated/degree16_23.json` | unrestricted integers | 23 | 16 | not optimized |
| `positive/eleven/p11_positive_degree277.json` | strictly positive integers | 11 | 277 | 111 |
| `positive/twelve/equation.json` | strictly positive integers | 12 | 78 | 103 |

The complete article is `report.pdf`; `report.tex` includes the three
component sections. Each integer packet defines a single equation as the
sum of squares of every listed residual. Each positive packet defines a
single polynomial by its finite division-free straight-line program.
Registers are abbreviations, not extra quantified unknowns.

The ordinary proof establishes, for each equation on its stated domain,

    ZFC proves: no solution <-> Con(ZFC).

The proof uses the explicitly identified native compiler, Pell, and fixed
syntactic-calculus calibration theorems of the source packages. The new
transformations and their exact algebra are supplied here. This is not a
new end-to-end Lean/Rocq or internal object-ZFC proof certificate, and no
global simplicity minimum or worldwide priority claim is made.

The integer equations keep source71's complete six-numeral binding, with
beta=2^1064921-1. The positive equations use the distinct compact44 tuple,
with beta=2^590069-1. All actual fixed integers are included as compressed
minimal unsigned little-endian bytes. **Do not mix tuples or shift MF again.**

## New source-level theorem

`direct/` proves and implements a two-accumulator Horn proof certificate.
Linear weights M+j and a coefficient-budget recurrence replace the earlier
label-difference common-multiple requirement. The local source has 20
natural existential coordinates, five exposed coordinates, degree52, and
one bounded universal family at the trace interface. These are local
counts. The whole fixed-dimensional consistency polynomial from this
architecture is not compiled or claimed.

The article also proves a four-radical separation lemma as an ingredient
for future work. Its carrier compatibility problem remains open.

## Reproduction

Run from this directory:

```sh
python3 verify.py
make
```

The primary checks use only Python's standard library. The optional
independent integer audit uses SymPy 1.14.0:

```sh
python3 independent_integer_audit.py integer
```

The release checks reconstruct coefficients, regenerate equation packets,
verify exact source-row restorations and norm identities, certify degrees,
and test the local certificate implementation. They are finite checks;
the unbounded existence proofs are in the article and pinned upstream
proofs. No program here searches for a ZFC refutation or assumes that
ZFC is consistent.

`verification/` contains review and release receipts. `MANIFEST.sha256`
records the delivered file contents. Running verifiers can regenerate
receipts with a different elapsed time. Expanded term counts in the
integer component count the six numeral ports symbolically; they are not
counts of monomials after specializing those ports to integers.

`python3 build_release.py` regenerates the content manifest and a clean ZIP
next to this directory, excluding LaTeX intermediates and Python caches.
It verifies every archived content hash and the ZIP CRCs. The existing PDF
is included; rebuild it with `make` first if its sources have changed.

## Integration

This archive is ready to place as a new package alongside the existing
sources in `Computability/DiophantineConsistency/con-zfc-diophantine-forms`.
No remote repository mutation is part of this delivery. Preserve the
component notices, source pins, coefficient bindings and licenses.

Suggested integration targets are the paired integral translations and
their exact restoration maps, the 26Z8/24Z10/23Z16 frontier points, and
the coefficient-budget source theorem. Formalization of the native
calibration and the direct trace compiler remain separate tasks.
