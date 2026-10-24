# An eight-column direct C222 consistency polynomial

This component supplies a fully expanded quartic in 7,617 unrestricted
integer unknowns. It reduces the reviewed direct C222 compiler from
27,916 to 7,617 unknowns (72.7%) and from 758,275 to 148,220 monomials
(80.5%). Its 73-bit maximum coefficient is larger than the baseline
coefficient height. Existing native small-variable constructions still
use far fewer unknowns; this is a comparison within the direct proof-rule
architecture, not a claim of a globally simplest consistency equation.

The construction compiles the fixed C222 rules without K215 simulation
or Jones's universal polynomial. Its consistency interpretation imports
the stated C222-to-ZFC-refutation and arithmetic-representation theorems.
The paper and proof files distinguish those imported ordinary theorems
from new reductions and from finite artifact checks.

Prepared for Vladimir Reshetnikov's ProveIt project, 24 October 2026.
The complete report is `report/ConZFC_Direct_Projection.pdf`; its LaTeX
source is beside it. The particular equation is

    P(x_0,...,x_7616) = sum_{j=1}^{4379} r_j(x)^2 = 0.

All 4,379 quadratic-or-lower residuals are explicitly listed. The
expanded polynomial has no unevaluated coefficient ports, variable
exponents, or implicit extra unknowns. Composing the new transformations
with the named inherited theorems gives the ordinary mathematical result

    ZFC proves: (there is no x in Z^7617 with P(x)=0) iff Con(ZFC).

The equivalence does not assume consistency and does not assert either
side of the biconditional.

| Metric | Reviewed Round12 direct quartic | This release |
|---|---:|---:|
| Unrestricted integer variables | 27,916 | **7,617** |
| Total degree | 4 | **4** |
| Expanded nonzero monomials | 758,275 | **148,220** |
| Bounded local witness columns | 29 | **8** |
| Power/Pell graph calls | 108 | **40** |
| Maximum coefficient magnitude, in bits | 49 | **73** |

The reduction is 20,299 variables (72.71%) and 610,055 monomials (80.45%).
The largest absolute coefficient is 8,974,652,400,619,654,748,160.

## Main construction ideas

1. Substitute deterministic constructor wires and premise/conclusion
   labels separately inside each of the twelve rule branches.
2. Pad a proof with truth steps until its horizon `N` bounds the four
   genuine rule parameters. A fixed monotone polynomial `H(N)` bounds
   every label, so the large evaluation base is chosen before the
   accumulator and its beta encoding.
3. Bound beta remainders by their scale `y`; the two strict-remainder
   slack columns disappear. The eight local columns are
   `(a,b,c,d,S,q,S_next,q_next)`, bounded by `(N,N,N,N,y,U,y,U)`.
4. Enlarge the CRT factorial argument to dominate all coordinate bounds.
   The bound factorials are units modulo the CRT product and cancel from
   the range conditions. An entire factorial graph disappears.
5. Compile signed integer arithmetic directly, use one signed quotient
   per congruence, and infer the signs of unconditional Euclidean
   quotients. Guard only semantic inputs that still need nonnegativity.

## Files

- `equations/equation_integer.json`: the complete ordinary polynomial.
- `equations/residuals_integer.json`: its 4,379 quadratic-or-lower
  residuals, whose squares sum to that polynomial.
- `equations/circuit_integer.json`: the literal signed arithmetic DAG.
- `equations/source_circuit_before_pruning.json`: source bindings and
  arithmetic primitive call ledger for independent audits.
- `SCHEMA.md`: coefficient, monomial and coordinate conventions.
- `source/PREPROCESSING_PROOF.md`: the eight-column source proof.
- `proofs/SIGNED_COMPILER.md`: signed arithmetic and quartic conversion.
- `checks/COMPARISON.json`: baseline, checked 9,476-coordinate checkpoint,
  and final metrics. The checkpoint polynomial is not duplicated here.

## Rebuild and exact checks

Python 3's standard library is sufficient. No network, external package,
Turing-machine run, halting search, or consistency decision is used.

For the complete release verification, run:

```bash
python3 verify.py
```

This checks the release manifest when present, verifies the projected
source, rebuilds the six core artifacts, compares them byte for byte,
runs both independent final checkers, and confirms that three intentional
corruptions are rejected. All mutations and builds occur in a temporary
copy. To retain a new receipt outside the frozen release:

```bash
python3 verify.py --output /tmp/con-zfc-direct-verification.json
```

The `--optimized` option runs subprocesses with Python `-O`. Included
receipts also record successful normal and optimized builder/interface
checks. The recorded runtime was CPython 3.12.14.

Individual commands are:

    python3 build.py --output /tmp/proveit-direct-rebuild
    python3 check_exact.py /tmp/proveit-direct-rebuild
    python3 check_signed_independent.py /tmp/proveit-direct-rebuild \
        --natural-source source/circuit.json
    python3 source/check_projection.py

`build.py` reconstructs every coefficient of the final equation. The
independent exact checker imports no builder: it reconstructs every
arithmetic residual from the literal DAG, checks the nonnegativity
guards, expands their squared sum, and compares all coefficients.
The source checker verifies the finite local projection and CRT
interfaces; neither checker replaces an unbounded mathematical proof.

There is no newly completed Lean/Rocq certificate or encoded
object-language ZFC derivation in this component. The theorem claimed at
the ordinary mathematical level is the equivalence between existence of
an integer zero and a finite ZFC refutation, after composing the named
inherited calibration. No claim that ZFC is consistent is made.

## Rebuild the paper

With a conventional TeX Live installation containing the packages in
the LaTeX preamble, run:

```bash
python3 report/build_report.py
```

Auxiliary files stay in a temporary directory. The byte-for-byte rebuild
claim concerns the six core JSON artifacts, not PDF metadata across
different TeX installations. `report/metrics.tex` records counts from
the final equation. `MANIFEST.json` covers every other release file.

`equations/variable_map.json` is a static explanatory coordinate map.
The six files regenerated by the equation builder are enumerated in
`verify.py`; they contain the entire literal polynomial and construction.

## Provenance and integration

The reviewed repository snapshot is
`04a1d79222d55cabe4ba52897863fc33baa8c268`. The direct baseline came from
`docs/incoming/ConZFC_Direct_Centered_Round12_2026-10-24.zip`, whose hash
and file pins are in `provenance/BASELINE_PINS.json`. The inherited
logical sources retain the earlier pin
`9a33342a03d19cf5b061b2083c6b5d3f27f752ed`, with original paths and hashes
recorded separately. The frozen `.lean` files are review dependencies,
not a standalone compilable Lean project.

`provenance/BASELINE_NOTICE.md` and
`provenance/BASELINE_MATHEMATICAL_AUDIT.md` are historical baseline files.
Their references to other constructions describe the earlier archive,
not missing deliverables or additional claims of this release. Current
attribution and scope are in `NOTICE.md` and this README. Original
licenses and notices are retained; `LICENSE.NEW` covers new material
to the extent a license is required.

For integration, preserve this as an additional direct-construction
research package, or place the ZIP in `docs/incoming`. It does not
replace native few-variable constructions. No remote repository files
were changed in preparing this delivery.

SHA-256 of `equations/equation_integer.json`:

```text
af06bc5c92b9ab6b1cb4d0da94933c2280720537a3088585649f7793466da382
```
