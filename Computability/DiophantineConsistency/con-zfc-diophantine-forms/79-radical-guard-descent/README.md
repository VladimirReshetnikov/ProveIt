# Radical majorants, guard compression, and Pell descent

Research contribution prepared for Vladimir Reshetnikov's ProveIt project,
23 October 2026. Mathematical development and executable audits with AI
assistance. Repository baseline:
`2605669a532342f153b13eb6b4a0af4b54f5fa37`.

**Start with `report.pdf` or `report.tex`.** This package specifies six fixed
ordinary Diophantine polynomials, their new mathematical reductions, literal
coefficient data, finite generators, and independent algebraic audits.

## Results

All domains below are part of the assertion. Abbreviations in the manuscript
are polynomial expressions, not additional existential variables.

| Domain | Unknowns | Exact degree | Other size measure | Literal equation |
|---|---:|---:|---|---|
| Strictly positive integers | 9 | 1,158,228 | 1,753 live binary arithmetic operations | `nine_positive/equation9.json` |
| Strictly positive integers | 11 | 277 | 111 operations; 108 for its two-residual system | `positive11/p11_positive_degree277.json` |
| Unrestricted integers | 31 | 6 | Sum of 18 squares; 815 symbolic terms | `integer/forms/sextic31.json` |
| Unrestricted integers | 26 | 8 | Sum of 14 squares; 5,459 symbolic terms | `integer/forms/octic26.json` |
| Unrestricted integers | 23 | 12 | Sum of 11 squares; 16,366 symbolic terms | `integer/forms/degree12_23.json` |
| Unrestricted integers | 22 | 14 | Sum of 10 squares; 16,492 symbolic terms | `integer/forms/degree14_22.json` |

The symbolic term counts keep the fixed coefficient ports as symbolic
quantities; they are not a claim about a minimal expanded representation
after numeric collection. No optimized arithmetic-circuit count is asserted
for the integer forms. Positive circuit counts include scalar operations and
squaring, with integer leaves and register reuse free.

Compared with the pinned wave-ten frontier, the nine-positive degree falls
from 1,379,730 by 16.054%, at the cost of increasing 478 operations to 1,753.
The eleven-positive form improves degree 325 and 113 operations to 277 and
111. The integer forms improve the 32-variable sextic and 27-variable octic
by one variable each. Both (23,12) and (22,14) improve the old (26,16) point
in variables and degree. These are measured improvements, not a proof of
global minimality or historical priority. Existing nine-positive and
ten-unrestricted-integer variable bounds are not lowered.

## Main new ideas

1. **Bound the complete radical.** The nine-positive construction takes the
   polynomial part of the formal square root of the entire Pell radicand.
   Clearing denominators yields a 654-term integer polynomial. Two complete
   positive-coefficient certificates turn the discovery calculation into a
   uniform strict inequality. The exact outer-norm degree is certified after
   the new cancellations; the former degree formula is not reused blindly.
2. **Combine calibrated sign conditions.** The integer construction combines
   source71's determinant cone, source68's nearest-square positivity
   criterion, and source75's signed-power bootstrap. Their completeness
   constructions use the same canonical native witnesses.
3. **Reduce norm rows before eliminating coordinates.** An invertible
   polynomial row operation and an integral root shift lower the cost of
   deleting the strong Pell ordinate. This produces the 22-variable,
   degree-14 form. Direct substitution would instead produce degree 20.
4. **Remove an unnecessary denominator guard.** Applying the rational Pell
   descent from source69 to the source70 three-root norm eliminates the
   factor q(q-1) from its strong ordinate. This produces degree 277 with
   eleven positive unknowns and removes two circuit operations.

The alternative appendix gives a new single-loop source for unordered affine
proof certificates: four outer natural parameters instead of five, one
bounded universal block instead of two, and 22 local witnesses instead of
23. It remains a source improvement; no final fixed polynomial metric is
claimed for that route.

## Exact meaning of the consistency assertion

Fix the repository's recursive syntactic ZFC-refutation predicate. For each
listed polynomial P and its listed domain D, the intended theorem is

    ZFC proves: (there is no x in D with P(x)=0) iff Con(ZFC).

The new local reductions are proved in the manuscript. Their composition
uses the inherited ordinary native/compiler, Pell, and syntactic-refutation
calibration theorems, with the precise whole coefficient tuple appropriate
to each component. The full inherited semantic calibration is not proved
anew in this contribution. No new end-to-end Lean/Rocq certificate or sealed
object-language ZFC derivation is supplied. The distinction is substantive:
finite arithmetic checks, external standard-model equivalence, and an
internal ZFC derivation are different verification claims. See the report's
proof-boundary section and retained `provenance/OBJECT_ZFC.md`.

The construction does not assert that any of these polynomials actually has
no solution, and it does not assume or prove Con(ZFC). Each implication is
an ordinary argument intended to formalize in ZFC. The calibrated source is
still K215-based; the independent direct-proof appendix is not substituted
for that source without a completed arithmetic closure.

## Reproduce and inspect

Python 3.10 or later, standard library only, is sufficient for release
verification and all fixed coefficient reconstruction:

```sh
python3 verify_all.py
python3 -O verify_all.py
```

Checks are explicit and do not disappear under `-O`. The integrated verifier
reconstructs all fixed coefficient tuples, regenerates the literal circuits
and integer equations, checks exact identities and degree witnesses, runs
independent sparse-polynomial auditors, and checks the appendix adapter.
Each component retains detailed JSON receipts. The small modular evaluations
and finite Pell examples are diagnostics, not substitutes for the general
proofs. The independent audits are independently implemented within the AI
collaboration, not external human peer review.

The optional discovery regenerator
`nine_positive/regenerate_majorant.py` uses SymPy (tested with 1.14); SymPy is
not needed to check the released coefficients or certificates.

Build the PDF with a TeX installation providing the standard packages listed
at the top of `report.tex`:

```sh
make pdf
```

`python3 make_archive.py` creates the complete ZIP and its SHA-256 manifest.
It excludes caches and TeX build intermediates. There are no downloads or
network calls in the release verification commands.

## File map and integration

| Location | Content |
|---|---|
| `report.tex`, `report.pdf` | Unified mathematical report with the literal compact equations |
| `integer/` | Four SOS forms, compact/expanded JSON, coefficient generator and payloads, retained proofs, independent audit |
| `positive11/` | Eleven-positive circuit, proof, coefficient generator and payloads, exact degree/circuit audits |
| `nine_positive/` | Nine-positive circuit, all majorant/defect coefficients, shifted positivity certificates, independent audits and native data |
| `alternative/` | Single-loop source theorem, local polynomial adapter and diagnostic certificate |
| `PROVENANCE.json`, component source pins | Full commit, source paths, and hashes |
| `licenses/`, component notices | Original repository, K215, Wade and source licenses |
| `VERIFICATION*.json`, `MANIFEST.sha256` | Integrated release receipts and file integrity manifest |

The folder can be copied into a new numbered proposal directory under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/`.
All runtime paths are relative to the component's own directory. No proposed
number is reserved, and no repository files have been edited or published.

Keep each component's **whole coefficient tuple** together. The integer and
nine-positive components happen to share beta=2^1064921-1 but have different
K, MC, and MF ports. The eleven-positive component uses compact44 with
beta=2^590069-1. MF is already shifted in every supplied tuple. Hashes check
the data; actual integer bytes and deterministic finite recipes define it.

New material is offered under MIT No Attribution, subject to preserved
licenses and notices for inherited work.
