# Quadratic-system packing for a ten-integer consistency equation

**One explicit polynomial in ten unrestricted integer unknowns, of exact
degree 237,520,456, evaluated by a 782-operation arithmetic circuit.**

Prepared for Vladimir Reshetnikov's ProveIt project, 23 October 2026.
Reviewed repository snapshot:
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08`.

The article proves, by ordinary mathematics with the dependencies stated
below, that the fixed polynomial `F10` satisfies

\[
 \mathrm{ZFC}\vdash
 \left[\neg\exists(f,g,h,k,l,w,x,y,z,m)\in\mathbb Z^{10}\;
 F_{10}(f,g,h,k,l,w,x,y,z,m)=0\right]
 \longleftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

All ten unknowns range over **all integers**. Every coefficient is fixed by
the included finite recipes and coefficient payloads. Exponents in the
polynomial are fixed integers; the final circuit uses only addition,
subtraction, and multiplication. Coding predicates, roots, divisibility,
and additional witnesses occur in the proof, not as extra operations or
unknowns in the delivered equation.

## What improves

The direct comparison is with package `31-sun10` at the same repository
snapshot. This construction retains its complete native compiler tuple and
its ten-integer finalizer while replacing the source packing.

| Measure | Package 31 | This package |
|---|---:|---:|
| Unrestricted integer unknowns | 10 | **10** |
| Equations | 1 | **1** |
| Exact total degree | `126496 * 5^31 + 27064` | **237,520,456** |
| Binary arithmetic operations | 1,442 | **782** |
| Addition gates | — | 221 |
| Subtraction gates | — | 25 |
| Multiplication gates | — | 536 |
| Native compiler tuple | Package 31's complete tuple | **Identical tuple** |

The degree decreases by a factor of approximately **2.48 × 10^18**.
The literal evaluator uses **660 fewer binary operations**. The operation
comparison counts every addition, subtraction and multiplication in the
arithmetic circuit; fixed integer coefficient leaves are inputs to that
circuit, and their construction is separately specified and verified.
These are explicit construction counts, not lower bounds on all possible
evaluators.

The new idea is to encode the parent's **22 quadratic equations directly**.
Forming their quartic sum of squares before encoding is unnecessary. A
32-element set of integer weights between 0 and 799 has 528 distinct
unordered pair sums, so it separates all homogenized quadratic monomials.
Twenty-two separated target positions then test the residuals
simultaneously in one carry-free packing construction. This preserves the
source interface needed by the ten-integer reduction while dramatically
shortening its fixed exponent range.

This is a substantial relative improvement to the repository's
ten-integer construction. It is not a claim of global minimality, a new
general theorem reducing the number of integer unknowns below ten, or a
decision of either side of the consistency equivalence. Other repository
forms still optimize different measures, such as very small operation
counts with more unknowns.

## Read the construction

| Artifact | Role |
|---|---|
| `report.tex`, `report.pdf` | Complete article, proofs, comparisons, dependency boundary, and further research questions |
| `data/polynomial.json` | Literal ten-input arithmetic circuit defining the final polynomial |
| `data/weights.json` | Explicit 32-element weight set and finite construction parameters |
| `data/coefficient_recipes.json` | Fixed coefficient recipes, residual ordering, and source-base exponent |
| `data/beta_source.bin.gz` | Materialized fixed source constant |
| `coefficients/` | Unchanged package-31 native tuple, reconstruction code, proof, and source notices |
| `code/build.py`, `code/circuit.py` | Reproducible construction of the literal circuit |
| `code/verify.py` | Offline finite verification driver |
| `certificates/` | Exact symbolic, binding, degree, operation, and control-test receipts |
| `upstream/` | Pinned parent and endpoint source excerpts, plus new independent mathematical reviews |
| `research_candidate/` | Separate, unfinished receiver-factorization compiler candidate |
| `SOURCES.json`, `NOTICE.md`, `LICENSE` | Provenance, attribution, and license information |

The authoritative domains and port mapping are part of the article.
In the parent data, the variables are strictly positive; source packing
uses the substitution `x=n+1` with nonnegative `n`. The final ten variables
are unrestricted integers. The fourth native coefficient port is the
already shifted `MF_source`, not the unshifted mask.

## Reproduce

Run from this directory with Python 3, without `-O`:

```sh
python3 code/verify.py
```

The verifier uses Python's standard library. It reconstructs the fixed
native coefficient tuple, rebuilds the new circuit, checks the 22 parent
residuals and all quadratic targets symbolically, verifies the fixed
coefficient bound, checks source/machine bindings, expands the final norm
identity exactly, and runs finite accepting and rejecting controls for
the packing. It writes the current receipts to `certificates/`.

Compile the article with a LaTeX installation containing its listed
packages:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The supplied verification receipt reports `PASS`, ten variables, degree
237,520,456 and 782 operations. The exact degree is supported by both a
total-degree upper bound and a nonzero leading coefficient after all ten
variables are specialized to one indeterminate modulo a prime. That
certificate is an exact lower bound on degree, not a random-evaluation
heuristic. The supplied source-binding receipt confirms that the native
ports are identical to package 31's and that all 430 machine rows agree
with the literal K215 table.

## Proof and dependency status

The article supplies an ordinary mathematical proof of the new source
packing and its composition with the inherited finalizer. It uses the
pinned repository's machine-to-parent equivalence and the explicitly
cited number-theoretic results of Zhi-Wei Sun, including the 2026 preprint
*Ten unknowns for Hilbert's tenth problem over the integers*. The general
ten-integer reduction is attributed to Sun; this package's contribution
is the direct quadratic-system source encoding and its concrete
specialization.

The repository includes Lean and Rocq results for the K215 endpoint.
They are inherited dependencies. This package does not contain a fresh
end-to-end Lean or Rocq proof of the new polynomial, and no such build is
claimed. Finite audits establish the stated finite identities, bindings
and circuit properties; they do not by themselves prove the unbounded
machine/compiler or number-theoretic theorems. Separate reviews supplied
in `upstream/` are internal mathematical reviews, not external human
endorsements.

The proof uses no consistency assumption as a premise for the displayed
equivalence. It does not prove `Con(ZFC)` or produce a ZFC refutation.

## Separate compiler research candidate

`research_candidate/` develops a different local decoder that factors
488 receiver tiles into two receiver modes and seventeen Boolean payload
bits. Its local theorem and finite certificates reduce selectors from
943 to 457 and native support positions from 986 to 523. The materialized
candidate has `B=2^690547`, with 346,098 raw coefficient bytes, compared
with package 36's `B=2^1012115` and 506,664 bytes.

This candidate permits lower payload bits in empty native cells. A
generalization of the inherited binary synchronization argument is still
required before the tuple can be used in a complete consistency
equation. The precise missing interface lemma appears in
`research_candidate/FACTORIZED_RECEIVERS.md`, Section 7. **The main
polynomial does not use these candidate coefficients.** Its proof and
metrics are independent of completing that work.

## Suggested repository placement

A proposed integration location is

```text
SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/
  con-zfc-diophantine-forms/38-quadratic-packing/
```

`38-quadratic-packing` is a proposed directory name, not a claim that the
package has already been committed or accepted. Preserve the complete
package layout and inherited notices. The collection-level comparison
should record the new ten-integer degree/operation point separately from
the unfinished coefficient candidate. Relative links inside verbatim
upstream proof copies describe their original source layouts; `SOURCES.json`
identifies their pinned origins where verified.
