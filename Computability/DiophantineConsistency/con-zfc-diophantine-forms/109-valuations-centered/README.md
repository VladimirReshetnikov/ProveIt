# Fixed valuations and centered certificates for Con(ZFC)

Research contribution for ProveIt, 24 October 2026 (UTC).
Comparison snapshot: `ec80841c07e91be8956ce6ed4af9a9c0b782d3d9`.

The main result is an explicit polynomial in **12 unrestricted integer
unknowns, exact degree 2304, and 216 live binary arithmetic operations**.
A cheaper companion uses **209 operations at degree 2848**. These improve
both operation count and degree over the reviewed twelve-integer parents
248/4832 and 223/16000, retaining the entire fixed source34 tuple.

The package also contains a ten-positive-variable equation at **126/718**
(operations/degree), and direct quartics in **395 nonnegative** or **853
unrestricted integer** variables. The direct route uses the numerical
proof calculus C222, with no K215 simulation or Jones universal polynomial.

Read `report/report.pdf` for the construction, ordinary proofs, comparison,
and complete printed direct-quartic residuals. `report/report.tex` is the
editable LaTeX source. Every new equation has a literal machine-readable
specification, and the direct quartics have fully collected coefficient lists.

## Exact results

| Lane | Domain | Variables | Operations | Exact degree | Expanded monomials | Expanded coefficient height or fixed input tuple |
|---|---|---:|---:|---:|---:|---:|
| Integer norm, cheaper | Integers | 12 | 209 | 2848 | Not expanded | Source34 tuple |
| Integer norm, rational auxiliary | Integers | 12 | 215 | 2336 | Not expanded | Source34 tuple |
| Integer norm, centered | Integers | 12 | 216 | 2304 | Not expanded | Source34 tuple |
| Positive norm | Positive integers | 10 | 126 | 718 | Not expanded | Compact44 tuple |
| Direct natural quartic | Nonnegative integers | 395 | Not optimized | 4 | 8292 | 83843425 |
| Direct integer quartic | Integers | 853 | Not optimized | 4 | 9747 | 2445790974704 |

Each complete equation has zeros in its stated domain exactly when ZFC has
a finite syntactic refutation. Negating gives the desired ZFC-provable
equivalence between absence of zeros and Con(ZFC). The ordinary proofs
compose with named, pinned inherited compiler/calibration theorems. No
assumption of Con(ZFC), proof of Con(ZFC), global simplicity optimum, or
new end-to-end Lean/Rocq/internal-ZFC proof object is claimed.

## What changes mathematically

1. Fixed powers of 3 distinguish the square classes that previously needed
   growing Archimedean weights. A smaller nonzero carrier scale and a
   rational, centered auxiliary radical further lower degree. The new
   intersective carrier is `(x*x+3)*(x*x*x-19)`; original31-carrier
   checkpoints are included separately.
2. A scale used to distinguish the strong Pell root is moved from its
   ordinate into the radical itself. Two upper polynomial centers then
   permit a smaller transport majorant without losing positive witnesses.
3. For all natural n,f, the centered factorial identity is

       f=n! iff f=floor((2f+n+1)^n / (2^n * binom(f+n,n))).

   For odd n=2h+1 the quotient becomes `(f+h+1)^n/binom(f+n,n)`.
   Its output supplies the bound needed to exclude false fixed points.
   The final quartics expand all powers, binomials, and floor relations
   into ordinary quadratic residuals.

## Reproduce

Python 3.10 or later and the standard library suffice for all polynomial
checks. From this directory:

    python3 verify.py --output receipts/replays/new-normal.json
    python3 -O verify.py --output receipts/replays/new-optimized.json

The verifier checks the manifest, copies the three lanes to temporary
directories, and executes their independent audits/rebuilders. It does
not overwrite delivered equations or search for consistency witnesses.
It verifies exact counts, coefficient bindings, polynomial identities,
degree certificates, natural/integer restoration, full direct expansions,
and deliberate corruption rejection. The original and peer verification
receipts are included. Finite checks supplement the unbounded proofs.

To compile the report (a normal TeX Live installation is sufficient):

    python3 build_report.py

This compiles `report/report.tex` twice and checks for unresolved references
and overfull boxes. The complete residual appendix sources are already
included, and `direct_quartic/render_centered.py` reproduces them.

## File map

| Path | Contents |
|---|---|
| `report/` | Main PDF, TeX, and complete residual appendices |
| `integer12/` | Six literal norm circuits, new proof, exact constants, independent review, original parent ZIP |
| `positive10/` | Complete 126/718 circuit and proof, whole compact44 tuple and recipe, parent/source proofs and reviews |
| `direct_quartic/` | New factorial compiler, 395/398/853 equations and full expansions, certificates, proofs, original dependency tree |
| `receipts/` | Root verification, PDF checks, and reproducible release evidence |
| `verify.py` | Portable top-level replay without modifying delivered equations |
| `MANIFEST.json` | SHA-256 inventory of release files |
| `REVIEW.md` | Root mathematical review and exact evidence boundaries |

Norm circuits and direct residual JSON use different explicitly documented
schemas. The former list ordinary arithmetic gates; the latter encode a
term `[c,[i,j,...]]` as coefficient `c` times `x_i*x_j*...`. Indices start
at zero. The six-port source34 and four-port compact44 constants must never
be mixed. Both supplied high masks are already shifted.

## Attribution

This is an AI-assisted research contribution. The new reductions build on
the named ProveIt parents, whose original notices and licenses are retained
in their respective lanes. Independent agent reviews and root review found
no gap in the new steps within their stated scope; this is not external
peer review or a proof-assistant certification. The report states the
remaining inherited semantic/formalization boundaries explicitly.
