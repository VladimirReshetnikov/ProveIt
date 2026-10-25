# A direct quartic in 260 unrestricted integers

The principal equation is

    P(x_0,...,x_259) = sum_(j=0)^184 r_j(x)^2 = 0,

where every `r_j` is a literal quadratic polynomial in
`equations/symmetric_caps/equation.json`. The full collected polynomial is
`expanded_polynomial.json` in the same directory. Every coordinate ranges
over all integers. There are no symbolic coefficient ports, variable
exponents, factorial operations, or unspecified arithmetic predicates in
these final files.

| Endpoint | Integer variables | Residuals | Degree | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Principal, `symmetric_caps` | 260 | 185 | 4 | 5,099 | 128,446 |
| Dimension tradeoff, `dimension259` | 259 | 184 | 4 | 21,287 | 240,653 |
| Authenticated Cofinal Anchors parent | 282 | 192 | 4 | 5,491 | 128,446 |

The principal saves 22 variables, seven residuals and 392 collected terms
relative to that parent, at unchanged degree and coefficient height. The
259-variable variant spends substantially more terms and larger coefficients
to remove one more variable. Neither construction is claimed globally
minimal or a variable-count record among all consistency quartics.

## Mathematical result and attribution

The new ordinary proof composes three changes:

1. The comparison center is fixed by `f=(1-A)H`, `D=A+Hf`, and its index
   congruence uses the modulus `C`. The sharper Pell-growth margin and
   explicit unit-ordinate exclusion make this valid at either sign of A,
   without doubling the old frame. The center polynomial itself has an
   earlier appearance in the incoming Certificate Reductions package.
2. A pooled row contains all fourteen squared ordinate errors and only
   nine linear terms `1-X_i`. The other five abscissa orientations follow
   from their genuine power requests in an acyclic order.
3. Eleven separate interval-product guards are replaced by four symmetric
   quadratic remainder caps. The key pre-factorial coefficient estimate
   proves their soundness before invoking the factorial identity.

`CENTER_PROOF.md`, `LINEAR_POOL_REVIEW.md`, and
`GROUPED_SIGNED_DIGIT_CAPS.md` supply the unbounded arguments. The three
immediate parent proofs remain in `baseline/`, and the inherited Pell,
factorial, CRT, Horn-calculus and named logical-interface source texts are
retained under `inherited/`. Some inherited source paths describe the
original package layout; `SOURCE_PINS.json` maps every retained file to
its actual archive member and SHA-256 identity.

These arguments and the identified inherited C222/ZF/ZFC-refutation
calibration establish an ordinary proof formalizable in ZFC that integer
solvability is equivalent to finite ZFC refutability. Negating yields
the requested ZFC-provable equivalence between unsolvability and Con(ZFC).
This uses neither K215 simulation nor Jones's universal polynomial.
The retained interface declarations are not a new end-to-end Lean/Rocq
build or an encoded object-language ZFC derivation. The work does not
prove consistency, inconsistency, or global minimality.

## Exact data and readable exports

In each residual or collected polynomial, a term `[c,[i,j,...]]` means
`c*x_i*x_j*...`; repeated indices denote repeated factors, and `[]`
is the constant monomial. Coordinate indices are zero-based. The file
`equation.json` contains the complete ordered coordinate list and every
quadratic residual. `expanded_polynomial.json` contains every collected
quartic coefficient.

The adjacent `residuals.tex` and `residuals.txt` transcribe every row.
`variables.tsv` gives the retained source coordinate, name and integral
shift: the source coordinate equals the final variable plus the last
column. Projection certificates give all further deleted-coordinate
restorations, in reverse elimination order.

`evaluate.py` exactly evaluates either equation on a supplied JSON array of
all ordered coordinates. It verifies an individual proposed tuple; it is
not a procedure for deciding whether any solution exists.

The source certificate records exactly three row replacements, eleven
removed private guard rows, and four fresh caps. No other source row is
changed. The principal's 216 later monic substitutions are independently
replayed; the dimension variant uses 217.

## Reproduce offline

Python 3.10 or later and its standard library are sufficient. The main
entry point works from any current directory and leaves the release
unchanged:

    python3 -B verify.py --rebuild
    python3 -B -O verify.py

Use `--receipt /path/to/new-receipt.json` to save the output. The rebuild
runs in a temporary directory and compares eleven files per endpoint
byte for byte. The verifier authenticates all retained inherited sources,
checks both complete polynomials and their readable transcriptions, and
runs a second independently authored checker for the principal equation.

For direct component checks:

    python3 -B check.py
    python3 -B check_independent.py
    python3 -B render.py --check

The independent checker imports neither the producer nor its polynomial
arithmetic or projection implementation. The other checker reconstructs
the source delta without importing the producer, checks the actual
four-way denominator partition, replays all projection certificates and
uses its own translation/expansion routine. Mutated center, index, pool,
cap and coefficient data are rejected even if their supplied hashes are
refreshed. Finite checking authenticates these exact algebraic artifacts;
it does not replace the unbounded mathematical proof.

To build a separate principal copy:

    python3 -B build.py --output /path/to/new-equation
    python3 -B render.py /path/to/new-equation

Use `--cap 20` for the 259-variable variant. The verified local trials at
caps 20, 24 and 32 produced the same dimension tradeoff; no exhaustive
optimization is claimed.

## Provenance and licensing

The repository snapshot is
`e0c98c629bf10d30b695884f6b1d2ab361bdf513`, including the actual incoming
`ConZFC_Cofinal_Anchors_Height_One_Round17_2026-10-25.zip`. Its archive hash
and every retained source member are in `SOURCE_PINS.json`.

New code and exposition were prepared with AI assistance for Vladimir
Reshetnikov and ProveIt. Retained material preserves its original licenses
and notices in `inherited/`. The present finite and mathematical reviews
were separate tasks within the same AI-assisted workflow and are not
outside human peer reviews. No repository publication or mutation is
performed by this component.
