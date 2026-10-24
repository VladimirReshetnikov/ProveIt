# The two literal direct quartics

All unknowns in this component range over **nonnegative integers**.
The proof-calculus target is the sealed C222 code 1, with free truth code 0.

The default equation has 3,614 unknowns and is the sum of squares of
2,954 explicitly listed quadratic residuals. It has 15,996 nonzero
expanded monomials, exact degree four, and maximum absolute expanded
coefficient 127,778,545.

The small_height variant keeps all affine gates. It has 6,183 unknowns,
5,523 quadratic residuals, 17,430 expanded monomials, degree four, and
coefficient height 1,993.

## Literal formats

In equation.json, the variables list fixes the coordinate ordering. The
residuals list supplies all quadratic residuals. A monomial is encoded
by a coefficient and a list of variable indices. The list of indices is a
sorted multiset: an empty list means 1; a repeated index means a power.
Every residual has degree at most two. The single equation is the sum
of their squares equal to zero.

The expanded_polynomial.json file lists the same single equation after exact
expansion and collection of like monomials. Its variable order is identical.
BUILD.json binds the source, builder, numerical-calculus implementation,
and two output hashes, and gives the exact census.

Read the concrete JSON field names directly when writing a downstream
parser; the supplied checker is a complete standard-library example.

## Deterministic build

From this directory:

    python3 build_equation.py --output /path/to/new-output
    python3 build_equation.py --keep-linear-wires --output /path/to/height-output

The top-level verify.py --rebuild handles temporary output directories and
exact byte comparison without overwriting the delivered files.

The builder uses the literal constructor implementation in direct_calculus.py.
The expanded wire-eliminated source is retained for independent comparison.
The optional expanded-source and total-power builder switches are comparison
modes; their output is not the default equation described in the article.

## Audits

- check_equation.py: independent expansion, indices and degree census,
  affine restoration, static positive-argument induction, and arithmetic
  regression fixtures.
- audit_calculus.py: exact compositional matching of the numerical C222
  formulas to all 56 source wire definitions and 34 branch residuals.
- audit_source.py: triangular source elimination and branch controls.
- audit_literal.py: reproducible direct-calculus/expanded-source modular
  comparison, 300 assignments over three primes.
- audit_power_graph.py: symbolic elimination of 61 defining gates and
  exact matching of all 17 positive-power constraints.

The root verifier routes receipt writes to temporary paths. Individual
audit scripts may by default update their adjacent receipt; use their
--help options when available to choose another output.

## Source and semantic boundary

The original 13 local wire coordinates are eliminated before bounded
compilation. The final local row has 13 witnesses: three formula labels
bounded by m, four schema witnesses, and six sequence/accumulator witnesses.
A single shared factorial scale handles all bounds. There are exactly
55 positive-power, 16 binomial, and 2 factorial graph occurrences.

The two final quartics are related by projection and nonnegative affine
restoration. They inherit the pinned C222-to-ZF and ZF-to-ZFC calibration.
The report proves the arithmetic transformations and specifies the
Pell-Matiyasevich dependency. This is not a consistency proof or a newly
checked full Lean development.
