# A direct quartic for Con(ZFC) in 241 nonnegative integers

The principal equation is the sum of squares of the **189 literal quadratic
residuals** in `equations/principal241/natural/equation.json`. It has **241
nonnegative integer variables**, exact degree four, **30,058** collected
monomials, and coefficient height **85,187,728**. Its full coefficient list
and a plain-text residual version are supplied beside that file.

The ordinary mathematical proof in `PROOF.md`, composed with the explicitly
retained C222-calculus/ZFC calibration, proves in ZFC that this equation has
no natural solution if and only if Con(ZFC). It uses no K215 simulation and
no Jones universal polynomial. No consistency or global-minimality claim is
made, and this is not a new end-to-end proof-assistant certificate.

Compared with the inspected direct 261-variable incoming construction,
the principal improves all four measured counts at the same exact degree:

| Natural quartic | Variables | Residuals | Monomials | Coefficient height |
|---|---:|---:|---:|---:|
| Incoming common-cap parent | 261 | 194 | 31,679 | 85,566,955 |
| Principal combined equation | **241** | **189** | **30,058** | **85,187,728** |
| Dense companion | **239** | **187** | 387,494 | 269,805,528 |

The dense companion saves two further variables and trades away sparse
support and smaller coefficients. These are relative improvements within
this direct quartic architecture; other repository constructions have
fewer variables at other degrees, domains or coefficient sizes.

## Mathematical content

The construction combines a binomial shared by factorial and reciprocal
CRT arithmetic, one Pell anchor certifying all exact and modular indices,
and a radix chosen after the CRT representatives. The frame must include
the modular upper indices as well as the exact-power ports. The new radix
`q=N(S+1)^K`, with `K=R` and horizon 12, removes the representative bound;
the raw ceiling equations supply the required binomial bootstrap before
its intended meaning is used. Every quantified arithmetic object is
compiled to ordinary quadratic residuals in the delivered files.

`INDEPENDENT_REVIEW.md` records a separate mathematical and exact arithmetic
audit. This means an independent review within the AI-assisted research
workflow, not external human endorsement. `SOURCE_LEDGER.json` records the
repository snapshot, the three incoming archive hashes, and each retained
source file. Imported sources keep their notices and license.

## Offline verification and reconstruction

Python 3.10 or newer and its standard library suffice. From this directory:

    python3 -B verify.py
    python3 -B -O verify.py
    python3 -B verify.py --rebuild

Verification checks the complete source ledger; all 225 independently
audited semantic boundary conditions; all 428 affine restorations; all
natural contraction certificates; every collected quartic coefficient;
degree and variable liveness; and deliberate corruptions. Rebuilding runs
the retained portable compiler in a fresh temporary directory, compares
all generated JSON files byte for byte, and removes the temporary directory.
It does not alter the supplied frozen equation files.

To generate a new principal copy or dense companion:

    python3 -B build.py --output NEW_PRINCIPAL_DIRECTORY
    python3 -B build.py --support-cap 64 --output NEW_DENSE_DIRECTORY

To evaluate the principal polynomial at a supplied array of 241 naturals:

    python3 -B evaluate.py POINT.json

This evaluates a point; it is not a decision procedure for existence of
integer zeros. The checkers do not infer unbounded arithmetic theorems
from finite samples.

## File conventions

In every JSON polynomial, a monomial is an ordered list of zero-based
coordinate indices with repetition for powers: `[2,2,7]` means
`z_2^2 z_7`; `[]` means the constant monomial. Each pair
`[coefficient, monomial]` is one integer term. The residual list, not a
square of its sum, defines the sum-of-squares polynomial. All unknowns
range over `N={0,1,2,...}`.

The final natural equation follows from the 777-coordinate semantic graph
by 428 nonnegative affine restorations and then 108 further certified
natural restorations. Every eliminated coordinate is restored explicitly.
All 241 retained unknowns occur in the polynomial.
