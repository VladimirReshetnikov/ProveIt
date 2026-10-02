# Factorial growth of ascent sequences avoiding 000

## Result

For a_n=OEIS A202058, this report proves

lim (a_n/n!)^(1/n) = 8/(3*pi^2).

The exponential generating function has radius 3*pi^2/8. A coarse logarithmic error bound and controlled leading Lambert-W threshold inverse are also proved. The constant was conjectured by Conway, Conway, Elvey Price and Guttmann (2022); their exact compacted recurrence is the starting point.

The ratio limit, leading amplitude, power/stretched-exponential factors and all-orders expansion remain unresolved. The coarse 9/13 error exponent is a proof bound, not a claim about the true correction scale.

## Contents

- a202058-report.pdf: complete mathematical report
- a202058-report.tex: editable source
- build.sh: two-pass portable PDF build
- verify_radius.py/json: independent recurrence, direct enumeration, uniform residual and characteristic-integral checks
- verify_root_limit.py/json: bounded-shift calculus checks
- verification-summary.json: build, mathematical-review and layout verification scope
- requirements.txt: numerical verification dependency

## Reproduce

Run with Python3:

    python -m pip install -r requirements.txt
    python verify_radius.py
    python verify_root_limit.py

The radius check visits 287820 state/parameter cases and can take around a minute. These are finite diagnostics; the report proves the uniform inequalities analytically.

To build the PDF, install a normal TeX Live distribution providing pdflatex, amsmath, amsthm, lmodern, microtype, enumitem and hyperref, then run:

    bash build.sh

The script keeps its generated TeX format and other mutable build files in a local .build directory. No network access, repository write, or account access is required by the checks or build.
