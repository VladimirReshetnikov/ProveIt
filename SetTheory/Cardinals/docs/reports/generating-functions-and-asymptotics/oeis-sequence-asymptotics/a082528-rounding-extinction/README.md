GAMMA CONSTANTS AND SCALING LIMITS FOR ROUNDING EXTINCTION
Reproducible computation package
Recorded run: 4 October 2026 (UTC)

PURPOSE

The accompanying article proves
    tau_m(n) ~ (c_m n)^(1/(m+1)),
    c_m = m Gamma(m/(m+1))^(m+1),
and related threshold and path limits.

This program checks the finite arithmetic and generates numerical
illustrations. Finite checks and floating-point plots are not substitutes
for the mathematical proofs in the article.

QUICK REPLAY

From this directory, run:
    python reproduce.py

A complete replay uses Python plus mpmath and matplotlib. It needs no
network access. The recorded environment was Python 3.12.14,
mpmath 1.3.0, and matplotlib 3.10.8. requirements.txt records the last two
versions. The code is written for Python 3.10 or later.

To run only the exact checks, using the Python standard library:
    python reproduce.py --exact-only --out replay_exact

To run the full calculation into another directory while retaining the
recorded outputs:
    python reproduce.py --out replay_full

The program reads data/oeis_prefixes.json relative to the program itself.
All generated output goes to the selected output directory. Existing
generated files at that destination are replaced.

By default the threshold tables and convergence figure reach K=100000.
The optional flag --max-k changes that maximum; it must be at least 1000.
Example:
    python reproduce.py --max-k 10000 --out replay_short

EXACT QUERIES AND RATIONAL EXPONENTS

Examples:
    python reproduce.py --threshold 1000 --m 2/3
    python reproduce.py --stop 12345 --m 3/2

The --threshold query returns T_m(K), the least starting integer n for which
tau_m(n)>K. Thus tau_m(n)=K+1 when
    T_m(K) <= n < T_m(K+1).

The initial condition is x_1=n, with stages k=2,3,... . We set tau_m(0)=1.
For the forward-path plot only, x_0 is also defined as n to make the
rescaled path meaningful at t=0.

The exponent is parsed as an exact Fraction. For m=p/q>0, each backward
step is computed as
    ceil_root_q( v^q k^p / (k-1)^p ).
The forward normalized step uses
    floor_root_q( v^q (k-1)^p / k^p ).

Both use integer arithmetic. The square-root case uses math.isqrt.
Other degrees use an integer Newton algorithm. The final ceiling decision
uses an exact integer comparison; no numerical root can change a floor or
ceiling decision.

The directly simulated original recurrence for integer m is an independent
implementation:
    x_k = k^m * (x_(k-1) // k^m).

CHECKS IN verification.json

1. Integer-root defining inequalities: 90009 cases.
2. Rational-root floor and ceiling inequalities: 27555 cases.
3. For m=1,2,3 and every integer n=0,...,2000:
   - original x-rounding equals normalized forward rounding;
   - each forward stopping time agrees with its exact backward-threshold
     interval;
   - the computed threshold ranges are strictly increasing.
4. Exact rational exponents 1/2, 2/3, 3/2, 5/3:
   forward versus backward-threshold intervals for n=0,...,200.
5. Displayed OEIS prefixes:
   - A073047: 79 terms, starting at n=1;
   - A082527: 105 terms, starting at n=0;
   - A082528: 105 terms, starting at n=0.
6. Block weights w_k=ceil(k/3)^m, for integer m=1,2,3:
   - T_block(K)=T_m(ceil(K/3)), K=1,...,200;
   - tau_block(n)=3(tau_m(n)-1)+1, n=1,...,2000;
   - tau_block(0)=1 is checked as a separate exception.
7. Exact finite-product endpoints for integer m=1,2,3,5 and j=10,100,1000.
   Their relative interval width is checked exactly:
       upper/lower - 1 = m/((m+1)j).

The three larger forward paths are also checked against the exact threshold
bracket for their observed stopping times.

CONSTANT CERTIFICATES

For integer m, the program constructs the exact rational product
    t_j = product_(r=1)^j (1 - 1/((m+1)r))
and the exact rational endpoints
    lower = 1 / [t_j^(m+1) (j/m + 1/(m+1))],
    upper = m / [j t_j^(m+1)].

The theorem makes these an interval containing c_m. Arithmetic values are
stored as numerator/denominator pairs in data/constant_certificates.json.
Their comparison with the Gamma expression uses 70-digit mpmath arithmetic
and is explicitly classified as a numerical diagnostic.

data/constant_intervals.tex rounds lower endpoints downward and upper
endpoints upward to ten decimal places using exact integer arithmetic.
The central Gamma values are rounded for display. The CSV retains
higher-precision numerical endpoint values; the exact rationals are the
certificate of record.

All Gamma parameters are formed in mpmath before division. In particular,
the code does not evaluate m/(m+1) as an ordinary machine float.

FILES

reproduce.py
    Source for all exact checks, tables and figures.

requirements.txt
    Recorded versions of the two optional numerical/plotting packages.

verification.json
    Scope and outcome of the exact checks, numerical diagnostics,
    environment, and recorded runtime.

data/oeis_prefixes.json
    Fixed input fixtures with OEIS links, retrieval date and offsets.

data/gamma_constants.json
    Numerical values of c_m for m=1/2,1,2,3,5, at 60 significant digits.

data/threshold_table.csv
    Exact T_m(K), Gamma constant, and normalized threshold
    c_m T_m(K)/K^(m+1), for m=1/2,1,2,3,5 and K=10,100,1000,10000,100000.

data/threshold_table.tex
    Typeset version through K=10000; it requires the booktabs package.

data/threshold_convergence.csv
    Exact thresholds and normalized values used in the convergence plot.

data/constant_certificates.json
    Exact rational products and interval endpoints.

data/constant_intervals.csv
    Numerical display of the finite-product intervals.

data/constant_intervals.tex
    Typeset j=1000 intervals, with outward decimal endpoint rounding;
    it requires the booktabs package.

data/backward_profiles.csv
    Exact backward q_k values for m=3, K=20,100,1000 and their rescalings.

data/limiting_profile.csv
    Breakpoints of the piecewise linear m=3 limit on [0.12,1].

data/forward_profiles.csv
    Exact integer forward x_k values for m=3 and initial values
    n=1000,1000000,1000000000, with their observed stopping horizons.

data/limiting_forward_profile.csv
    Numerical values of F_3(t)=c_3 t^3 y_3(t) on a grid in [0,1].
    The endpoints are defined as F_3(0)=1 and F_3(1)=0.

figures/backward_profiles.png
    The backward scaling limit and exact grid profiles on [0.12,1],
    plus an enlarged view of the final ceiling levels. Discrete grid
    values are joined by straight lines.

figures/normalized_thresholds.png
    Exact threshold ratios for m=1,2,3, on a logarithmic K axis.
    A second panel magnifies the larger horizons. The irregular
    fluctuations are visible; no convergence-rate claim is inferred.

figures/forward_paths.png
    Full forward step paths for m=3 compared with F_3(t). The horizontal
    coordinate uses each path's actual first-zero horizon J.

The PNG figures have white backgrounds and are rendered at 250 dpi.

OEIS PROVENANCE

The fixed prefixes were retrieved on 4 October 2026 (UTC) from:
    https://oeis.org/A073047
    https://oeis.org/A082527
    https://oeis.org/A082528

Sequence definitions and original conjectures are due to Benoit Cloitre
as attributed in those entries. OEIS is maintained by the OEIS Foundation.
The first two entries use different offsets, which are preserved in the
fixtures. The replay never contacts OEIS or any other external service.

LIMITATIONS OF THE NUMERICAL OUTPUT

The exact threshold algorithms support positive rational exponents.
The article's real-parameter theorem is broader than this exact-arithmetic
implementation. A decimal exponent supplied to --m is interpreted as the
corresponding exact decimal rational.

Gamma values, plot coordinates and the reported forward-path error sizes
are high-precision or machine-precision numerical diagnostics, not
interval-certified analytic bounds. The exact arithmetic checks concern
only the explicitly recorded finite ranges.

A full replay records its runtime and package versions, so verification.json
will naturally differ in those environment-dependent fields between runs.


BUILD THE ARTICLE

From the extracted package directory, run twice:
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

The document uses standard TeX Live packages and includes body.tex,
extensions.tex, computation.tex, questions.tex, bibliography.tex, and
the two table snippets in data/. Keep the supplied figures/ directory.
No downloaded bibliography or network access is required.

CLAIM BOUNDARY

The new proof establishes the real-parameter leading asymptotic, the
explicit Gamma constant, smooth-weight universality, and the full path
limit. The m=1 leading law is classical. No bounded additive error or
quantitative discrete convergence rate is claimed. See the article for
historical attribution, independent audit details, and research questions.
