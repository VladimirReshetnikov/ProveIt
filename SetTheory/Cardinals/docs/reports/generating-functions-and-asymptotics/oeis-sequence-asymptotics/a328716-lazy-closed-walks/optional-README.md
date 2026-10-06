# Optional CAS and high-precision diagnostics

The complete core verification and PDF/ZIP builder use only the Python standard
library. These independent original-method cross-checks additionally require
SymPy 1.14.0 and mpmath 1.3.0 (see requirements.txt). They are not imported or run
by the core build. Install dependencies only in an environment of your choosing.

From the package root:

```
python -B optional/check_walks.py --compare
python -B optional/independent_check.py --compare
python -B optional/check_walks.py --compare --output /tmp/new-walk-checks.json
python -B optional/independent_check.py --compare --output /tmp/new-independent-checks.json
```

With no output argument, each script prints JSON to stdout and writes no file.
Output files must be new and outside the package; parents must exist and cannot
be symlinks. Existing files are never replaced. --compare checks the computed
object against its bundled reference in data/ (not against a hardcoded external
workspace). Script checks remain active under optimized Python.

check_walks.py computes exact binomial-convolution counts through n=161,
partition-indexed saddle corrections through order three, Bessel constants,
marked PGF and zero-step total-variation diagnostics, and occupation moments.
independent_check.py uses differentiated ODE raw moments, a formal exponential
recurrence, nonempty-coordinate joint counts, and an independent rational
Riccati recurrence. Its complex-amplitude zero and joint characteristic-function
checks use mpmath and are deliberately optional.

The stored decimals and finite-n trends are diagnostics, not interval
certificates or proofs of remainder bounds. Different dependency versions may
print mathematically equivalent expressions differently and fail the literal
--compare test; inspect any difference rather than overwriting references.
