# Report 229: public verification code

This directory is self-contained. It neither imports another report's code nor
needs any files outside this public package. Run the commands below from the
package directory. Python 3.11 or newer is recommended. The required finite
checks and numerical helper use only the Python standard library. The optional
symbolic certificate requires SymPy (tested with SymPy 1.14.0).

## Reproduce the included results

Keep the bundled test fixtures unchanged. In a POSIX shell, create a new
external output directory and run:

```sh
OUT="$(mktemp -d "${TMPDIR:-/tmp}/report229-checks.XXXXXXXX")"
python -B code/reproduce.py --output "$OUT/exact_checks.json"
python -B -O code/reproduce.py --output "$OUT/exact_checks_optimized.json"
python -B code/check_guards.py --output "$OUT/guard_checks.json"
python -B code/numerics.py --output "$OUT/numeric_checks.json"
python -B code/check_poles.py --output "$OUT/pole_checks.json"
```

The last command requires the optional dependency. Every command prints its JSON
result to standard output and writes a file only when `--output` is given. The
`-B` option avoids bytecode-cache writes. You can omit `--output` entirely to use
standard output without creating a result file.

Output directories must already exist, and each output filename must be new.
Existing regular files and live or dangling final-component symlinks are
rejected with exit code 2. An early check rejects them before computation or
optional imports; the actual write also uses exclusive `open('x')`, protecting
against a target appearing after that early check. Failed computations create
no output file. Repeating the commands requires a new output directory or new
filenames; the tools never replace the included fixtures.

Other failures raise an explicit exception or exit nonzero; correctness and
resource guards never depend on Python assertions. Successful exact-check
output is identical with and without `-O`.

A quick smaller run is:

```sh
python -B code/reproduce.py --n 24 --k 8
```

Changing `--n` or `--k` changes the main sector/deficit range only. The standard
root-tail checks (degree 40, q=0,...,6) and literal enumeration (size 12) still run.
No timings, random seeds, machine paths, or timestamps enter recorded outputs.
The default full exact run takes roughly 15 seconds on a typical modern CPU;
machine-dependent runtime is not a result of the test.

## Files and independent constructions

- `third_sector.py`: exact integer series arithmetic and verification functions
- `output_json.py`: early output checks and exclusive JSON-file creation
- `reproduce.py`: main exact verification entry point
- `check_guards.py`: resource/input/integrity guard tests in two fresh Python
  processes, one normal and one optimized; also tests rejected CLI arguments
- `check_poles.py`: optional exact symbolic normal-form and Laurent-pole checks
- `numerics.py`: explicitly uncertified finite-tail decimal constants

`rooted_counts(n)` generates ordinary rooted, unlabeled, nonplane tree counts
from successive binomial factors in the rooted-tree Euler product. The tree
size recursion is triangular: at weight s, the preceding forest coefficient
gives r_s, which supplies the next factor `(1-z^s)^(-r_s)`.

`universal_series(n)` builds H, J2, J3 and the marked derivative J3v directly
from their products. It constructs B using the original positive formula

    B = z J2 G/(1-z) + (1+z) F^2/(1-z)
        + z R G ((F^2-F(z^2))/2 + z F^2/(1-z))

It then computes a, D, c, E2(D), E3(D), U, V and W from the formulas in the
report. All divisions by 2 or 6 are checked for exact integrality. The fact that
D has one weight-zero type is retained, including in its substitutions D(z^j).
The alternative B identity and the relations between U,V and the all-size
layers H0,K are additional internal consistency checks, not their definitions.

`bounded_counts(n,k)` independently counts maximum outdegree at most k via the
cycle-index recurrence

    d Z_d = sum_(j=1)^d A(z^j) Z_(d-j)

solved in increasing tree size. It does not reuse the unrestricted Euler-product
construction. Subtracting counts for caps k and k-1 yields T(N,k). Subtracting
the cap-(k-1) counts from unrestricted counts yields delta_k. The default run
compares the closed forms with this independent construction in:

- 1,536 third-sector cases, N <= 192 and k <= 64
- 7,840 all-size deficit coefficients, including degree zero, N <= min(192,4k)
- 47 first-boundary cases, residual -6 for k=1 and -7 for k=2,...,47

It also records U,V coefficients, the first negative W coefficient `(13,-7692)`,
and bounded counts at the chosen largest size. These finite tests corroborate
the formulas and their implementation; they do not prove an infinite theorem.

`check_root_tails()` independently constructs unrestricted root forests by the
cycle-index recurrence and the bivariate J3 by binomial factors. It constructs
the entire displayed nonnegative remainder through degree 40, using

    z^(3q+1) sum_(ell,t>=1) z^(2ell+t) (1+...+z^(ell-1))
       sum_(b>=q+ell+t+2) (b-q-ell-t-1) [v^b] J3(z,v)

and compares it coefficient by coefficient with the exact root tail minus its
three-layer approximation. It also checks nonnegativity, valuation 4q+8, and
leading coefficient binomial(q+7,3). This yields 287 coefficient comparisons for
q=0,...,6. Both the specialization J3(z,1) and the component derivative J3v are
cross-checked against the bivariate product.

`check_literal_trees()` generates actual canonical trees as sorted tuples of
child type IDs, with no generating-function formula used for enumeration. It
checks uniqueness and maximum outdegree, enumerating 7,813 types through size
12, and makes 144 bounded-cycle comparisons. The unrestricted size counts are
cross-checked too.

## Limits and guard behavior

The main exact cutoff is 1 <= N <= 256; the outdegree cap is 0 <= k <= 80
(`check_exact` requires k_max >= 1). Boolean and noninteger inputs are rejected.
The unrestricted rooted-count helper allows 0 <= n <= 512, accommodating the
three shifted products and the separate finite-tail numerical calculation.
The literal enumeration is limited to size 12. Root-tail verification accepts
8 <= N <= 64 and requires 0 <= q_max <= floor((N-8)/4), so every requested
leading remainder term is visible. Numeric tails are limited to 32..480 and
working precision to 40..200 decimal digits. These bounds limit accidental
resource use, rather than expressing mathematical restrictions.

`check_guards.py` exercises, in each optimization mode:

- 37 rejected API inputs/integrity failures and five valid edge cases
- Seven rejected CLI argument combinations
- Twelve output-path rejection cases: regular file, live symlink and dangling
  symlink for each of the four CLI tools, with preservation checks
- Three additional direct checks of final exclusive creation, bypassing the
  early path check to model a filename appearing after preflight
- Two failed-computation checks confirming that no output file is left behind

The 12 CLI output-rejection tests disable site packages with `-S`, so they do not
require SymPy even when checking `check_poles.py`. The guard suite uses temporary
directories and requires a platform that permits filesystem symlinks. It
confirms that explicit checks remain effective under `python -O`. Normal inputs
remain subject to the same bounds when the entire public build runs under `-O`.

## Symbolic and numerical scope

`check_poles.py` starts from the positive B formula and verifies the displayed
normal form for Y. It derives the corrected tau coefficient, checks the inverse
G jet and the implicit odd coefficient, and proves both missing even poles
vanish in each contributing group. It checks the leading U pole and the
subleading U pole identity. W and the remaining simple-pole term cannot affect
these cancellations. The certificate is exact symbolic algebra; its finite
local expansion is not a proof of global analytic continuation.

`numerics.py` constructs the analytic q>=2 tails from integer rooted counts,
solves the finite-tail singularity equation by Decimal Newton iteration, and
computes pi by the arithmetic-geometric-mean algorithm. Defaults are 360 tail
coefficients and 70 working decimal digits. It includes rho, beta, C, J3(rho),
tau, the leading amplitudes A_U and A_V, and subleading diagnostic constants.
The numeric JSON key `eta` is the article's zeta: the analytic-prefactor s^2
coefficient in A(rho(1-s^2))/A(rho). It is distinct from tau, the s^3 coefficient
of 1-R.
The digits are expressly uncertified: finite cutoffs, high precision, a small
Newton residual, or agreement after a larger run do not provide interval error
bounds. Numeric output is separate from the required exact theorem checks.
