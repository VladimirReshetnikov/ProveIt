# Exact finite computations and reproducibility

The article supplies the analytic proofs. These programs verify bounded finite
counts and algebraic identities. The rational constant enclosures additionally
use the proved analytic tail inequalities. No receipt certifies a finite-n
remainder, a numerical onset, global novelty, or finite-input inverse rounding.

## Exact cycle-index enumeration

Write h_j = sum_(nu partitions j) p_nu/z_nu and
F = product_(j>=1) (1-h_j)^(-1), with alpha_nu = [p_nu]F.
The imported Schwob identities are

    a_n = sum_(nu partitions n) alpha_nu * r(nu),
    b_n = sum_(nu partitions n) alpha_nu^2 * z_nu,
    c_n = sum_(nu partitions n) alpha_nu^2 * (-1)^(n-length(nu)) * z_nu.

`code/exact_counts.py` multiplies finite polynomials indexed by integer
partitions. All coefficients are `fractions.Fraction`. For each cycle length l
with multiplicity m, the square-root count is

    odd l: sum_(k=0)^floor(m/2) m! l^k / ((m-2k)! 2^k k!),
    even l: zero for odd m, otherwise m! l^(m/2)/(2^(m/2)(m/2)!).

The product over lengths is r(nu). This is a square-root count, not a count of
involutions commuting with a permutation. The three weightings must produce
integers and agree with the fixed cited OEIS prefixes through n=20. A104779 and
A321652 have offset 0. A068313 has offset 1; c_0=1 is the empty-object extension.

The public cutoff is an integer 0 <= n <= 20. Partition arguments are tuples
or lists of positive integers, total weight at most 20. Booleans, floats,
invalid types, excessive length, and invalid parts are rejected before cached
helpers are reached. Polynomial construction has an explicit 3,000-monomial
budget. The analytic all-order theorem is not an unbounded executable API.

## Independent symmetric-margin enumeration

For each partition of n, a separate recursion counts symmetric nonnegative
integer matrices having those labelled row margins. It removes one specified
vertex of the least positive margin d. Entries connecting it to vertices with
equal residual degree are grouped by multiplicity; exact multinomial factors
restore all labelled assignments. Every unused unit of d is the unique diagonal
entry. Residual margins may be sorted for memoization because relabelling gives
a bijection, but the matrices themselves are never quotiented by permutations.
Zero residual margins are omitted; all-unit residual margins give the involution
number by its exact recurrence.

This method contains no cycle-index coefficient calculation or square-root
weighting. It agrees with the cycle-index values for every n from 0 through 20.
The same independent recursion checks

    2 M(2,1^(n-2)) = I_n,
    6 M(3,1^(n-3)) = I_n + 2 I_(n-3)

through the supported range. Its cache has at most 50,000 states. The companion
counts use the source identities; this public receipt does not claim an
independent matrix enumeration for those two sequences.

## Exact support-constant certificates

`code/certify_constants.py` fixes J=70, support at most 6, and 40 decimal
places. It computes C_J and the displayed low-support formulas as exact rational
numbers. Independently, it builds the entire truncated multivariate product
product_(2<=j<=70)(1-d_j)^(-1) over the same rational field and checks H_0=1,
H_1=H_2=0 and H_3,...,H_6 against those formulas. This checks repeated powers
from the same factor, not just products from distinct factors. It also verifies
the companion low-support formulas for both signs directly from the extracted
q_rho coefficients.

The error bounds are those proved in the article:

    0 <= C-C_J <= 6(J+2)/((J+1)(J+1)!),
    0 <= H_s-H_(s,J) <= 24 s R_s^* 4^s (J+1)^s/(J+1)!.

The program computes R_s^* by finite partition enumeration. Exact integer
division rounds the lower endpoint downward and the finite sum plus tail bound
upward. Each resulting interval has width exactly 10^-40. Only the small decimal
endpoints are serialized: large intermediate rational numerators and
denominators are never converted to decimal strings.

## Symbolic saddle, shifts, composition, and inverse

`code/symbolic_coefficients.py` implements the finite Gaussian-polynomial saddle
recursion and checks its coefficients exactly in SymPy. Conversion through the
specified order yields the involution logarithmic coefficients and their
multiplicative exponential. It then verifies the generic fixed-shift ratio,
the H_3,...,H_6 composition, and the corresponding logarithmic correction,
including the -H_3^2/2 term. Formal inverse substitution verifies the displayed
centered and uncentered inverse coefficients. Companion factorial-shift and
logarithmic conversions are checked separately.

All orders and symbols are fixed by the program. It accepts no configurable
symbolic expression or expansion order and performs no numerical fitting.
These exact cancellations are not a proof of saddle localization, integrated
Taylor remainders, asymptotic inversion error, or integer rounding. Those
arguments, including their explicit limitations, belong to the article.

## Separate floating-point diagnostics

`code/diagnostics.py` runs at 100-digit mpmath working precision, with fixed
product cutoff J=80 and fixed involution test indices 100, 1000, and 10000.
Exact involution integers are computed internally without decimal serialization.
It prints scaled asymptotic residuals and a centered inverse error. It also
shows the low-n Kostka ratios at n=10,15,20 from the exact-count fixture.
These are illustrative floating-point outputs, not directed intervals or one
of the four exact/guard receipts. No finite-n bound or unconditional inverse
rounding is inferred from agreement at these test points.

## Exact Gaussian-sector identities and separate quadratures

The symbolic checker additionally constructs the shifted Gaussian moment
recursion at fixed order ten, independently of the Cauchy-saddle recursion.
It verifies coefficient parity between the two half axes, equality with the
involution coefficients, and the generic Kostka composition through order six.
These rational identities belong in the exact symbolic receipt.

`code/sector_diagnostics.py` is intentionally separate. At 80-digit working
precision it numerically integrates the two Gaussian half axes for n=0,...,12,
checks their involution moment sum, and combines exact finite cycle-index
support weights with those quadratures. It also evaluates normalized half-axis
integrals at the fixed n values 100, 1000, and 10000 for both signs. Public
quadrature arguments reject all other large-n indices, signs other than -1 or
1, booleans, and floats. The diagnostic tolerances are floating-point checks,
not rigorous error bounds. These outputs do not enter the frozen exact receipts
or imply exponential accuracy after a fixed dominant-sector truncation.

## Filesystem and optimization safety

Every public checker writes to stdout unless an explicitly supported `--output`
is requested. Output files and directories must be new and outside the source
package; existing paths, missing parents, live or dangling symlink ancestors,
dot/dot-dot components, and backslashes are rejected. Final creation is
exclusive. Guards are explicit exceptions and remain active under `python -O`.
The test suite rejects unsupported numeric types even after caches are warmed.
The integer-to-decimal conversion cap is 640 digits and is never disabled.
Every Python child receives `-B`, `PYTHONDONTWRITEBYTECODE=1`, deterministic hash
settings, and `PYTHONINTMAXSTRDIGITS=640`. Ambient `PYTHONOPTIMIZE` is
cleared so explicit normal and optimized replay modes cannot collapse together.

The build checks every source hash, required package file, source directory,
and source type. It compares fresh deterministic receipts with frozen bytes;
it cannot silently repair a mismatch. Source files are hashed again after the
build and ZIP assembly. TeX compilation uses disposable copies, private format
and cache directories, and explicit `-no-shell-escape` for both format creation
and every document pass. TeX input/output restrictions are enabled. Layout and
reference warnings cause failure. The reference PDF must be reproduced exactly
on the installed toolchain; a mismatch is reported rather than overwritten.

## Actual-ZIP replay

`code/reproduce_zip.py` first validates the actual input ZIP. It permits at most
500 regular stored members and 32 MiB of uncompressed contents (33 MiB archive
size), with the fixed root directory, timestamp, regular-file mode, and no
extra fields, member comments, or archive comment. It rejects duplicate paths,
traversal, symlinks, compressed members, and unexpected metadata. Before running
any code it requires every member byte to agree with this trusted source
package.

Two separate extractions then run the complete build, one with ordinary Python
and one with `-O`. Each source tree must remain unchanged; each rebuilt ZIP must
match all member bytes and metadata and the complete original archive bytes.
The PDFs, all four receipts, and build-check records must also be byte-identical.
The original trusted tree and input archive are checked again at the end.
This is a bounded integrity/reproducibility workflow, not a general sandbox for
arbitrary archives or protection against hostile concurrent filesystem changes.
