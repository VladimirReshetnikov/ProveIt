"""Bounded, offline computations for packed matrices (Report 169, A261784).

Rows and columns are ordered, all are nonzero, entries are nonnegative,
and an n-row matrix has total entry sum 2*n. No permutations are factored out.
The empty matrix has count 1. Only decimal diagnostics are approximate.
"""
from collections import defaultdict
from contextlib import contextmanager
from decimal import Decimal, localcontext
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
import os
from math import comb, factorial
from pathlib import Path

MAX_COUNT_N = 800
MAX_IE_N = 100
MAX_MARKED_N = 8
MAX_ENUM_N = 4
MIN_DIGITS, MAX_DIGITS = 30, 160
ROOT = Path(__file__).resolve().parent


def bounded_int(value, name, lower, upper):
    if type(value) is not int:
        raise TypeError(f"{name} must be an integer (bool is not accepted)")
    if not lower <= value <= upper:
        raise ValueError(f"{name} must lie in [{lower}, {upper}]")
    return value


def integer_decimal(value):
    """Encode bounded nonnegative integers without changing Python's digit guard.

    Python 3.11+ may reject str(large_int) above 4300 decimal digits. Counts at
    n=800 exceed that default, so use base-10**9 chunks of at most 9 digits.
    """
    if type(value) is not int:
        raise TypeError("value must be an integer")
    if value < 0 or value.bit_length() > 65536:
        raise ValueError("value must be nonnegative and have at most 65536 bits")
    if not value:
        return "0"
    parts = []
    while value:
        value, remainder = divmod(value, 10**9)
        parts.append(remainder)
    return str(parts[-1]) + "".join(f"{part:09d}" for part in reversed(parts[:-1]))


def first_kind_row(N):
    """Unsigned Stirling numbers [N,j], using integer recurrence."""
    bounded_int(N, "N", 0, 2 * MAX_COUNT_N)
    row = [1] + [0] * N
    for k in range(1, N + 1):
        for j in range(k, 0, -1):
            row[j] = row[j - 1] + (k - 1) * row[j]
        row[0] = 0
    return row


def second_kind_table(N):
    # Only the small marked transform needs a full quadratic table.
    bounded_int(N, "N", 0, 2 * MAX_MARKED_N)
    rows = [[1]]
    for k in range(1, N + 1):
        prev = rows[-1]
        row = [0] * (k + 1)
        for j in range(1, k + 1):
            row[j] = prev[j - 1] + (j * prev[j] if j < k else 0)
        rows.append(row)
    return rows


@lru_cache(maxsize=16)
def ordered_bell_numbers(N):
    """B_N = sum binomial(N,j)*B_(N-j), 1<=j<=N; B_0=1."""
    bounded_int(N, "N", 0, 2 * MAX_COUNT_N)
    bells = [1]
    for k in range(1, N + 1):
        bells.append(sum(comb(k, j) * bells[k - j] for j in range(1, k + 1)))
    return tuple(bells)


def count_stirling(n):
    """Exact n!/(2n)! * sum_j [2n,j]{j,n}B_j, with checked division."""
    bounded_int(n, "n", 0, MAX_COUNT_N)
    if n == 0:
        return 1
    N = 2 * n
    first = first_kind_row(N)
    bells = ordered_bell_numbers(N)
    row = [1] + [0] * n
    numerator = 0
    for j in range(N + 1):
        numerator += first[j] * row[n] * bells[j]
        if j < N:
            for k in range(min(j + 1, n), 0, -1):
                row[k] = row[k - 1] + k * row[k]
            row[0] = 0
    quotient, remainder = divmod(factorial(n) * numerator, factorial(N))
    if remainder:
        raise ArithmeticError("Stirling transform unexpectedly failed integrality")
    return quotient


def count_inclusion(n):
    """Independent nonempty-column recurrence, then row inclusion-exclusion.

    For r allowed rows, a column of sum j has binomial(r+j-1,j) choices.
    A_r(0)=1; A_r(N)=sum_(j=1)^N binomial(r+j-1,j) A_r(N-j).
    Empty rows are removed by sum_r (-1)^(n-r) binomial(n,r) A_r(2n).
    This route does not use Stirling numbers or ordered Bell numbers.
    """
    bounded_int(n, "n", 0, MAX_IE_N)
    if n == 0:
        return 1
    N = 2 * n
    total = 0
    for r in range(1, n + 1):
        columns = [0] + [comb(r + j - 1, j) for j in range(1, N + 1)]
        seq = [1]
        for mass in range(1, N + 1):
            seq.append(sum(columns[j] * seq[mass - j] for j in range(1, mass + 1)))
        total += (-1) ** (n - r) * comb(n, r) * seq[N]
    return total


def _poly_mul(a, b, N):
    """Multiply polynomials in z,u, truncated only at z-degree N."""
    out = defaultdict(Fraction)
    for (za, ua), ca in a.items():
        for (zb, ub), cb in b.items():
            if za + zb <= N:
                out[za + zb, ua + ub] += ca * cb
    return {key: value for key, value in out.items() if value}


def marked_transform(n):
    """Return {(J,K): coefficient of u**J*v**K} exactly.

    Uses n! sum_(j=n)^(2n) {j,n} B_j(v)/j! [z^(2n)]w(z,u)^j,
    with w=-log(1-z)+log(1+(u-1)z^2), truncated in z.
    """
    bounded_int(n, "n", 0, MAX_MARKED_N)
    if n == 0:
        return {(0, 0): 1}
    N = 2 * n
    second = second_kind_table(N)
    w = defaultdict(Fraction)
    for z in range(1, N + 1):
        w[z, 0] += Fraction(1, z)
    for r in range(1, N // 2 + 1):
        for j in range(r + 1):
            w[2 * r, j] += Fraction((-1) ** (r + 1 + r - j) * comb(r, j), r)
    w = {key: value for key, value in w.items() if value}
    power = {(0, 0): Fraction(1)}
    out = defaultdict(Fraction)
    for j in range(1, N + 1):
        power = _poly_mul(power, w, N)
        if j < n:
            continue
        scale = Fraction(factorial(n) * second[j][n], factorial(j))
        for (mass, repeats), coefficient in power.items():
            if mass == N:
                for columns in range(1, j + 1):
                    out[repeats, columns] += (
                        scale * coefficient * factorial(columns) * second[j][columns]
                    )
    answer = {}
    for key, coefficient in out.items():
        if coefficient.denominator != 1 or coefficient < 0:
            raise ArithmeticError("Marked transform has a nonintegral or negative coefficient")
        if coefficient:
            answer[key] = coefficient.numerator
    return dict(sorted(answer.items()))


def _vectors(total, length):
    if length == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for tail in _vectors(total - first, length - 1):
                yield (first,) + tail


def marked_enumeration(n):
    """Independent finite enumeration of ordered nonzero columns.

    A state records mass, covered-row bitmask, and cells >=2. Column vectors
    with the same state are aggregated with their multiplicities; no analytic
    generating function, Stirling number, or Bell number is used.
    """
    bounded_int(n, "n", 0, MAX_ENUM_N)
    if n == 0:
        return {(0, 0): 1}
    N = 2 * n
    column_types = defaultdict(int)
    for mass in range(1, N + 1):
        for column in _vectors(mass, n):
            mask = sum((1 << r) for r, entry in enumerate(column) if entry)
            repeats = sum(entry >= 2 for entry in column)
            column_types[mass, mask, repeats] += 1
    state = {(0, 0, 0): 1}
    output = defaultdict(int)
    full_mask = (1 << n) - 1
    for columns in range(1, N + 1):
        next_state = defaultdict(int)
        for (mass, mask, repeats), count in state.items():
            for (weight, new_mask, new_repeats), multiplicity in column_types.items():
                if mass + weight <= N:
                    next_state[mass + weight, mask | new_mask, repeats + new_repeats] += (
                        count * multiplicity
                    )
        state = next_state
        for (mass, mask, repeats), count in state.items():
            if mass == N and mask == full_mask:
                output[repeats, columns] += count
    return dict(sorted(output.items()))


def marked_record(n, polynomial):
    total = sum(polynomial.values())
    if total <= 0:
        raise ValueError("Polynomial must have positive total")
    mean_j = Fraction(sum(j * c for (j, k), c in polynomial.items()), total)
    mean_k = Fraction(sum(k * c for (j, k), c in polynomial.items()), total)
    variance_k = Fraction(sum(k * k * c for (j, k), c in polynomial.items()), total) - mean_k**2
    return {
        "n": n,
        "total": integer_decimal(total),
        "terms": [{"J": j, "K": k, "count": integer_decimal(c)} for (j, k), c in sorted(polynomial.items())],
        "mean_J": str(mean_j),
        "mean_K": str(mean_k),
        "variance_K": str(variance_k),
    }


def _morse_coefficients(q, R):
    """Finite Morse/Lagrange coefficient prescription, C0 through C3.

    Arithmetic is generic: Fraction (exact rational specialization), Decimal
    (uncertified), or the optional SymPy field Q(q,R) (exact identities).
    """
    one, zero = q * 0 + 1, q * 0
    rat = lambda p, d=1: one * p / d
    N = 6

    def const(value):
        return [one * value] + [zero] * N

    def add(a, b):
        return [a[i] + b[i] for i in range(N + 1)]

    def scale(a, k):
        return [c * k for c in a]

    def mul(a, b):
        return [sum((a[j] * b[i - j] for j in range(i + 1)), zero) for i in range(N + 1)]

    def power(a, exponent):
        if a[0] != one:
            raise ArithmeticError("Power-series binomial expansion requires constant term 1")
        z = a.copy()
        z[0] = zero
        answer, term, binomial = const(1), const(1), one
        for j in range(1, N + 1):
            term = mul(term, z)
            binomial = binomial * (exponent - j + 1) / j
            answer = add(answer, scale(term, binomial))
        return answer

    a, b = q / (1 - q), (2 * q - 1) / (1 - q)
    log = [-2 * q] + [-a**k / k for k in range(1, N + 3)]
    ratio = [1 / q - 1] + [rat((-1)**k) / q for k in range(1, N + 3)]
    phase = [sum((log[j] * ratio[k-j] for j in range(k+1)), zero)
             - (zero if k == 0 else rat((-1)**(k+1), k)) for k in range(N+3)]
    # Fraction and symbolic computations must satisfy these exactly. Decimal
    # roundoff is intentionally not promoted into a symbolic correctness test.
    if not isinstance(q, Decimal) and (phase[1] != zero or 2 * phase[2] != b):
        raise ArithmeticError("Saddle normalization failed")
    S = [2 * phase[k+2] / b for k in range(N+1)]
    S[0] = one  # Algebraically 2*f_2/b=1; avoid Decimal rounding drift.
    base = const(1)
    base[1] = -a
    amplitude = mul(mul(power(base, rat(-1, 2)),
                         [(R*q)**k / factorial(k) for k in range(N+1)]),
                    [rat((-1)**k) for k in range(N+1)])
    Q = const(q)
    Q[1] = q
    Q2, Q3 = mul(Q, Q), mul(mul(Q, Q), Q)
    Q4 = mul(Q2, Q2)
    inverse = scale(power(base, rat(-1)), 1 / (1-q))
    H1 = add(add(scale(mul(Q2, inverse), rat(1, 12)), scale(Q, -R/2)),
             add(scale(Q2, -R**2/12), const(rat(-1, 12))))
    H2 = scale(Q2, -R**2/24)
    H3 = add(scale(mul(Q3, add(mul(mul(inverse, inverse), inverse), const(-1))), rat(-1, 360)),
             add(scale(Q4, R**4/1440), const(rat(1, 360))))
    P = [const(1), H1, add(H2, scale(mul(H1, H1), rat(1, 2))),
         add(add(H3, mul(H1, H2)), scale(mul(mul(H1, H1), H1), rat(1, 6)))]
    coefficients = []
    for m in range(4):
        value = zero
        for j in range(m + 1):
            k = m - j
            series = mul(mul(amplitude, P[j]), power(S, rat(-2*k-1, 2)))
            double_factorial = 1
            for odd in range(1, 2*k, 2):
                double_factorial *= odd
            value += series[2*k] * ((-1)**k * double_factorial) / b**k
        coefficients.append(value)
    return coefficients


@lru_cache(maxsize=1)
def coefficient_data():
    data = json.loads((ROOT / "frozen" / "coefficients_C0_C3.json").read_text(encoding="utf-8"))
    entries = data.get("coefficients")
    if not isinstance(entries, list) or len(entries) != 4:
        raise ValueError("Malformed frozen coefficient data")
    for j, entry in enumerate(entries):
        if entry.get("order") != j:
            raise ValueError("Coefficient order mismatch")
        bounded_int(entry.get("denominator_scale"), "denominator scale", 1, 10**9)
        bounded_int(entry.get("denominator_power"), "denominator power", 0, 9)
        for term in entry.get("numerator_terms", []):
            if not isinstance(term, list) or len(term) != 3:
                raise ValueError("Malformed numerator term")
            bounded_int(term[0], "integer coefficient", -10**9, 10**9)
            bounded_int(term[1], "q power", 0, 15)
            bounded_int(term[2], "R power", 0, 6)
        if not entry.get("numerator_terms"):
            raise ValueError("Empty numerator")
    return data


def _frozen_coefficients(q, R):
    zero = q * 0
    values = []
    for entry in coefficient_data()["coefficients"]:
        numerator = sum((c * q**i * R**j for c, i, j in entry["numerator_terms"]), zero)
        denominator = entry["denominator_scale"] * (2*q-1)**entry["denominator_power"]
        values.append(numerator / denominator)
    return values


def rational_coefficients(q, R, method="morse"):
    """Exact specializations in Q; these are not evaluations at log(2), q*."""
    if not isinstance(q, Fraction) or not isinstance(R, Fraction):
        raise TypeError("q and R must be fractions.Fraction values")
    if not Fraction(1, 2) < q < 1 or not 0 < R <= 2:
        raise ValueError("Require 1/2 < q < 1 and 0 < R <= 2")
    if max(q.numerator.bit_length(), q.denominator.bit_length(),
           R.numerator.bit_length(), R.denominator.bit_length()) > 256:
        raise ValueError("Rational inputs must have at most 256-bit numerators and denominators")
    if method == "morse":
        return _morse_coefficients(q, R)
    if method == "frozen":
        return _frozen_coefficients(q, R)
    raise ValueError("method must be 'morse' or 'frozen'")


def exact_coefficient_checks():
    checks = []
    for q in (Fraction(3, 5), Fraction(2, 3), Fraction(3, 4), Fraction(4, 5)):
        for R in (Fraction(1, 2), Fraction(2, 3), Fraction(1)):
            direct = rational_coefficients(q, R, "morse")
            frozen = rational_coefficients(q, R, "frozen")
            if direct != frozen:
                raise ArithmeticError(f"Coefficient comparison failed at q={q}, R={R}")
            checks.append({"q": str(q), "R": str(R), "C0_C3": [str(c) for c in direct]})
    return {
        "arithmetic": "exact fractions.Fraction",
        "scope": "12 exact rational specializations; not by themselves a proof of rational-function identity",
        "full_identity_command": "python verify_symbolic.py",
        "all_matches": True,
        "checks": checks,
    }


def _decimal_constants(digits):
    # The caller supplies a guarded Decimal context. No floats or mpmath.
    D = Decimal
    rho = D(2).ln()
    low, high = D(3)/4, D(7)/8
    tolerance = D(10) ** (-digits-5)
    for unused in range(4*(digits+10)):
        mid = (low+high)/2
        if -(1-mid).ln() - 2*mid > 0:
            high = mid
        else:
            low = mid
        if high-low < tolerance:
            break
    else:
        raise ArithmeticError("Decimal saddle solver did not converge")
    q = (low+high)/2
    # Quadratically convergent Gauss-Legendre algorithm for pi.
    a, b, t, p = D(1), D(1)/D(2).sqrt(), D(1)/4, D(1)
    for unused in range((digits+20).bit_length()+1):
        next_a = (a+b)/2
        b = (a*b).sqrt()
        t -= p*(a-next_a)**2
        a = next_a
        p *= 2
    pi = (a+b)**2/(4*t)
    d = 1/(rho*rho*q*(1-q))
    C = (rho*q).exp()/(4*pi*rho*(2*q-1).sqrt())
    return {"rho": rho, "q": q, "t": 2*q, "pi": pi, "C": C, "d": d}


def _inverse_errors(exact, n, constants, coefficients, digits):
    """Uncertified Lambert-core and two corrected errors at x=a_n.

    Uses Y=(log(x)-log(2*pi*C))/2, W=W_0(sqrt(d)*Y/e), v=Y/W.
    This evaluates smooth formulas; it never selects an integer inverse.
    """
    D = Decimal
    Y = (D(exact).ln() - (2*constants["pi"]*constants["C"]).ln()) / 2
    argument = constants["d"].sqrt() * Y / D(1).exp()
    if argument <= 0:
        raise ArithmeticError("Positive-real Lambert diagnostic requires a positive argument")
    W = (1+argument).ln()
    tolerance = D(10)**(-digits-10)
    for unused in range(4*(digits+10)):
        exponential = W.exp()
        correction = (W*exponential-argument)/(exponential*(W+1))
        W -= correction
        if abs(correction) < tolerance:
            break
    else:
        raise ArithmeticError("Decimal Lambert solver did not converge")
    v = Y/W
    L = 1+W
    h1 = coefficients[1]+D(1)/6
    h2 = coefficients[2]-coefficients[1]**2/2
    first = v-h1/(2*v*L)
    second = first-h2/(2*v*v*L)
    return {"core_error": v-n, "first_corrected_error": first-n,
            "second_corrected_error": second-n}


def decimal_diagnostics(indices=(10, 20, 50, 100), digits=60):
    bounded_int(digits, "digits", MIN_DIGITS, MAX_DIGITS)
    if not isinstance(indices, (list, tuple)) or not 1 <= len(indices) <= 12:
        raise ValueError("indices must be a list or tuple of 1 to 12 indices")
    for n in indices:
        bounded_int(n, "n", 1, MAX_COUNT_N)
    if len(set(indices)) != len(indices):
        raise ValueError("indices must be distinct")
    with localcontext() as ctx:
        ctx.prec = digits + 30
        constants = _decimal_constants(digits + 10)
        coefficients = _morse_coefficients(constants["q"], constants["rho"])
        frozen = _frozen_coefficients(constants["q"], constants["rho"])
        if any(abs(a-b) > Decimal(10)**(-digits-5) for a, b in zip(coefficients, frozen)):
            raise ArithmeticError("Guarded decimal coefficient cross-check failed")
        fmt = lambda value: format(value, f".{digits-1}E")
        records = []
        for n in indices:
            exact = count_stirling(n)
            leading = constants["C"] * constants["d"]**n * Decimal(factorial(n))**2 / n
            ratio = Decimal(exact) / leading
            residual = ratio - 1
            scales = []
            for order in range(1, 4):
                residual -= coefficients[order]/Decimal(n)**order
                scales.append({"retained_order": order,
                               "scaled_residual": fmt(residual*Decimal(n)**(order+1))})
            exact_text = integer_decimal(exact)
            records.append({"n": n, "exact_count": exact_text,
                            "exact_count_sha256": hashlib.sha256(exact_text.encode("ascii")).hexdigest(),
                            "normalized_ratio": fmt(ratio), "residuals": scales,
                            "inverse_errors": {key: fmt(value) for key, value in
                                _inverse_errors(exact, n, constants, coefficients, digits).items()}})
        return {
            "certification": "UNCERTIFIED numerical diagnostics: rounded Decimal arithmetic, not interval bounds",
            "display_significant_digits": digits,
            "working_precision": digits+30,
            "constants": {name: fmt(value) for name, value in constants.items()},
            "C0_C3": [fmt(value) for value in coefficients],
            "residual_definition": "n^(m+1)*(a_n/(C*d^n*(n!)^2/n)-sum_(j=0)^m C_j/n^j)",
            "inverse_scope": "Uncertified smooth Lambert-core and first/second corrected errors at x=a_n; not an exact integer inverse or ceiling rule",
            "records": records,
        }


def read_oeis_prefix():
    data = json.loads((ROOT / "frozen" / "oeis_A261784.json").read_text(encoding="utf-8"))
    if data.get("offset") != 0 or len(data.get("terms", [])) != 15:
        raise ValueError("Malformed frozen OEIS prefix")
    return data


def json_text(data):
    return json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False) + "\n"


@contextmanager
def _new_directory_handle(output):
    """Pin each POSIX directory descriptor; never follow a symlink ancestor."""
    requested = Path(output)
    if ".." in requested.parts:
        raise ValueError("Parent traversal is not permitted in output paths")
    absolute = Path(os.path.abspath(requested))
    if absolute == Path("/"):
        raise ValueError("A named output directory is required")
    for flag in ("O_NOFOLLOW", "O_DIRECTORY"):
        if not hasattr(os, flag):
            raise OSError("Safe output generation requires POSIX " + flag)
    parent_fd = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
    try:
        for part in absolute.parts[1:-1]:
            next_fd = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=parent_fd)
            os.close(parent_fd)
            parent_fd = next_fd
        os.mkdir(absolute.name, mode=0o700, dir_fd=parent_fd)
        directory_fd = os.open(absolute.name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                               dir_fd=parent_fd)
        try:
            yield directory_fd
        finally:
            os.close(directory_fd)
    finally:
        os.close(parent_fd)


def write_bundle(output, payloads):
    """Descriptor-pinned exclusive directory/files; no traversal or symlinks.

    Existing output leaves (including symlinks) are rejected. A failed write
    may leave a partial new directory; it never replaces existing files.
    """
    if any(not isinstance(name, str) or not name or "/" in name or "\\" in name
           or name in (".", "..", "manifest.json") for name in payloads):
        raise ValueError("Output names must be plain filenames; manifest.json is reserved")
    texts = {name: json_text(data) for name, data in sorted(payloads.items())}
    manifest = {"algorithm": "SHA-256", "files": {
        name: hashlib.sha256(content.encode("utf-8")).hexdigest() for name, content in texts.items()
    }}
    texts["manifest.json"] = json_text(manifest)
    with _new_directory_handle(output) as directory_fd:
        for name, content in texts.items():
            fd = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                         0o600, dir_fd=directory_fd)
            with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as stream:
                stream.write(content)


def generated_payloads(digits=60):
    receipt = read_oeis_prefix()
    counts = []
    for n, expected_text in enumerate(receipt["terms"]):
        expected = int(expected_text)
        first, second = count_stirling(n), count_inclusion(n)
        if first != expected or second != expected:
            raise ArithmeticError(f"Frozen prefix mismatch at n={n}")
        counts.append({"n": n, "count": integer_decimal(first), "stirling_matches": True,
                       "inclusion_exclusion_matches": True})
    extended = []
    for n in (20, 50, 100):
        first, second = count_stirling(n), count_inclusion(n)
        if first != second:
            raise ArithmeticError(f"Independent count mismatch at n={n}")
        extended.append({"n": n, "count": integer_decimal(first), "both_routes_match": True})
    marked = []
    for n in range(5):
        first, second = marked_transform(n), marked_enumeration(n)
        if first != second or sum(first.values()) != count_stirling(n):
            raise ArithmeticError(f"Marked polynomial mismatch at n={n}")
        record = marked_record(n, first)
        record["direct_enumeration_matches"] = True
        marked.append(record)
    return {
        "counts_exact.json": {"arithmetic": "exact Python integers", "source": receipt["url"],
                              "prefix": counts, "additional_independent_checks": extended},
        "marked_exact.json": {"arithmetic": "exact integers and fractions.Fraction", "records": marked},
        "coefficients_exact_checks.json": exact_coefficient_checks(),
        "diagnostics_uncertified.json": decimal_diagnostics(digits=digits),
    }
