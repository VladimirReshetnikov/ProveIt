#!/usr/bin/env python3
"""Exact and high-precision experiments for dyadic-comb Fabius/Rvachev sums.

The script accompanies the report

    Dyadic-Comb Moments of the Fabius and Rvachev Functions

and implements the formulas proved there.  It deliberately avoids black-box
sampling of the Fabius function.  Dyadic values are generated from the finite
Thue--Morse/Appell convolution

  F(k/2^m) = 2^{-m(m+1)/2}/m! * sum_{a<k} tau(a) P_m(2(k-a)-1),

where tau(a)=(-1)^s_2(a), P_m(x)=E[(x-X)^m], and X has Rvachev density up.
Multiplication by the finite Thue--Morse polynomial is performed as a chain of
m sparse finite differences, reducing the cost from O(4^m) to O(m 2^m).

Outputs (written next to this script):
  generated_results.tex      exact tables used by the report
  corpus_inventory.tex       recursive inventory of the repository's .tex files
  corpus_audit.txt            keyword/heading audit of that corpus
  fractional_convergence.png numerical convergence plot

No internet access is required after the ProveIt checkout is present.
"""
from __future__ import annotations

import argparse
import hashlib
import math
import re
import subprocess
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence


# ---------------------------------------------------------------------------
# Rational Bernoulli numbers, cumulants, moments, and continuous Fabius moments
# ---------------------------------------------------------------------------

def bernoulli_numbers(nmax: int) -> list[Fraction]:
    """Return B_0,...,B_nmax with the convention B_1=-1/2."""
    b = [Fraction(0) for _ in range(nmax + 1)]
    b[0] = Fraction(1)
    for n in range(1, nmax + 1):
        b[n] = -sum(Fraction(math.comb(n + 1, k)) * b[k]
                    for k in range(n)) / Fraction(n + 1)
    return b


def bernoulli_at_one(n: int, b: Sequence[Fraction]) -> Fraction:
    """B_n(1): it equals B_n except that B_1(1)=+1/2."""
    return Fraction(1, 2) if n == 1 else b[n]


def rvachev_cumulants(nmax: int, b: Sequence[Fraction]) -> list[Fraction]:
    r"""Cumulants of X with density up.

    M(t)=E exp(tX)=prod_{nu>=1} sinh(t/2^nu)/(t/2^nu), and

      kappa_{2r} = 2^{2r-1} B_{2r}/(r(2^{2r}-1)),  kappa_{2r+1}=0.
    """
    kappa = [Fraction(0) for _ in range(nmax + 1)]
    for r in range(1, nmax // 2 + 1):
        n = 2 * r
        kappa[n] = (Fraction(2 ** (n - 1)) * b[n]
                      / Fraction(r * (2 ** n - 1)))
    return kappa


def moments_from_cumulants(kappa: Sequence[Fraction]) -> list[Fraction]:
    """Convert cumulants to raw moments using the complete Bell recurrence."""
    nmax = len(kappa) - 1
    mu = [Fraction(0) for _ in range(nmax + 1)]
    mu[0] = Fraction(1)
    for n in range(1, nmax + 1):
        mu[n] = sum(Fraction(math.comb(n - 1, k - 1))
                    * kappa[k] * mu[n - k]
                    for k in range(1, n + 1))
    return mu


def fabius_integral_moment(p: int, mu: Sequence[Fraction],
                            b: Sequence[Fraction]) -> Fraction:
    r"""I_p = integral_0^1 x^p F(x) dx.

    From the exponential generating function

      sum I_p t^p/p! = e^t/t - e^t M(t)/(e^t-1),

    one obtains

      I_p = [1 - sum_j C(p+1,j) mu_j B_{p+1-j}(1)]/(p+1).
    """
    total = sum(Fraction(math.comb(p + 1, j)) * mu[j]
                * bernoulli_at_one(p + 1 - j, b)
                for j in range(p + 2))
    return (Fraction(1) - total) / Fraction(p + 1)


def positive_half_up_moment(p: int, mu: Sequence[Fraction],
                            b: Sequence[Fraction]) -> Fraction:
    """a_p = integral_0^1 x^p up(x) dx = 1/(p+1)-I_p."""
    return Fraction(1, p + 1) - fabius_integral_moment(p, mu, b)


def moment_polynomial_value(m: int, x: int,
                            mu: Sequence[Fraction]) -> Fraction:
    r"""P_m(x)=E[(x-X)^m]; odd moments of the symmetric X vanish."""
    return sum(Fraction(math.comb(m, r)) * mu[r] * Fraction(x ** (m - r))
               for r in range(0, m + 1, 2))


# ---------------------------------------------------------------------------
# Exact dyadic values and exact comb moments
# ---------------------------------------------------------------------------

def dyadic_fabius_values_exact(m: int, mu: Sequence[Fraction]) -> list[Fraction]:
    """Return [F(k/2^m)] for k=0,...,2^m exactly.

    The Thue--Morse convolution is evaluated by multiplying its generating
    series successively by (1-z^{2^j}).  Descending in-place updates preserve
    the old coefficient at k-2^j and therefore implement each multiplication
    exactly.
    """
    if m < 0:
        raise ValueError("m must be nonnegative")
    n = 1 << m
    coeff = [Fraction(0) for _ in range(n + 1)]
    for d in range(1, n + 1):
        coeff[d] = moment_polynomial_value(m, 2 * d - 1, mu)

    for j in range(m):
        step = 1 << j
        for k in range(n, step - 1, -1):
            coeff[k] -= coeff[k - step]

    scale = Fraction(1, math.factorial(m) * 2 ** (m * (m + 1) // 2))
    values = [scale * c for c in coeff]

    # These exact assertions catch normalization, Bernoulli, or update errors.
    assert values[0] == 0
    assert values[n] == 1
    for k in range(n + 1):
        assert values[k] + values[n - k] == 1
    return values


def right_comb_exact(m: int, p: int, mu: Sequence[Fraction]) -> Fraction:
    r"""S_{m,p}=2^{-m} sum_{k=0}^{2^m}(k/2^m)^p F(k/2^m)."""
    n = 1 << m
    values = dyadic_fabius_values_exact(m, mu)
    return sum(Fraction(k ** p) * values[k] for k in range(1, n + 1)) \
           / Fraction(n ** (p + 1))


def falling_integer(p: int, r: int) -> int:
    """Falling factorial p^{underline r}; zero when r>p for p>=0."""
    if r > p:
        return 0
    ans = 1
    for j in range(r):
        ans *= p - j
    return ans


def stabilized_comb_formula(m: int, p: int, i_p: Fraction,
                            b: Sequence[Fraction]) -> Fraction:
    r"""Universal finite Euler--Maclaurin expression for an integer p."""
    n = 1 << m
    ans = i_p + Fraction(1, 2 * n)
    for q in range(1, (p + 1) // 2 + 1):
        r = 2 * q - 1
        ans += (b[2 * q] * Fraction(falling_integer(p, r), math.factorial(2 * q))
                / Fraction(n ** (2 * q)))
    return ans


def power_sum_right(m: int, p: int) -> Fraction:
    n = 1 << m
    return Fraction(sum(k ** p for k in range(1, n + 1)), n ** (p + 1))


def polynomial_multiply(a: Sequence[Fraction], b: Sequence[Fraction]) -> list[Fraction]:
    out = [Fraction(0) for _ in range(len(a) + len(b) - 1)]
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return out


def iterated_sum_reduced(m: int, p: int, order: int,
                         ordinary: Sequence[Fraction]) -> Fraction:
    r"""Normalized inclusive repeated sum at the right endpoint.

      J_h^n a(N)=h^n sum_{k=0}^N C(N-k+n-1,n-1) a_k.

    The binomial kernel is expanded as

      h^n C(N-k+n-1,n-1)
       = h/(n-1)! prod_{r=1}^{n-1}(1+rh-kh).
    """
    if order < 1:
        raise ValueError("order must be >= 1")
    h = Fraction(1, 1 << m)
    poly = [Fraction(1)]
    for r in range(1, order):
        poly = polynomial_multiply(poly, [Fraction(1) + r * h, Fraction(-1)])
    return sum(poly[j] * ordinary[p + j] for j in range(order)) \
           / Fraction(math.factorial(order - 1))


def iterated_sum_direct(m: int, p: int, order: int,
                        mu: Sequence[Fraction]) -> Fraction:
    n = 1 << m
    values = dyadic_fabius_values_exact(m, mu)
    numerator = sum(Fraction(math.comb(n - k + order - 1, order - 1))
                    * Fraction(k ** p, n ** p) * values[k]
                    for k in range(n + 1))
    return numerator / Fraction(n ** order)


# ---------------------------------------------------------------------------
# Formatting helpers
# ---------------------------------------------------------------------------

def frac_tex(x: Fraction) -> str:
    if x.denominator == 1:
        return str(x.numerator)
    sign = "-" if x < 0 else ""
    x = abs(x)
    return f"{sign}\\frac{{{x.numerator}}}{{{x.denominator}}}"


def sci_tex(x: float) -> str:
    if x == 0:
        return "0"
    return f"{x:.3e}".replace("e-", "\\times10^{-").replace("e+", "\\times10^{+") + ("}" if "e" in f"{x:.3e}" else "")


def escape_tex_text(s: str) -> str:
    repl = {
        "\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$",
        "#": r"\#", "_": r"\_", "{": r"\{", "}": r"\}",
        "~": r"\textasciitilde{}", "^": r"\textasciicircum{}",
    }
    return "".join(repl.get(ch, ch) for ch in s)


# ---------------------------------------------------------------------------
# Repository corpus inventory
# ---------------------------------------------------------------------------
KEYWORDS = [
    ("dyadic", re.compile(r"dyadic|2\^\{|2-adic", re.I)),
    ("sum", re.compile(r"summ?ation|\\sum|discrete|comb", re.I)),
    ("integral", re.compile(r"integral|\\int", re.I)),
    ("Poisson", re.compile(r"Poisson summation|Poisson formula", re.I)),
    ("Thue--Morse", re.compile(r"Thue.?Morse|Prouhet", re.I)),
    ("q-series", re.compile(r"q-binomial|q-Pochhammer|q-series", re.I)),
    ("sinc/Fourier", re.compile(r"sinc|Fourier", re.I)),
    ("Lambert-W", re.compile(r"Lambert.?W", re.I)),
    ("Bell/Bernoulli", re.compile(r"Bell polynomial|Bernoulli", re.I)),
    ("iteration", re.compile(r"iterated sum|repeated sum|discrete antiderivative", re.I)),
]


def strip_tex_heading(s: str) -> str:
    s = re.sub(r"%.*", "", s)
    s = re.sub(r"\\[A-Za-z@]+\*?(?:\[[^\]]*\])?", "", s)
    s = s.replace("{", "").replace("}", "")
    s = re.sub(r"\s+", " ", s).strip()
    return s[:100]


def corpus_inventory(repo_docs: Path, out_dir: Path) -> tuple[int, str]:
    tex_files = sorted(repo_docs.rglob("*.tex"))
    if not tex_files:
        raise FileNotFoundError(f"No .tex files found under {repo_docs}")

    try:
        commit = subprocess.check_output(
            ["git", "-C", str(repo_docs), "rev-parse", "HEAD"], text=True
        ).strip()
    except Exception:
        # repo_docs is usually below the checkout root, and git -C still works.
        commit = "unknown"

    audit_lines: list[str] = []
    rows: list[tuple[str, int, str, str]] = []
    combined_hash = hashlib.sha256()
    for path in tex_files:
        raw = path.read_bytes()
        combined_hash.update(raw)
        text = raw.decode("utf-8", errors="replace")
        rel = path.relative_to(repo_docs).as_posix()
        line_count = text.count("\n") + 1
        heading_matches = re.findall(
            r"\\(?:part|chapter|section|subsection|title)\*?\s*\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}",
            text,
        )
        heading = strip_tex_heading(heading_matches[0]) if heading_matches else "(no simple heading parsed)"
        tags = [name for name, rx in KEYWORDS if rx.search(text)]
        rows.append((rel, line_count, heading, ", ".join(tags)))
        audit_lines.append(f"FILE: {rel}\nLINES: {line_count}\nFIRST HEADING: {heading}\nTAGS: {', '.join(tags)}\n")
        for name, rx in KEYWORDS:
            hits = list(rx.finditer(text))
            if hits:
                audit_lines.append(f"  {name}: {len(hits)} lexical hits\n")
        audit_lines.append("\n")

    digest = combined_hash.hexdigest()
    (out_dir / "corpus_audit.txt").write_text(
        f"Recursive TeX corpus: {repo_docs}\n"
        f"Git commit: {commit}\n"
        f"Files: {len(tex_files)}\n"
        f"Combined SHA-256: {digest}\n\n" + "".join(audit_lines),
        encoding="utf-8",
    )

    with (out_dir / "corpus_meta.tex").open("w", encoding="utf-8") as meta:
        meta.write("% Generated by experiments.py; do not edit by hand.\n")
        meta.write(f"\\newcommand{{\\CorpusFileCount}}{{{len(tex_files)}}}\n")
        meta.write(f"\\newcommand{{\\CorpusCommit}}{{\\texttt{{{escape_tex_text(commit[:12])}}}}}\n")
        meta.write(f"\\newcommand{{\\CorpusDigest}}{{\\texttt{{{escape_tex_text(digest[:16])}}}}}\n")

    with (out_dir / "corpus_inventory.tex").open("w", encoding="utf-8") as f:
        f.write("% Generated by experiments.py; do not edit by hand.\n")
        f.write("\\begin{longtable}{@{}p{0.43\\textwidth}r p{0.41\\textwidth}@{}}\n")
        f.write("\\toprule\nRelative path & Lines & Lexical topic tags \\\\\n\\midrule\n\\endfirsthead\n")
        f.write("\\toprule\nRelative path & Lines & Lexical topic tags \\\\\n\\midrule\n\\endhead\n")
        for rel, line_count, _heading, tags in rows:
            f.write(f"\\nolinkurl{{{rel}}} & {line_count} & {escape_tex_text(tags)} \\\\\n")
        f.write("\\bottomrule\n\\end{longtable}\n")
    return len(tex_files), commit


# ---------------------------------------------------------------------------
# High-precision fractional-power experiments
# ---------------------------------------------------------------------------

def dyadic_fabius_values_mpf(m: int, mu: Sequence[Fraction], dps: int = 100):
    import mpmath as mp
    mp.mp.dps = dps
    n = 1 << m
    mu_mp = [mp.mpf(q.numerator) / q.denominator for q in mu[:m + 1]]
    coeff = [mp.mpf("0") for _ in range(n + 1)]
    for d in range(1, n + 1):
        x = mp.mpf(2 * d - 1)
        value = mp.mpf("0")
        for r in range(0, m + 1, 2):
            value += math.comb(m, r) * mu_mp[r] * x ** (m - r)
        coeff[d] = value
    for j in range(m):
        step = 1 << j
        for k in range(n, step - 1, -1):
            coeff[k] -= coeff[k - step]
    scale = mp.mpf(1) / (math.factorial(m) * mp.mpf(2) ** (m * (m + 1) // 2))
    return [c * scale for c in coeff]


def generalized_falling(alpha, r: int):
    ans = alpha * 0 + 1
    for j in range(r):
        ans *= alpha - j
    return ans


def right_comb_mpf(values, alpha):
    import mpmath as mp
    n = len(values) - 1
    h = mp.mpf(1) / n
    return h * mp.fsum(values[k] * (mp.mpf(k) / n) ** alpha
                       for k in range(1, n + 1))


def em_corrected(s, m: int, alpha, b: Sequence[Fraction], qmax: int):
    import mpmath as mp
    n = 1 << m
    h = mp.mpf(1) / n
    ans = s - h / 2
    for q in range(1, qmax + 1):
        bn = mp.mpf(b[2 * q].numerator) / b[2 * q].denominator
        ans -= bn / math.factorial(2 * q) * generalized_falling(alpha, 2 * q - 1) * h ** (2 * q)
    return ans


def generate_fractional_data(out_dir: Path, mu: Sequence[Fraction],
                             b: Sequence[Fraction]):
    """Generate a compact convergence table and one plot.

    A level-15 value, corrected through h^8, is used as the numerical reference.
    At h=2^-15 the omitted formal terms are far below the displayed precision
    for the selected exponents.  This is a numerical reference, not an input to
    any exact theorem in the report.
    """
    try:
        import mpmath as mp
    except Exception:
        return [], None
    mp.mp.dps = 90
    alphas = [mp.mpf("-3"), mp.mpf("-0.5"), mp.mpf("0.5"), mp.mpf("1.5")]
    ref_m = 15
    ref_values = dyadic_fabius_values_mpf(ref_m, mu, dps=100)
    refs = {}
    for alpha in alphas:
        s = right_comb_mpf(ref_values, alpha)
        refs[str(alpha)] = em_corrected(s, ref_m, alpha, b, 4)

    rows = []
    plot_alpha = mp.mpf("0.5")
    plot_m = list(range(3, 11))
    plot_raw, plot_e0, plot_e1 = [], [], []
    for m in range(3, 11):
        vals = dyadic_fabius_values_mpf(m, mu, dps=90)
        for alpha in alphas:
            s = right_comb_mpf(vals, alpha)
            ref = refs[str(alpha)]
            e_raw = abs(s - ref)
            e0 = abs(em_corrected(s, m, alpha, b, 0) - ref)
            e1 = abs(em_corrected(s, m, alpha, b, 1) - ref)
            if m in (4, 6, 8, 10):
                rows.append((str(alpha), m, mp.nstr(s, 16), mp.nstr(e0, 5), mp.nstr(e1, 5)))
            if alpha == plot_alpha:
                plot_raw.append(float(e_raw))
                plot_e0.append(float(e0))
                plot_e1.append(float(e1))

    plot_path = None
    try:
        import matplotlib.pyplot as plt
        fig, ax = plt.subplots(figsize=(7.1, 4.3))
        ax.semilogy(plot_m, plot_raw, marker="o", label=r"raw $S_m$")
        ax.semilogy(plot_m, plot_e0, marker="s", label=r"after subtracting $h/2$")
        ax.semilogy(plot_m, plot_e1, marker="^", label=r"after also subtracting the $h^2$ term")
        ax.set_xlabel(r"dyadic level $m$")
        ax.set_ylabel("absolute error")
        ax.set_title(r"Fractional power $\alpha=1/2$: endpoint-corrected convergence")
        ax.grid(True, which="both", linewidth=0.4)
        ax.legend()
        fig.tight_layout()
        plot_path = out_dir / "fractional_convergence.png"
        fig.savefig(plot_path, dpi=180)
        plt.close(fig)
    except Exception:
        plot_path = None
    return rows, plot_path


# ---------------------------------------------------------------------------
# TeX result generation
# ---------------------------------------------------------------------------

def generate_results(out_dir: Path, max_order: int = 20) -> None:
    b = bernoulli_numbers(max(32, max_order + 4))
    kappa = rvachev_cumulants(max(32, max_order + 4), b)
    mu = moments_from_cumulants(kappa)
    i_values = [fabius_integral_moment(p, mu, b) for p in range(max_order + 1)]

    # Exact verification of the stabilization theorem.
    stabilization_rows = []
    for p in range(0, 9):
        m = p + 1
        exact = right_comb_exact(m, p, mu)
        formula = stabilized_comb_formula(m, p, i_values[p], b)
        assert exact == formula
        # The parity extension at m=p for even p.
        if p % 2 == 0:
            exact_edge = right_comb_exact(p, p, mu)
            formula_edge = stabilized_comb_formula(p, p, i_values[p], b)
            assert exact_edge == formula_edge
        stabilization_rows.append((p, i_values[p], m, exact))

    # First alias-defect Dirichlet values D_{2r}/pi^{2r}.
    dirichlet_rows = []
    for s in (2, 4, 6, 8, 10):
        m = s - 1
        exact = right_comb_exact(m, m, mu)
        base = stabilized_comb_formula(m, m, i_values[m], b)
        defect = exact - base
        ratio = (defect * Fraction((2 * (1 << m)) ** s)
                 / Fraction(2 * math.factorial(m) * ((-1) ** (s // 2))))
        dirichlet_rows.append((s, ratio, defect))
    assert dirichlet_rows[0][1] == Fraction(1, 18)
    assert dirichlet_rows[1][1] == Fraction(23, 4050)

    # A few exact iterated-sum checks against the direct binomial kernel.
    iter_rows = []
    for m, p, order in ((4, 0, 2), (5, 1, 3), (6, 2, 4), (7, 3, 5)):
        ordinary = [right_comb_exact(m, q, mu) for q in range(p + order)]
        reduced = iterated_sum_reduced(m, p, order, ordinary)
        direct = iterated_sum_direct(m, p, order, mu)
        assert reduced == direct
        iter_rows.append((m, p, order, direct))

    fractional_rows, plot_path = generate_fractional_data(out_dir, mu, b)

    with (out_dir / "generated_results.tex").open("w", encoding="utf-8") as f:
        f.write("% Generated by experiments.py; do not edit by hand.\n")
        f.write("\\begin{table}[htbp]\n\\centering\n")
        f.write("\\caption{First continuous Fabius moments and an exact stabilized comb value.}\n")
        f.write("\\label{tab:moments}\n")
        f.write("\\begin{tabular}{rlll}\n\\toprule\n")
        f.write("$p$ & $I_p=\\int_0^1x^pF(x)\\,dx$ & guaranteed level & $S_{p+1,p}$ \\\\\n\\midrule\n")
        for p, ip, m, exact in stabilization_rows:
            f.write(f"{p} & ${frac_tex(ip)}$ & $m\\ge {m}$ & ${frac_tex(exact)}$ \\\\\n")
        f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n")

        f.write("\\begin{table}[htbp]\n\\centering\n")
        f.write("\\caption{Exact spectral Dirichlet values.  The middle entry means $D_s=(D_s/\\pi^s)\\pi^s$.}\n")
        f.write("\\label{tab:dirichlet}\n")
        f.write("\\begin{tabular}{rll}\n\\toprule\n")
        f.write("$s$ & $D_s/\\pi^s$ & level-$s-1$ first defect \\\\\n\\midrule\n")
        for s, ratio, defect in dirichlet_rows:
            f.write(f"{s} & ${frac_tex(ratio)}$ & ${frac_tex(defect)}$ \\\\\n")
        f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n")

        f.write("\\begin{table}[htbp]\n\\centering\n")
        f.write("\\caption{Exact checks of the reduction of an inclusive $n$-fold sum to ordinary comb moments.}\n")
        f.write("\\label{tab:iterated}\n")
        f.write("\\begin{tabular}{rrrl}\n\\toprule\n")
        f.write("$m$ & $p$ & $n$ & $\\mathcal J_{2^{-m}}^n[x^pF(x)](1)$ \\\\\n\\midrule\n")
        for m, p, order, value in iter_rows:
            f.write(f"{m} & {p} & {order} & ${frac_tex(value)}$ \\\\\n")
        f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n")

        if fractional_rows:
            f.write("\\begin{table}[htbp]\n\\centering\n")
            f.write("\\caption{High-precision fractional/negative-power experiment.  $E_0$ is the error after subtracting $h/2$; $E_1$ also subtracts the $B_2\\alpha h^2/2!$ term.}\n")
            f.write("\\label{tab:fractional}\n")
            f.write("\\begin{tabular}{rrrrr}\n\\toprule\n")
            f.write("$\\alpha$ & $m$ & $S_m(\\alpha)$ & $E_0$ & $E_1$ \\\\\n\\midrule\n")
            for alpha, m, sval, e0, e1 in fractional_rows:
                f.write(f"${alpha}$ & {m} & ${sval}$ & ${e0}$ & ${e1}$ \\\\\n")
            f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n")
        if plot_path:
            f.write("\\begin{figure}[htbp]\n\\centering\n")
            f.write("\\includegraphics[width=0.84\\textwidth]{fractional_convergence.png}\n")
            f.write("\\caption{The universal endpoint corrections expose the even-power convergence sequence for a nonintegral exponent.}\n")
            f.write("\\label{fig:fractional-convergence}\n\\end{figure}\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-docs", type=Path,
                        default=Path("/mnt/data/ProveIt/Analysis/FabiusFunction/docs"),
                        help="Path to the recursively audited FabiusFunction/docs tree")
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    corpus_inventory(args.repo_docs.resolve(), args.out.resolve())
    generate_results(args.out.resolve())
    print(f"Generated report data in {args.out.resolve()}")


if __name__ == "__main__":
    main()
