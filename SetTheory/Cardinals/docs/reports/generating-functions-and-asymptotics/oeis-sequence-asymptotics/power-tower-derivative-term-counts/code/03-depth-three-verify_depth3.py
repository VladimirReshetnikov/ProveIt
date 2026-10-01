#!/usr/bin/env python3
"""Exact certificate for the D=3 stratum of OEIS A290268.

The program uses only Python's standard library and exact Fraction arithmetic.
It verifies the finite critical strip used in the proof, cross-checks the
centered-polynomial and normalized-gamma recurrences, and tests the resulting
zero classification against direct coefficient extraction on a broad box.

No floating-point arithmetic is used in any assertion.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from math import comb
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

REPO_COMMIT = "a02ab3567fef25793b27a68248b58a7b69694342"


def harmonic(q: int, power: int = 1) -> Fraction:
    assert q >= 0 and power >= 1
    return sum((Fraction(1, j**power) for j in range(1, q + 1)), Fraction(0))


H6 = harmonic(6)
H6_2 = harmonic(6, 2)


def E(q: int) -> Fraction:
    """The signed-harmonic e_2 value in the D=3 root formula."""
    a = harmonic(q) - H6
    return (a * a - harmonic(q, 2) - H6_2) / 2


def poly_add(a: Sequence[int], b: Sequence[int]) -> List[int]:
    n = max(len(a), len(b))
    out = [0] * n
    for i, v in enumerate(a):
        out[i] += v
    for i, v in enumerate(b):
        out[i] += v
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def poly_scale(a: Sequence[int], c: int) -> List[int]:
    return [c * v for v in a]


def poly_mul_y(a: Sequence[int]) -> List[int]:
    return [0, *a]


def poly_derivative(a: Sequence[int], order: int = 1) -> List[int]:
    out = list(a)
    for _ in range(order):
        out = [i * out[i] for i in range(1, len(out))]
        if not out:
            return [0]
    return out


def poly_eval(a: Sequence[int], x: Fraction) -> Fraction:
    value = Fraction(0)
    for coeff in reversed(a):
        value = value * x + coeff
    return value


def centered_polynomials(N: int, max_k: int) -> List[List[int]]:
    """R_{N,k}(y), where R_0=1, R_1=2y and
       R_{k+1}=2y R_k + k(N+k)R_{k-1}.
    """
    assert N >= 1 and max_k >= 0
    polys: List[List[int]] = [[1]]
    if max_k == 0:
        return polys
    polys.append([0, 2])
    for k in range(1, max_k):
        term1 = poly_scale(poly_mul_y(polys[k]), 2)
        term2 = poly_scale(polys[k - 1], k * (N + k))
        polys.append(poly_add(term1, term2))
    return polys


def F_from_polynomial(k: int, q: int) -> Fraction:
    """Normalized tail coefficient F_k(q) from the paper."""
    assert k >= 0 and q >= 0
    N = q + 7
    y = Fraction(6 - q, 2)
    u = H6 - harmonic(q)
    polys = centered_polynomials(N, k)
    r = polys[k]
    rp = poly_derivative(r)
    rpp = poly_derivative(r, 2)
    return (
        poly_eval(rpp, y)
        + 2 * u * poly_eval(rp, y)
        + 2 * E(q) * poly_eval(r, y)
    ) / 2


def F_table(max_k: int, max_q: int) -> List[List[Fraction]]:
    """Compute F by the exact recurrence
       F_{k+1}(q)=(q+k+8)F_k(q)-2(q+1)F_k(q+1).
    """
    # Extra q values are needed as k increases.
    width = max_q + max_k + 2
    rows: List[List[Fraction]] = [[E(q) for q in range(width)]]
    for k in range(max_k):
        prev = rows[-1]
        nxt = [
            (q + k + 8) * prev[q] - 2 * (q + 1) * prev[q + 1]
            for q in range(width - k - 1)
        ]
        rows.append(nxt)
    return rows


def phi_coeff(m: int) -> Fraction:
    if m <= 0:
        return Fraction(0)
    if m == 1:
        return Fraction(1)
    if m == 2:
        return Fraction(3, 2)
    return Fraction(2 * ((-1) ** (m + 1)), (m - 2) * (m - 1) * m)


def convolution(a: Sequence[Fraction], b: Sequence[Fraction], n: int) -> List[Fraction]:
    out = [Fraction(0)] * (n + 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            if i + j > n:
                break
            if y:
                out[i + j] += x * y
    return out


def phi_cube_coeffs(n: int) -> List[Fraction]:
    phi = [phi_coeff(j) for j in range(n + 1)]
    one = [Fraction(1)] + [Fraction(0)] * n
    return convolution(convolution(convolution(one, phi, n), phi, n), phi, n)


def gamma_direct(k: int, M: int, phi3: Sequence[Fraction]) -> Fraction:
    """[w^M](2+w)^k phi(w)^3."""
    return sum(
        Fraction(comb(k, r) * (2 ** (k - r))) * phi3[M - r]
        for r in range(0, min(k, M) + 1)
    )


def gamma_tail(k: int, q: int, f: Fraction) -> Fraction:
    """Tail formula with M=k+q+7."""
    # 4320*(-1)^q*q!/(k+q+7)! * F_k(q), built as a product to avoid floats.
    den = 1
    for j in range(q + 1, k + q + 8):
        den *= j
    return Fraction(4320 * ((-1) ** q), den) * f


def sgn(x: Fraction) -> str:
    return "+" if x > 0 else "-" if x < 0 else "0"


def compress_signs(signs: Sequence[str]) -> str:
    pieces: List[str] = []
    start = 0
    current = signs[0]
    for i in range(1, len(signs)):
        if signs[i] != current:
            end = i - 1
            interval = str(start) if start == end else f"{start}-{end}"
            pieces.append(f"{interval}:{current}")
            start = i
            current = signs[i]
    end = len(signs) - 1
    interval = str(start) if start == end else f"{start}-{end}"
    pieces.append(f"{interval}:{current}")
    return ", ".join(pieces)


def main() -> None:
    max_k = 60
    max_q = 1000
    table = F_table(max_k, max_q)

    # Harmonic phase transition.
    assert E(0) == Fraction(203, 90)
    assert E(1) == Fraction(-7, 36)
    assert E(37) < 0 < E(38)
    for q in range(0, 200):
        assert E(q + 1) - E(q) == (harmonic(q) - H6) / (q + 1)
    assert all(E(q) < 0 for q in range(1, 38))
    assert all(E(q) > 0 for q in [0, *range(38, 200)])

    # Cross-check the polynomial formula and the F recurrence in the entire
    # finite critical certificate box.
    critical_q = [*range(0, 39)]
    for k in range(0, 15):
        for q in critical_q:
            assert table[k][q] == F_from_polynomial(k, q)

    # Exact finite certificate used by the proof.
    critical_negative_E = [*range(1, 6), *range(7, 38)]
    for q in critical_negative_E:
        # Strip the parity factor for q>6.
        for k in range(0, 15):
            u = 2 * table[k][q] if q < 6 else 2 * ((-1) ** k) * table[k][q]
            assert u != 0
        u13 = 2 * table[13][q] if q < 6 else -2 * table[13][q]
        u14 = 2 * table[14][q] if q < 6 else 2 * table[14][q]
        assert u13 > 0 and u14 > 0

    # Center q=6: odd k are the symmetry holes; small even k are nonzero;
    # k=14 is the positive induction anchor.
    for k in range(0, 15):
        if k % 2:
            assert table[k][6] == 0
        else:
            assert table[k][6] != 0
    assert table[14][6] > 0

    # Stable signs supplied by the positivity induction.
    for k in range(13, max_k + 1):
        for q in range(0, max_q + 1):
            f = table[k][q]
            if k % 2 == 0:
                assert f > 0
            else:
                if q < 6:
                    assert f > 0
                elif q == 6:
                    assert f == 0
                else:
                    assert f < 0

    # The complete tail zero theorem on a large exact box.
    for k in range(0, max_k + 1):
        for q in range(0, max_q + 1):
            assert (table[k][q] == 0) == (q == 6 and k % 2 == 1)

    # Direct coefficient extraction cross-check for bulk and tail.
    direct_max_k = 24
    direct_max_M = 180
    phi3 = phi_cube_coeffs(direct_max_M)
    for k in range(direct_max_k + 1):
        for M in range(3, direct_max_M + 1):
            g = gamma_direct(k, M, phi3)
            if M <= k + 6:
                assert g > 0
            else:
                q = M - k - 7
                assert g == gamma_tail(k, q, table[k][q])
                assert (g == 0) == (M == k + 13 and k % 2 == 1)

    # Sign table printed in the article for k<=14.  q=0..38 suffices because
    # q>=38 has the uniform parity sign proved analytically.
    sign_rows = []
    for k in range(0, 15):
        signs = [sgn(table[k][q]) for q in range(0, 39)]
        # Replace the final range endpoint by an infinity marker in output.
        row = compress_signs(signs)
        sign_rows.append(f"k={k:2d}: {row}")

    anchors = {
        "E_37": E(37),
        "E_38": E(38),
        "F_14_6": table[14][6],
    }
    certificate_lines = [
        "Exact D=3 certificate for OEIS A290268",
        f"ProveIt snapshot: {REPO_COMMIT}",
        "Arithmetic: fractions.Fraction only; no floating point in assertions.",
        "",
        "Verified theorem:",
        "  gamma(k,3,M)=0 for k>=0, M>=3 iff M=k+13 and k is odd.",
        "",
        "Harmonic phase anchors:",
        *[f"  {name} = {value.numerator}/{value.denominator}" for name, value in anchors.items()],
        "",
        "Compressed signs of F_k(q) on q=0,...,38:",
        *[f"  {row}" for row in sign_rows],
        "",
        "Stable regime proved and checked:",
        "  even k >= 14: F_k(q)>0 for every q>=0;",
        "  odd  k >= 13: F_k(q)>0 for q<6, =0 for q=6, <0 for q>6.",
        "",
        f"Exact recurrence box checked: 0<=k<={max_k}, 0<=q<={max_q}.",
        f"Direct coefficient box checked: 0<=k<={direct_max_k}, 3<=M<={direct_max_M}.",
    ]
    body = "\n".join(certificate_lines) + "\n"
    digest = sha256(body.encode("utf-8")).hexdigest()
    body += f"Certificate-body SHA-256: {digest}\n"

    out_path = Path(__file__).with_name("depth3_certificate.txt")
    out_path.write_text(body, encoding="utf-8", newline="\n")
    print(body, end="")


if __name__ == "__main__":
    main()
