"""Exact independent audit of the Klarner-constant 4.5235 certificate.

This script is deliberately tiny and uses only Python's standard-library
``fractions.Fraction``.  Candidate discovery is outside the proof boundary:
the assertions below replay every rational inequality from scratch.
"""

from fractions import Fraction as Q


ZETA = Q(2000, 9047)
DENOMINATOR = 10_000_000
NAMES = tuple("c d e f g h p q r s t u v w x y z".split())
NUMERATORS = (
    3_482_045,
    4_310_668,
    5_751_028,
    16_014_774,
    9_499_305,
    7_394_875,
    6_515_468,
    3_748_277,
    2_390_936,
    3_084_206,
    2_902_315,
    5_050_537,
    1_238_300,
    1_015_088,
    1_664_015,
    1_375_847,
    1_132_149,
)


def bui_map(values: tuple[Q, ...]) -> tuple[Q, ...]:
    """The 17-coordinate polynomial map in Bui's Section 4."""

    c, d, e, f, g, h, p, q, r, s, t, u, v, w, x, y, z = values
    zz = ZETA * ZETA
    return (
        ZETA + ZETA * e,
        ZETA + ZETA * g,
        ZETA + ZETA * f,
        g + p,
        e + q,
        d + s,
        e * h + q * d + x * r + v * y + u * y * z,
        ZETA * g + ZETA * g * e + zz * (u + t * g + r * u),
        y + w,
        ZETA * g + ZETA * e * e + zz * t + zz * x * g + zz * y * u,
        x + v,
        d * h + s * d + y * r + w * y + u * z * z,
        ZETA * s + zz * (g * g + t * e + r * t),
        ZETA * s + zz * (e * g + x * e + y * t),
        ZETA * d + zz * (g + u),
        ZETA * c + zz * (g + t),
        ZETA * c + zz * (e + x),
    )


def main() -> None:
    values = tuple(Q(n, DENOMINATOR) for n in NUMERATORS)
    residuals = tuple(a - b for a, b in zip(values, bui_map(values)))
    g = values[NAMES.index("g")]

    assert len(values) == len(NAMES) == 17
    assert all(value >= 0 for value in values)
    assert all(residual >= 0 for residual in residuals)
    assert g < 1
    assert 1 / ZETA == Q(9047, 2000)

    print(f"zeta = {ZETA}; reciprocal = {1 / ZETA}")
    print(f"g = {g} < 1")
    for name, residual in zip(NAMES, residuals):
        print(f"{name}: {residual}")


if __name__ == "__main__":
    main()
