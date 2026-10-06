"""Hand-transcribed typed semantic fixtures from Report147 and its exact tables.

Integers are int, rationals are Fraction. These are independent expectations,
not generated from the implementation under test. Coefficients use A/Z unless
explicitly labelled relative. Phase means beta=mu/leading_phase.
"""
from dataclasses import dataclass
from fractions import Fraction as F

PLUS_PREFIX = (1, 1, 5, 36, 490, 12729, 689896, 70223666, 13803604854,
               5567490203192, 4386006155453382, 6711625359213752077)
MINUS_PREFIX = (1, 1, 4, 35, 457, 12421, 678101, 69540142, 13730026114,
                5551573311817, 4379029522335786, 6705866900012021577)


@dataclass(frozen=True)
class TermFixture:
    beta: F
    falling_degree: int
    coefficient: F


@dataclass(frozen=True)
class SectorFixture:
    residue: int
    relative_floor: F
    absolute_floor: F
    degree_exclusive: int
    eligible_atoms: tuple
    profile_count: int
    terms: tuple


COMMON = (
    SectorFixture(0, F(7, 10), F(7, 10), 19, ((2, 1), (4, 1), (5, 1)), 14, (
        TermFixture(F(1), 0, F(1)), TermFixture(F(8, 9), 2, F(7, 6)),
        TermFixture(F(64, 81), 4, F(331, 720)), TermFixture(F(20, 27), 3, F(3, 2)),
        TermFixture(F(512, 729), 6, F(5357, 72576)))),
    SectorFixture(1, F(7, 10), F(14, 15), 23,
                  ((1, 1), (2, 1), (4, 1), (5, 1), (6, 1)), 21, (
        TermFixture(F(1), 1, F(3, 2)), TermFixture(F(8, 9), 3, F(27, 40)),
        TermFixture(F(5, 6), 2, F(1)), TermFixture(F(64, 81), 5, F(1979, 13440)),
        TermFixture(F(3, 4), 0, F(1)), TermFixture(F(20, 27), 4, F(25, 24)),
        TermFixture(F(512, 729), 7, F(223117, 13305600)))),
    SectorFixture(2, F(7, 10), F(7, 5), 21,
                  ((1, 1), (2, 1), (4, 1), (5, 1)), 17, (
        TermFixture(F(1), 0, F(1)), TermFixture(F(8, 9), 2, F(25, 24)),
        TermFixture(F(5, 6), 1, F(1)), TermFixture(F(64, 81), 4, F(1303, 5040)),
        TermFixture(F(20, 27), 3, F(7, 6)),
        TermFixture(F(512, 729), 6, F(19093, 518400)))),
)

DIFFERENCE = (
    SectorFixture(0, F(4, 9), F(4, 9), 42,
                  ((1, 1), (1, 2), (2, 1), (2, 2), (4, 1), (5, 1), (6, 1), (7, 1)),
                  3, (TermFixture(F(4, 9), 2, F(5, 2)),)),
    SectorFixture(1, F(1, 2), F(2, 3), 40,
                  ((1, 1), (1, 2), (2, 1), (2, 2), (4, 1), (5, 1), (6, 1), (7, 1)),
                  2, (TermFixture(F(1, 2), 1, F(2)),)),
    SectorFixture(2, F(1, 2), F(1), 38,
                  ((1, 1), (1, 2), (2, 1), (4, 1), (5, 1), (6, 1), (7, 1)),
                  1, (TermFixture(F(1, 2), 0, F(1)),)),
)

# Coefficient * (m-shift)_order; explicit A/L normalization checks.
FIRST_RELATIVE = ((F(7, 6), 0, 2), (F(9, 20), 1, 2), (F(25, 24), 0, 2))
SECOND_LADDER_RELATIVE = ((F(331, 720), 0, 4), (F(1979, 20160), 1, 4),
                          (F(1303, 5040), 0, 4))
DIFFERENCE_RELATIVE = ((F(5, 2), 0, 2), (F(4, 3), 0, 0), (F(1), 0, 0))
BERNOULLI_PREFIX = (F(1), F(-1, 2), F(1, 6), F(0), F(-1, 30), F(0), F(1, 42),
                   F(0), F(-1, 30), F(0), F(5, 66))
G_FIRST = (F(1, 4), F(11, 12), F(-1, 12))
