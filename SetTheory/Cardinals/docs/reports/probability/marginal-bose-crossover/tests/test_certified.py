"""Check actual enclosure widths, independent formulas, and failure behavior."""

import sys
from pathlib import Path

import pytest
from flint import arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "code"))
from bose_certified import (accelerated_enclosure, critical_temperature_enclosure,
                            evaluate, mellin_enclosure)


@pytest.mark.parametrize("s", ["1", "3", "4.9"])
def test_two_independent_certified_representations(s):
    with ctx.workdps(110):
        first = mellin_enclosure(s, "1e-30", 100)
        second = accelerated_enclosure(s, "1e-35", 110)
        assert first.ball.rad() < arb("1e-30")
        assert second.ball.rad() < arb("1e-35")
        assert first.ball.overlaps(second.ball)


@pytest.mark.parametrize("s", ["1e-100", "2.5", "2.51", "5", "100", "1e100"])
def test_global_evaluator_enforces_total_radius(s):
    with ctx.workdps(110):
        result = evaluate(s, "1e-30", 110)
        assert result.ball.is_finite()
        assert result.ball > 0
        assert result.ball.rad() < arb("1e-30")


@pytest.mark.parametrize("s", ["0", "-1"])
def test_invalid_stiffness_rejected(s):
    with pytest.raises(ValueError):
        evaluate(s)


def test_insufficient_precision_is_not_silently_certified():
    with pytest.raises(ValueError, match="Increase dps"):
        evaluate("4.9", "1e-60", 20)


def test_root_enclosure_from_deliberately_imperfect_guess():
    with ctx.workdps(120):
        report = critical_temperature_enclosure("0.36", "0.01", "0.1",
                                                  "1e-40", 120)
        ball = arb(report["temperature_ball"])
        reference = arb("0.359500750128335309891857687832384873520295167")
        assert ball.contains(reference)
        assert ball.rad() < arb("0.0001")
        assert report["rounding_included"]
