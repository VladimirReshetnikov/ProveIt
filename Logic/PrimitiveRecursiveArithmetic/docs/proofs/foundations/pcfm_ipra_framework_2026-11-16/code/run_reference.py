#!/usr/bin/env python3
"""Run the exact-arithmetic PCFM reference demonstrations and print JSON."""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "code"))

from reference import (  # noqa: E402
    Interval,
    backward_viability,
    check_cubic_trace,
    cubic_bisect,
    select_viable_path,
)


def main() -> None:
    cubic = cubic_bisect(Fraction(2), Interval(Fraction(0), Fraction(2)), 24)
    viability = backward_viability(
        [4, 5, 4, 3],
        good=lambda t, a: (a + t) % 2 == 0 or t == 3,
        compatible=lambda _t, a, b: abs(a - b) <= 1,
        terminal=lambda a: a == 2,
    )
    out = {
        "cubic_trace_verified": check_cubic_trace(Fraction(2), cubic),
        "cubic_steps": len(cubic) - 1,
        "cubic_final_interval": [
            str(cubic[-1].lo),
            str(cubic[-1].hi),
        ],
        "cubic_final_width": str(cubic[-1].width),
        "selected_viable_path": select_viable_path(viability),
    }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
