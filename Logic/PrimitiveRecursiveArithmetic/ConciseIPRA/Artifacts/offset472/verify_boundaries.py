"""Reproduce the independent 521,284-case shifted-codec boundary search.

Run beside offset472.py with Python 3.12.14:

    python3 verify_boundaries.py

This is the original finite search, packaged as a standalone script. It
executes the candidate's unchanged checker definition with one available
packet for each case; its input reader and print driver are omitted. That
is equivalent to the kernel call made by the full input
[packet, [goal, 0]]. This finite check is regression evidence, not a proof
of the universal soundness or completeness theorem.
"""

import ast
import itertools
import json
from pathlib import Path
import time


ROOT = Path(__file__).resolve().parent
CANDIDATE = ROOT / "offset472.py"
RECEIPT = ROOT / "evidence" / "offset_independent_false_search.json"

# All 19 values used in the original independent search, in its original order.
VALUES = [
    0, 1, 2, 3, 4, 5, 6, 7, -1, -2,
    [], [0], [1], [4], [5], [6], [7], [0, 0], [0, 1],
]

# The four original closed canonical shifted public goals, in original order.
# 0: 0 = S0.
# 1: S0 = 0.
# 2: S0 = S(S0).
# 3: D_{x,y}(I(y,0;u.0) = I(y,0;u.S0)).
#    The dummy iterator slot shifts the D index y to raw coordinate 7.
#    The witness x is unused. The zero row is true and the successor rows
#    are false, so both the ordinary and progressive guarded readings fail.
GOALS = [
    [0, [0]],
    [[0], 0],
    [[0], [[0]]],
    [[[7, 0, 0], [7, 0, [0]]]],
]


def main():
    tree = ast.parse(CANDIDATE.read_text())
    # Execute exactly the same first two statements as the original search:
    # the standard-library import and the complete checker-lambda definition.
    if not (
        len(tree.body) >= 2
        and isinstance(tree.body[0], ast.Import)
        and isinstance(tree.body[1], ast.Assign)
        and len(tree.body[1].targets) == 1
        and isinstance(tree.body[1].targets[0], ast.Name)
        and tree.body[1].targets[0].id == "c"
    ):
        raise ValueError("Candidate layout changed; inspect the search harness.")
    namespace = {}
    exec(compile(ast.Module(tree.body[:2], []), str(CANDIDATE), "exec"), namespace)
    check = namespace["c"]
    accepted = []
    counts = {}
    started = time.time()

    for goal_index, goal in enumerate(GOALS):
        count = 0
        for packet in itertools.product(VALUES, repeat=4):
            stack = [list(packet)]
            namespace["q"] = stack.pop
            try:
                check([0], goal, 0)
            except (
                TypeError, IndexError, ValueError, ZeroDivisionError,
                RecursionError, OverflowError,
            ):
                pass
            else:
                accepted.append({"goal": goal, "packets": [list(packet)]})
                if len(accepted) >= 3:
                    break
            count += 1
        counts[str(goal_index)] = count
        if accepted:
            break

    result = {
        "cases": counts,
        "accepted_false_goals": accepted,
        "elapsed_seconds": round(time.time() - started, 2),
    }
    rendered = json.dumps(result, indent=2) + "\n"
    RECEIPT.parent.mkdir(parents=True, exist_ok=True)
    RECEIPT.write_text(rendered)
    print(rendered, end="")
    if accepted or counts != {str(i): 19 ** 4 for i in range(4)}:
        raise SystemExit("Boundary search failed or ended before all cases.")


if __name__ == "__main__":
    main()
