"""Demonstrate and prevent the compound-progress selector regression.

This diagnostic stops after the first newly allocated branch. It does not
claim to be a complete proof of a false closed theorem. The unsafe control
is created only in memory by removing the final `== 0` restriction.
"""
import ast
from pathlib import Path


class BranchCaptured(Exception):
    pass


def inspect_branch(path, unsafe=False):
    source = Path(path).read_text()
    if unsafe:
        if source.count("len(a) % 2 == u == 0") != 1:
            raise ValueError("the protected selector was not found exactly once")
        source = source.replace("len(a) % 2 == u == 0", "len(a) % 2 == u")
    tree = ast.parse(source)
    # Import json and construct the checker function; do not run its I/O entry.
    namespace = {}
    prefix = ast.Module(body=tree.body[:2], type_ignores=[])
    exec(compile(prefix, "<selector diagnostic>", "exec"), namespace)
    checker = namespace["c"]
    packets = [[0, 0, 1, 0]]
    namespace["q"] = packets.pop

    def intercept(context, goal, floor=0, phase=0):
        if floor < 0:
            raise BranchCaptured(context[-1], goal)
        return checker(context, goal, floor, phase)

    namespace["c"] = intercept
    # A canonical closed D/D/equality formula; its outer matrix is compound.
    goal = [[[7, 0]]]
    try:
        intercept([0], goal, phase=1)
    except BranchCaptured as captured:
        hypothesis, conclusion = captured.args
        return {"hypothesis": hypothesis, "conclusion": conclusion}
    raise ValueError("the diagnostic did not reach its intended branch")


def regression(path):
    safe = inspect_branch(path)
    unsafe = inspect_branch(path, unsafe=True)
    expected_goal = [[[-1], 0]]
    if safe != {"hypothesis": [[0, 0]], "conclusion": expected_goal}:
        raise ValueError("the safe checker did not select compound case mode")
    if unsafe != {"hypothesis": [[-1, 0]], "conclusion": expected_goal}:
        raise ValueError("the negative control did not expose compound progress")
    return {"scope": "one branch of the actual checker; not a false-theorem certificate",
            "canonical_goal": [[[7, 0]]], "packet": [0, 0, 1, 0],
            "safe_case_branch": safe, "unsafe_progress_branch": unsafe,
            "passed": True}


if __name__ == "__main__":
    import json
    print(json.dumps(regression(Path(__file__).with_name("checker_strict.py")), indent=2))
