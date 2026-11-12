"""Reproduce metrics, checker regressions, and the scope counterexample.

This utility is not imported by any measured acceptance module.
Use CPython 3.12.14 to reproduce the normalization counts exactly.
"""
from pathlib import Path
import ast
import hashlib
import io
import json
import platform
import subprocess
import sys
import tempfile
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
EXPECTED = {
    "checker/controls/tokens248.py": (248, 277, 609),
    "checker/controls/ast270.py": (254, 270, 608),
    "checker/controls/compact479.py": (272, 304, 479),
    "checker/code/compact478.py": (271, 305, 478),
    "checker/controls/native607.py": (337, 383, 607),
    "checker/controls/strict637.py": (344, 392, 637),
}


def demand(condition, detail):
    if not condition:
        raise ValueError(detail)


def measure():
    rows = []
    for name, expected in EXPECTED.items():
        raw = (ROOT / name).read_bytes()
        normalized = ast.unparse(ast.parse(raw)) + "\n"
        actual = (
            sum(t.type not in SKIP for t in
                tokenize.generate_tokens(io.StringIO(normalized).readline)),
            sum(1 for _ in ast.walk(ast.parse(normalized))),
            len(normalized.encode()),
        )
        demand(actual == expected, (name, actual, expected))
        rows.append(dict(path=name, significant_tokens=actual[0],
                         ast_nodes=actual[1], normalized_bytes=actual[2],
                         sha256=hashlib.sha256(raw).hexdigest(),
                         normalized_sha256=hashlib.sha256(normalized.encode()).hexdigest()))
    result = dict(python=platform.python_version(), rows=rows,
                  prior_observed_envelope=[248, 270, 479],
                  new_exhibited_envelope=[248, 270, 478],
                  one_program_attains_all_coordinates=False,
                  global_minimality_claim=False)
    (ROOT / "evidence/metrics.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def execute(source, data, optimized):
    command = [sys.executable, "-I", "-S", "-B"]
    if optimized:
        command.append("-O")
    command.append(str(source))
    run = subprocess.run(command, input=json.dumps(data).encode(),
                         capture_output=True, timeout=20)
    return run.returncode == 0 and run.stdout == b"ACCEPT\n"


def counterexample():
    """Demonstrate why the compact change cannot be generalized.

    The intentionally invalid mutations exist only in a temporary directory.
    Their false acceptance is the EXPECTED outcome of this negative experiment.
    """
    attack = json.loads((ROOT / "evidence/positive_floor_attack.json").read_text())
    old_header = attack[:-1] + [attack[-1][0]]
    floor_zero = attack[:-1] + [[attack[-1][0], 0]]
    rows = []
    with tempfile.TemporaryDirectory(prefix="ipra_rejected_") as temporary:
        for name in ("native607.py", "strict637.py"):
            source = ROOT / "checker/controls" / name
            text = source.read_text()
            demand(text.count("k=0, v=0:") == 1, "unrecognized control signature")
            demand(text.count("c([0], q(), v=1)") == 1, "unrecognized root call")
            bad = text.replace("k=0, v=0:", "k, v=0:").replace(
                "c([0], q(), v=1)", "c([0], *q(), v=1)")
            temporary_source = Path(temporary) / ("INVALID_" + name)
            temporary_source.write_text(bad)
            for optimized in (False, True):
                for label, path, payload, expected in (
                    ("unchanged_control", source, old_header, False),
                    ("invalid_mutation_floor_1", temporary_source, attack, True),
                    ("invalid_mutation_floor_0", temporary_source, floor_zero, False),
                ):
                    actual = execute(path, payload, optimized)
                    demand(actual == expected, (name, label, optimized, actual))
                    rows.append(dict(control=name, experiment=label,
                                     optimized=optimized, expected_accept=expected,
                                     accepted=actual, passed=True))
    result = dict(packet_count=len(attack)-1, checks=len(rows), all_passed=True,
                  warning="False acceptance is intentional evidence AGAINST these mutations.",
                  standard_equation_values=[dict(n=n, lhs=2*n, rhs=n+n*n)
                                            for n in range(3)],
                  results=rows)
    demand(result["standard_equation_values"][-1]["lhs"] !=
           result["standard_equation_values"][-1]["rhs"], "false-goal check")
    (ROOT / "evidence/counterexample_reproduced.json").write_text(
        json.dumps(result, indent=2) + "\n")
    return result


def finite_math_examples():
    """Illustrations only. The paper's symbolic induction is the proof."""
    def select(n, a, b):
        return a if n == 0 else b

    def zero_test(n):
        return select(n, 1, 0)

    examples = []
    for n in range(1000):
        p = max(n - 1, 0)
        decomposition = select(zero_test(n), p + 1, 0)
        demand(n == decomposition, ("decomposition", n))
        demand(n == 0 or zero_test(n) == 0, ("split", n))
        if zero_test(n) == 0:
            demand(n == p + 1, ("witness", n))
        if n < 5:
            examples.append(dict(n=n, zero_test=zero_test(n), predecessor=p,
                                 decomposition=decomposition))
    point = (0, 1)
    zpoint = tuple(zero_test(x) for x in point)
    demand(point != (0, 0) and zpoint != (0, 0), "product obstruction")
    result = dict(status="finite illustrations; not a proof of induction",
                  ordinary_naturals_checked=1000, examples=examples,
                  product_counterexample=dict(n=list(point), Z_n=list(zpoint),
                                              split=False))
    (ROOT / "evidence/finite_math_examples.json").write_text(
        json.dumps(result, indent=2) + "\n")
    return result


def main():
    metrics = measure()
    run = subprocess.run([sys.executable, str(ROOT / "checker/verify.py")],
                         cwd=ROOT / "checker", capture_output=True, text=True,
                         timeout=180)
    demand(run.returncode == 0, run.stdout + run.stderr)
    checker = json.loads((ROOT / "checker/compact478_verification.json").read_text())
    demand(not checker["failures"], checker["failures"])
    attack = counterexample()
    examples = finite_math_examples()
    result = dict(python=platform.python_version(), all_passed=True,
                  measured_modules=len(metrics["rows"]),
                  compact_checker_executions=checker["executions"],
                  negative_experiment_checks=attack["checks"],
                  finite_math_examples=examples["ordinary_naturals_checked"],
                  new_exhibited_envelope=[248, 270, 478])
    (ROOT / "evidence/reproduction.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

