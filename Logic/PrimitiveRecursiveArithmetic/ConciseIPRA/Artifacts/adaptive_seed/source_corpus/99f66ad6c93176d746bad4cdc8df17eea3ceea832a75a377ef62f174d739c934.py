"""Reproduce finite evidence and full-module metrics, without network access."""
from pathlib import Path
import ast
import importlib.util
import json
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("inherited_measure", ROOT / "reference" / "measure.py")
measure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(measure)


def run(name, *arguments):
    result = subprocess.run([sys.executable, str(ROOT / "code" / name), *map(str, arguments)],
                            cwd=ROOT, capture_output=True, text=True)
    (ROOT / "evidence" / (Path(name).stem + "_stdout.txt")).write_text(result.stdout + result.stderr)
    if result.returncode:
        print(result.stdout + result.stderr)
        raise SystemExit(result.returncode)
    return result.stdout


def main():
    for script in ("produce_counter.py", "produce_scalar.py"):
        run(script, ROOT / "fixtures")
    for script in ("validate_counter.py", "validate_scalar.py", "validate_balanced.py", "check_scalar_arithmetic.py"):
        run(script)
    numerical = ast.literal_eval(run("check_scalar_basis.py").strip())
    (ROOT / "evidence" / "numerical_validation.json").write_text(json.dumps(numerical, indent=2) + "\n")
    names = (
        "reference/checker_tokens.py", "reference/checker_ast.py",
        "reference/checker_bytes.py", "code/kernel_scalar_boxed.py",
        "code/kernel_balanced.py",
        "code/kernel_counter.py", "code/control_counter.py",
    )
    rows = [{"file": name, **measure.metrics(ROOT / name)} for name in names]
    expected = {
        "reference/checker_tokens.py": (287, 328, 749),
        "reference/checker_ast.py": (293, 323, 893),
        "reference/checker_bytes.py": (305, 351, 738),
        "code/kernel_scalar_boxed.py": (290, 334, 685),
        "code/kernel_balanced.py": (286, 320, 736),
        "code/kernel_counter.py": (295, 339, 689),
        "code/control_counter.py": (294, 336, 706),
    }
    if sys.version_info[:2] == (3, 12):
        for row in rows:
            observed = tuple(row[k] for k in ("normalized_tokens", "ast_nodes", "normalized_bytes"))
            if observed != expected[row["file"]]:
                raise ValueError((row["file"], observed, expected[row["file"]]))
    summary = {"python": platform.python_version(), "programs": rows,
               "metric_note": "Whole modules; reference/measure.py from the pinned corpus. Exact counts may vary with Python's ast.unparse version."}
    (ROOT / "evidence" / "final_metrics.json").write_text(json.dumps(summary, indent=2) + "\n")
    validations = {}
    for name in ("counter", "scalar", "balanced"):
        data = json.loads((ROOT / "evidence" / ("implementation_" + name + "_validation.json")).read_text())
        validations[name] = {"checks": data["check_count"], "passed": data["passed"]}
    print(json.dumps({"validation": validations, "numerical": numerical,
                      "metrics": [{"file": r["file"], **{k: r[k] for k in ("normalized_tokens", "ast_nodes", "normalized_bytes")}} for r in rows]},
                     indent=2))


if __name__ == "__main__":
    main()
