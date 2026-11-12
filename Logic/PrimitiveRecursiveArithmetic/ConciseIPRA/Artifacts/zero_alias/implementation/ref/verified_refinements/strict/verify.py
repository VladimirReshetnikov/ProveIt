"""Reproduce the strict JSON checker and its exact phase refactoring."""
from pathlib import Path
import ast
import concurrent.futures
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
        tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT}

def measure(name):
    raw = (ROOT / name).read_bytes()
    tree = ast.parse(raw)
    normal = ast.unparse(tree) + "\n"
    return dict(file=name, tokens=sum(t.type not in SKIP for t in
                tokenize.generate_tokens(io.StringIO(normal).readline)),
                ast=sum(1 for _ in ast.walk(tree)), bytes=len(normal.encode()),
                sha256=hashlib.sha256(raw).hexdigest())

def main():
    old = (ROOT / "control666.py").read_text()
    expected = (old.replace("def c(g, a, k=0, v=0):", "def c(g, a, k=0):")
                .replace("not v or", "g or")
                .replace("d % 2 or v", "d % 2 or not g")
                .replace("    v = 0", "    g += [0]")
                .replace("c([0], q(), v=1)", "c([], q())"))
    if ast.dump(ast.parse(expected)) != ast.dump(ast.parse((ROOT / "checker.py").read_text())):
        raise ValueError("The candidate is not the documented phase transformation")
    metrics = [measure(n) for n in ("control666.py", "checker.py")]
    for row, wanted in zip(metrics, [(342, 391, 666), (334, 387, 654)]):
        if tuple(row[k] for k in ("tokens", "ast", "bytes")) != wanted:
            raise ValueError((row, wanted))
    tasks = []
    for group in ("proofs", "boundary"):
        for case in json.loads((ROOT / "fixtures" / group / "cases.json").read_text()):
            for name in ("control666.py", "checker.py"):
                for opt in (False, True):
                    tasks.append((group, case, name, opt))
    def run(task):
        group, case, name, opt = task
        cmd = [sys.executable, "-I", "-S", "-B"] + (["-O"] if opt else []) + [str(ROOT / name)]
        payload = (ROOT / "fixtures" / group / case["file"]).read_bytes()
        r = subprocess.run(cmd, input=payload, capture_output=True, timeout=30)
        accepted = r.returncode == 0 and r.stdout == b"ACCEPT\n"
        return dict(group=group, fixture=case["file"], checker=name, optimized=opt,
                    accepted=accepted, expected=case["expected"],
                    passed=accepted == case["expected"],
                    fixture_sha256=hashlib.sha256(payload).hexdigest())
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        checks = list(pool.map(run, tasks))
    report = dict(python=platform.python_version(), exact_phase_transform_verified=True,
                  metrics=metrics, cli_checks=len(checks),
                  failures=sum(not x["passed"] for x in checks), checks=checks)
    (ROOT / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "checks"}, indent=2))
    if report["failures"]:
        raise SystemExit(1)

if __name__ == "__main__":
    main()

