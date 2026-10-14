"""Run Lean's linters over modules (no olean written; dependencies must be built) and keep the
warnings.  One lean at a time, waiting for any other lean.exe on the machine.

usage: python -X utf8 lint_pass.py OUTDIR MODULE [MODULE ...]   (short names, e.g. Proofs16Lemma1)
Writes OUTDIR/<module>.txt with the messages; skips modules whose .txt is newer than the source.
"""
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b')
GS = ROOT / 'Combinatorics/Ramsey/Lean/GowersSzemeredi'
PACKAGES = Path(r'C:\ProveIt\.lake\packages')
OUTPUT = ROOT / '.lake/build/lib/lean'
OPTS = ['-DautoImplicit=false', '-Dlinter.unusedVariables=true', '-Dlinter.unusedSimpArgs=true',
        '-Dlinter.unnecessarySimpa=true', '-Dlinter.unreachableTactic=true',
        '-Dweak.linter.unusedTactic=true', '-Dlinter.unusedVariables.analyzeTactics=true']


def other_lean_running():
    out = subprocess.run(['tasklist', '/FI', 'IMAGENAME eq lean.exe', '/FO', 'CSV', '/NH'],
                         capture_output=True, text=True).stdout
    return out.count('lean.exe')


def main():
    out = Path(sys.argv[1])
    out.mkdir(exist_ok=True)
    env = dict(os.environ)
    env['LEAN_PATH'] = os.pathsep.join(map(str, [OUTPUT] + sorted(PACKAGES.glob('*/.lake/build/lib/lean'))))
    for m in sys.argv[2:]:
        src = GS / f'{m}.lean'
        dst = out / f'{m}.txt'
        if dst.exists() and dst.stat().st_mtime > src.stat().st_mtime:
            continue
        while other_lean_running():
            time.sleep(20)
        t0 = time.time()
        r = subprocess.run(['lean'] + OPTS + [str(src)], cwd=ROOT, env=env, capture_output=True,
                           text=True, encoding='utf8', errors='replace')
        msgs = (r.stdout + r.stderr)
        dst.write_text(f'# rc={r.returncode}\n' + msgs, encoding='utf8')
        print(f'{m} rc={r.returncode} {time.time() - t0:.0f}s {msgs.count("warning:")} warnings', flush=True)


main()
