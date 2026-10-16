"""Delta-debug `have` statements out of a module: remove one at a time, keep the removal if
the module still elaborates without errors (no olean written; dependencies must be built).

usage: python -X utf8 prune_haves.py MODULE [START_LINE END_LINE]
Writes the pruned source back to the module file at the end (and after every success,
so an interruption loses nothing) and prints a summary.
"""
import os
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b')
GS = ROOT / 'Combinatorics/Ramsey/Lean/GowersSzemeredi'
PACKAGES = Path(r'C:\ProveIt\.lake\packages')
OUTPUT = ROOT / '.lake/build/lib/lean'
HERE = Path(__file__).resolve().parent


def other_lean_running():
    out = subprocess.run(['tasklist', '/FI', 'IMAGENAME eq lean.exe', '/FO', 'CSV', '/NH'],
                         capture_output=True, text=True).stdout
    return out.count('lean.exe')


def compiles(text, scratch):
    scratch.write_text(text, encoding='utf8', newline='\n')
    env = dict(os.environ)
    env['LEAN_PATH'] = os.pathsep.join(map(str, [OUTPUT] + sorted(PACKAGES.glob('*/.lake/build/lib/lean'))))
    while other_lean_running():
        time.sleep(20)
    r = subprocess.run(['lean', '-DautoImplicit=false', str(scratch)], cwd=ROOT, env=env,
                       capture_output=True, text=True, encoding='utf8', errors='replace')
    out = r.stdout + r.stderr
    return r.returncode == 0 and ': error' not in out


def units(lines, lo, hi):
    """(start, end) line ranges of `have` statements: the have line plus deeper-indented continuation."""
    res = []
    for i in range(lo, min(hi, len(lines))):
        m = re.match(r'^(\s*)have\b', lines[i])
        if not m:
            continue
        ind = len(m.group(1))
        j = i + 1
        while j < len(lines) and lines[j].strip() and len(lines[j]) - len(lines[j].lstrip()) > ind:
            j += 1
        res.append((i, j))
    return res


def main():
    mod = sys.argv[1]
    src = GS / f'{mod}.lean'
    lines = src.read_text(encoding='utf8').split('\n')
    lo = int(sys.argv[2]) - 1 if len(sys.argv) > 2 else 0
    hi = int(sys.argv[3]) if len(sys.argv) > 3 else len(lines)
    scratch = HERE / f'Prune_{mod}.lean'
    assert compiles('\n'.join(lines), scratch), 'baseline does not compile'
    removed = 0
    # go bottom-up so earlier line numbers stay valid
    for (a, b) in reversed(units(lines, lo, hi)):
        trial = lines[:a] + lines[b:]
        t0 = time.time()
        ok = compiles('\n'.join(trial), scratch)
        print(f'{"REMOVED" if ok else "kept   "} L{a + 1}-{b} ({time.time() - t0:.0f}s): {lines[a].strip()[:90]}', flush=True)
        if ok:
            lines = trial
            removed += b - a
            src.write_text('\n'.join(lines), encoding='utf8', newline='\n')
    print(f'removed {removed} lines', flush=True)


if __name__ == '__main__':
    main()
