"""Drive drop_hyp.py over a list of `MODULE LEMMA VAR...` lines; build after each, revert on failure.
usage: python -X utf8 drop_hyps_all.py candidates.txt   -> appends results to drop_hyps.log"""
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
log = open(HERE / 'drop_hyps.log', 'a', encoding='utf8')


def run(args):
    return subprocess.run([sys.executable, '-X', 'utf8'] + args, cwd=HERE, capture_output=True, text=True,
                          encoding='utf8', errors='replace')


for line in open(sys.argv[1], encoding='utf8'):
    parts = line.split()
    if not parts:
        continue
    snap = {f: f.read_text(encoding='utf8') for f in GS.glob('*.lean')}
    r = run(['drop_hyp.py'] + parts)
    out = (r.stdout + r.stderr).strip()
    if r.returncode != 0 or not out or out.startswith('SKIP'):
        log.write(f'{" ".join(parts)}: {out}\n')
        log.flush()
        continue
    mods = out.split()
    b = run(['heal_build.py', '5'] + mods)
    ok = 'SUCCESS' in b.stdout
    if not ok:
        restored = []
        for f, t in snap.items():
            if f.read_text(encoding='utf8') != t:
                f.write_text(t, encoding='utf8', newline='\n')
                restored.append(f.stem)
        # oleans built from the reverted sources must be rebuilt, or later attempts see them
        for m in restored:
            run(['heal_build.py', '3', m])
        tail = b.stdout.strip().splitlines()[-3:]
        log.write(f'{" ".join(parts)}: REVERTED ({" | ".join(tail)[:300]})\n')
    else:
        log.write(f'{" ".join(parts)}: OK {" ".join(mods)}\n')
    log.flush()
    print(parts[1], 'OK' if ok else 'REVERTED', flush=True)
