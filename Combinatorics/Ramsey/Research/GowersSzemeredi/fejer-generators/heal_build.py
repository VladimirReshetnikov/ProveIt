"""Trust-build targets, healing stale dependency oleans on demand.

usage: python -X utf8 heal_build.py MAX_ROUNDS TARGET [TARGET ...]
Each round runs build_trust.py on (healed modules + targets). On
`Unknown identifier X` / `unknown constant X` it adds the module defining X;
on `environment already contains 'N' from M` it adds every stale importer
on the path, i.e. the module named in `import M' failed`. Stops on success,
on a failure it cannot attribute, or after MAX_ROUNDS.
"""
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')


def defining_module(name):
    short = name.split('.')[-1]
    pat = re.compile(r'^(?:theorem|lemma|def|abbrev|structure|instance|noncomputable def) ' + re.escape(short) + r'\b', re.M)
    hits = [f.stem for f in GS.glob('*.lean') if pat.search(f.read_text(encoding='utf8'))]
    return hits


def main():
    rounds = int(sys.argv[1])
    targets = ['GowersSzemeredi.' + t.split('.')[-1] for t in sys.argv[2:]]
    healed = []
    for r in range(rounds):
        args = healed + targets
        print(f'round {r}: {len(healed)} healed', flush=True)
        out = subprocess.run([sys.executable, '-X', 'utf8', str(HERE / 'build_trust.py')] + args,
                             capture_output=True, text=True, encoding='utf8', errors='replace')
        log = out.stdout + out.stderr
        (HERE / f'heal_round{r}.log').write_text(log, encoding='utf8')
        for l in log.splitlines():
            if 'Checking' in l or ' ok ' in l or 'FAILED' in l:
                print('  ' + l, flush=True)
        if out.returncode == 0:
            print('SUCCESS', flush=True)
            return
        new = []
        for m in re.finditer(r"[Uu]nknown (?:identifier|constant) `?'?([\w.']+)", log):
            for mod in defining_module(m.group(1)):
                new.append('GowersSzemeredi.' + mod)
        for m in re.finditer(r"import GowersSzemeredi\.(\w+) failed, environment already contains '([\w.']+)' from GowersSzemeredi\.(\w+)", log):
            # rebuild the side whose source no longer defines the moved name
            owners = set(defining_module(m.group(2)))
            for side in (m.group(1), m.group(3)):
                if side not in owners:
                    new.append('GowersSzemeredi.' + side)
        failed = re.search(r'FAILED (\S+)', log)
        new = [x for x in dict.fromkeys(new) if x not in healed and x not in targets]
        if not new:
            print('cannot attribute failure', flush=True)
            print('\n'.join(l for l in log.splitlines() if 'error' in l)[:3000], flush=True)
            return
        print(f'  healing {new}', flush=True)
        # healed modules must be built before the failing one: put them first
        healed = new + healed
    print('round limit reached', flush=True)


if __name__ == '__main__':
    main()
