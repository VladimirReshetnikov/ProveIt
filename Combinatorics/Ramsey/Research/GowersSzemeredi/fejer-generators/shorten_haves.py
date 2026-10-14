"""Try closing multi-line `have` proofs with one automation tactic; keep a replacement only if
the module still elaborates. usage: python -X utf8 shorten_haves.py MODULE"""
import importlib.util
import re
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('ph', HERE / 'prune_haves.py')
ph = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ph)


def candidates(goal):
    real = 'Real' in goal or 'alpha' in goal or '⁻¹' in goal or '/' in goal or 'rpow' in goal
    if re.match(r'\s*0\s*(<|≤)', goal) or re.search(r'(<|≤)\s*0\b', goal):
        first = ['positivity']
    else:
        first = []
    return first + (['linarith', 'nlinarith'] if real else ['omega', 'norm_num'])


def main():
    mod = sys.argv[1]
    src = ph.GS / f'{mod}.lean'
    lines = src.read_text(encoding='utf8').split('\n')
    scratch = HERE / f'Short_{mod}.lean'
    assert ph.compiles('\n'.join(lines), scratch), 'baseline does not compile'
    saved = 0
    for (a, b) in reversed(ph.units(lines, 0, len(lines))):
        head = lines[a]
        m = re.match(r'^(\s*)have (\S+) : (.*):= by\s*$', head)
        if not m or b - a < 3:  # only proofs spanning at least two further lines
            continue
        ind, name, goal = m.group(1), m.group(2), m.group(3)
        for tac in candidates(goal):
            new = f'{ind}have {name} : {goal}:= by {tac}'
            if len(new) > 100:
                new = f'{ind}have {name} : {goal}:=\n{ind}  by {tac}'
            trial = lines[:a] + new.split('\n') + lines[b:]
            t0 = time.time()
            if ph.compiles('\n'.join(trial), scratch):
                saved += (b - a) - len(new.split('\n'))
                print(f'SHORTENED L{a + 1}-{b} by {tac} ({time.time() - t0:.0f}s): {head.strip()[:90]}', flush=True)
                lines = trial
                src.write_text('\n'.join(lines), encoding='utf8', newline='\n')
                break
        else:
            print(f'kept L{a + 1}-{b}: {head.strip()[:90]}', flush=True)
    print(f'saved {saved} lines', flush=True)


if __name__ == '__main__':
    main()
