"""Delete dead declarations (with their docstrings), module by module, keeping a module's deletions only
if it still elaborates.  usage: delete_decls.py dead_decls.json [--orphans | --names N1 N2 ...]"""
import collections
import importlib.util
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
spec = importlib.util.spec_from_file_location('ph', Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Research\GowersSzemeredi\fejer-generators\prune_haves.py'))
ph = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ph)
res = json.load(open(sys.argv[1], encoding='utf8'))
if '--orphans' in sys.argv:
    sel = [r for r in res if r.get('orphan') or r['private']]
else:
    names = set(sys.argv[sys.argv.index('--names') + 1:])
    sel = [r for r in res if r['name'] in names]
by_mod = collections.defaultdict(list)
for r in sel:
    by_mod[r['mod']].append(r['name'])


def block(t, n):
    mm = re.search(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?(?:theorem|lemma|def|abbrev) "
                   + re.escape(n) + r"(?![\w'])", t, re.M)
    a = mm.start()
    while True:
        doc = t.rfind('/--', 0, a)
        if doc != -1 and t[t.index('-/', doc) + 2:a].strip() == '':
            a = doc
            continue
        # `set_option ... in` / `open ... in` modifiers belong to the declaration
        prev = t.rfind('\n', 0, a - 1) + 1
        if a > 0 and re.fullmatch(r'(set_option|open)\b.*\bin\s*', t[prev:a]):
            a = prev
            continue
        break
    e = re.compile(r'\n\n(?=\S)').search(t, mm.end())
    return a, (e.start() + 2) if e else len(t)


scratch = HERE / 'delete_scratch.lean'
for m, names in sorted(by_mod.items()):
    p = GS / f'{m}.lean'
    t = p.read_text(encoding='utf8')
    new = t
    for n in names:
        a, b = block(new, n)
        new = new[:a] + new[b:]
    new = re.sub(r'\n{3,}', '\n\n', new)
    if ph.compiles(new, scratch):
        p.write_text(new, encoding='utf8', newline='\n')
        print(f'{m}: deleted {", ".join(names)}', flush=True)
    else:
        print(f'{m}: KEPT (module does not compile without them)', flush=True)
