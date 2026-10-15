"""Move side results out of final-route modules into new side modules.

usage: python -X utf8 detach_moves.py spec.json
spec: [{"from": "U", "to": "NewModule", "imports": ["D1", ...], "decls": ["name", ...], "doc": "..."}]
The new module imports U and the listed modules, repeats U's `open` lines, and holds the moved
declarations (with their docstrings) in namespace LeanProofs.GowersSzemeredi.  Every other module
naming a moved declaration gets `import GowersSzemeredi.NewModule`.  Prints the touched modules.
"""
import json
import re
import sys
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
srcs = {f.stem: f.read_text(encoding='utf8') for f in GS.glob('*.lean')}
touched = set()


def block(t, n):
    mm = re.search(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?(?:theorem|lemma|def|abbrev) "
                   + re.escape(n) + r"(?![\w'])", t, re.M)
    assert mm, n
    a = mm.start()
    doc = t.rfind('/--', 0, a)
    if doc != -1 and t[t.index('-/', doc) + 2:a].strip() == '':
        a = doc
    e = re.compile(r'\n\n(?=\S)').search(t, mm.end())
    return a, (e.start() + 2) if e else len(t)


for s in json.load(open(sys.argv[1], encoding='utf8')):
    u, new = s['from'], s['to']
    t = srcs[u]
    pieces = []
    for n in s['decls']:
        a, b = block(t, n)
        pieces.append(t[a:b].rstrip() + '\n')
        t = t[:a] + t[b:]
    srcs[u] = re.sub(r'\n{3,}', '\n\n', t)
    touched.add(u)
    head = srcs[u].split('namespace LeanProofs.GowersSzemeredi', 1)
    pre_opens = [l for l in head[0].splitlines() if l.startswith('open ')]
    post = head[1].split('\n')
    post_opens = []
    for l in post[1:]:
        if l.startswith(('open ', 'variable')):
            post_opens.append(l)
        elif l.strip() and not l.startswith('--'):
            break
    if new in touched:   # a second source feeding the same side module
        nt = srcs[new]
        last = list(re.finditer(r'^import .*$', nt, re.M))[-1]
        nt = nt[:last.end()] + f'\nimport GowersSzemeredi.{u}' + nt[last.end():]
        i = nt.rindex('end LeanProofs.GowersSzemeredi')
        srcs[new] = nt[:i] + '\n'.join(pieces) + '\n' + nt[i:]
    else:
        text = '\n'.join([f'import GowersSzemeredi.{u}'] + [f'import GowersSzemeredi.{d}' for d in s['imports']]) + '\n\n'
        text += f'/-! {s["doc"]} -/\n\nset_option autoImplicit false\n\nnoncomputable section\n\n'
        text += ''.join(l + '\n' for l in pre_opens) + ('\n' if pre_opens else '')
        text += 'namespace LeanProofs.GowersSzemeredi\n\n'
        text += ''.join(l + '\n' for l in post_opens) + ('\n' if post_opens else '')
        text += '\n'.join(pieces) + '\nend LeanProofs.GowersSzemeredi\n'
        srcs[new] = text
    touched.add(new)
    pat = re.compile(r"(?<![\w'.])(?:" + '|'.join(map(re.escape, s['decls'])) + r")(?![\w'])")
    for m, mt in list(srcs.items()):
        code = re.sub(r'/-.*?-/', '', mt, flags=re.S)
        code = re.sub(r'--[^\n]*', '', code)
        if m in (u, new) or not pat.search(code):
            continue
        line = f'import GowersSzemeredi.{new}'
        if line in mt:
            continue
        last = list(re.finditer(r'^import .*$', mt, re.M))[-1]
        srcs[m] = mt[:last.end()] + '\n' + line + mt[last.end():]
        touched.add(m)
for m in touched:
    (GS / f'{m}.lean').write_text(srcs[m], encoding='utf8', newline='\n')
print(' '.join(sorted(touched)))
