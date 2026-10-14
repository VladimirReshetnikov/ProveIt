"""Apply basics_plan.json: write Proofs00Basics.lean with one public copy per family, delete the
member copies, rename their uses, keep public members as aliases, turn member attributes into local
attributes at the deleted lemma's position, and import Proofs00Basics in the topmost member modules.

usage: python -X utf8 apply_basics.py basics_plan.json [skip_name ...]
Prints the touched modules.
"""
import json
import os
import re
import sys

GS = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi'
HOST = 'Proofs00Basics'
plan = [p for p in json.load(open(sys.argv[1], encoding='utf8')) if p['name'] not in sys.argv[2:]]
# public members carrying attributes would need attributed aliases: leave those families alone
plan = [p for p in plan if not any(m['attr'] and not m['private'] for m in p['members'])]
while True:  # drop families citing a dropped family
    keep = {p['name'] for p in plan}
    nxt = [p for p in plan if all(d in keep for d in p['deps'])]
    if len(nxt) == len(plan):
        break
    plan = nxt
src = {}


def text(m):
    if m not in src:
        src[m] = open(os.path.join(GS, m + '.lean'), encoding='utf8').read()
    return src[m]


mods = [f[:-5] for f in os.listdir(GS) if f.endswith('.lean')]
imp = {m: re.findall(r'^import GowersSzemeredi\.(\S+)', text(m), re.M) for m in mods}
memo = {}


def anc(m):
    if m not in memo:
        s = set()
        memo[m] = s
        for d in imp.get(m, []):
            s |= {d} | anc(d)
    return memo[m]


def block(t, n):
    mm = re.search(r"^(?:@\[[^\]]*\]\s*)?(?:private )?(?:theorem|lemma) " + re.escape(n) + r"(?![\w'])", t, re.M)
    a = mm.start()
    doc = t.rfind('/--', 0, a)
    if doc != -1 and t[t.index('-/', doc) + 2:a].strip() == '':
        a = doc
    e = re.compile(r'\n\n(?=\S)').search(t, mm.end())
    return a, (e.start() + 2) if e else len(t)


def opens(m):
    head = text(m).split('namespace LeanProofs.GowersSzemeredi', 1)[0]
    return [l for l in head.splitlines() if l.startswith('open ')]


# order hosted copies so that dependencies come first
by = {p['name']: p for p in plan}
order, seen = [], set()


def visit(n):
    if n in seen or n not in by:
        return
    seen.add(n)
    for d in by[n]['deps']:
        visit(d)
    order.append(by[n])


for p in plan:
    visit(p['name'])
missing = [p['name'] for p in order if any(d not in by for d in p['deps'])]
assert not missing, missing

pick_mod = {}
for p in plan:
    first = p['copy'].splitlines()
    pick_mod[p['name']] = next(m['mod'] for m in p['members']
                               if re.search(r"(?:theorem|lemma) " + re.escape(m['name']) + r"(?![\w'])",
                                            text(m['mod'])) and m['lines'] == p['copy'].count('\n') + 1) \
        if any(m['lines'] == p['copy'].count('\n') + 1 for m in p['members']) else p['members'][0]['mod']

out = ['import GowersSzemeredi.Definitions', '', '/-!', '# Shared elementary lemmas',
       '', 'Small identities about `exponential`, `centeredAbs`, `countWhere` and Fourier transforms of',
       'indicators that several proof modules used to re-prove privately.', '-/', '',
       'set_option autoImplicit false', '', 'noncomputable section', '',
       'namespace LeanProofs.GowersSzemeredi', '']
for p in order:
    out += ['section', ''] + opens(pick_mod[p['name']]) + [''] + [p['copy'].rstrip(), '', 'end', '']
out += ['end LeanProofs.GowersSzemeredi', '']
hosted = '\n'.join(out)
hosted = re.sub(r'\n{3,}', '\n\n', hosted)

touched = set()
for p in plan:
    h = p['name']
    for m in p['members']:
        t = text(m['mod'])
        a, b = block(t, m['name'])
        repl = ''
        if not m['private']:
            if m['name'] != h:
                repl = f"alias {m['name']} := {h}\n\n"
        elif m['attr']:
            attr = m['attr'][2:-1]
            # `@[simp] private` is still a global, exported attribute: keep it global
            repl = f"attribute [{attr}] {h}\n\n"
        t = t[:a] + repl + t[b:]
        if m['name'] != h and m['private']:
            t = re.sub(r"(?<![\w.'])" + re.escape(m['name']) + r"(?![\w'])", h, t)
        src[m['mod']] = re.sub(r'\n{3,}', '\n\n', t)
        touched.add(m['mod'])
top = [m for m in touched if not any(x in anc(m) for x in touched if x != m)]
for m in top:
    t = text(m)
    last = list(re.finditer(r'^import .*$', t, re.M))[-1]
    src[m] = t[:last.end()] + '\nimport GowersSzemeredi.' + HOST + t[last.end():]
for m in touched:
    open(os.path.join(GS, m + '.lean'), 'w', encoding='utf8', newline='\n').write(src[m])
open(os.path.join(GS, HOST + '.lean'), 'w', encoding='utf8', newline='\n').write(hosted)
print(' '.join(sorted(touched | {HOST})))
