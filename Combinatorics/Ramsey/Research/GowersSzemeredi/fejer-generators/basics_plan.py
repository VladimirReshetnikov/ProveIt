"""Plan a Proofs00Basics module (imports only Definitions) hosting lemma families re-proved in several
unrelated proof modules.

usage: python -X utf8 basics_plan.py out.json
A family qualifies when
  * its members (same statement up to binder names, same namespace LeanProofs.GowersSzemeredi) live
    in >= 2 proof modules with local oleans, and no member module is an ancestor of all the others
    (those are handled by share_groups6.py);
  * its statement and the chosen copy's proof mention no constant declared outside Definitions
    except other planned basics lemmas (checked against every def/lemma/abbrev/structure name declared
    in any non-Definitions module).
The host name is the shortest member name not declared anywhere else in the corpus.
"""
import collections
import json
import os
import re
import sys

import stmtx
normalise = stmtx.normalise

GS = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi'
OUT = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\.lake\build\lib\lean\GowersSzemeredi'
mods = [f[:-5] for f in os.listdir(GS) if f.endswith('.lean')]
src = {m: open(os.path.join(GS, m + '.lean'), encoding='utf8').read() for m in mods}
imp = {m: re.findall(r'^import GowersSzemeredi\.(\S+)', src[m], re.M) for m in mods}
memo = {}


def anc(m):
    if m not in memo:
        s = set()
        memo[m] = s
        for d in imp.get(m, []):
            s |= {d} | anc(d)
    return memo[m]


BINDER = re.compile(r'[({\[⦃]\s*([^:(){}\[\]⦃⦄]+?)\s*:')
TOKEN = re.compile(r"[A-Za-z_\u0370-\u03ff][\w'.\u0370-\u03ff]*")
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?"
                  r"(theorem|lemma|def|abbrev|structure|inductive|instance|class) ([^\s(:{\[]+)", re.M)
HEAD = re.compile(r'^((?:@\[[^\]]*\]\s*)?)(private )?(theorem|lemma) (\S+)', re.M)
END = re.compile(r'\n\n(?=\S)')

outside = collections.defaultdict(set)   # short name -> modules (not Definitions) declaring it
for m in mods:
    if m == 'Definitions':
        continue
    for d in DECL.finditer(src[m]):
        outside[d.group(2).split('.')[-1]].add(m)


def ns_at(m, pos):
    stack = []
    for line in src[m][:pos].split('\n'):
        a = re.match(r'namespace (\S+)', line)
        b = re.match(r'end (\S+)', line)
        if a:
            stack.append(a.group(1))
        elif b and stack and stack[-1] == b.group(1):
            stack.pop()
    return '.'.join(stack)


def _old_normalise(stmt):
    stmt = ' '.join(stmt.replace('↦', '=>').split())
    names = []
    for b in BINDER.finditer(stmt):
        for n in b.group(1).split():
            if re.fullmatch(r"[A-Za-z_\u0370-\u03ff][\w'\u0370-\u03ff]*", n) and n not in names:
                names.append(n)
    ren = {n: f'v{i}' for i, n in enumerate(names)}
    return re.sub(r"[A-Za-z_\u0370-\u03ff][\w'\u0370-\u03ff]*", lambda t: ren.get(t.group(0), t.group(0)), stmt)


decls = []
for m in mods:
    if 'Audit' in m or not m.startswith('Proofs'):
        continue
    if not os.path.exists(os.path.join(OUT, m + '.olean')):
        continue
    s = src[m]
    for mm in HEAD.finditer(s):
        name = mm.group(4)
        if '.' in name or ns_at(m, mm.start()) != 'LeanProofs.GowersSzemeredi':
            continue
        j = stmtx.statement_end(s, mm.end())
        if j < 0:
            continue
        e = END.search(s, j)
        a = mm.start()
        doc = s.rfind('/--', 0, a)
        if doc != -1 and s[s.index('-/', doc) + 2:a].strip() == '':
            a = doc
        b = e.start() if e else len(s)
        decls.append(dict(stmt=normalise(s[mm.end():j]), mod=m, name=name, private=bool(mm.group(2)),
                          attr=mm.group(1).strip(), text=s[a:b], lines=s[a:b].count('\n') + 1))
fam = collections.defaultdict(list)
for d in decls:
    fam[d['stmt']].append(d)

cand = {}
for stmt, ms in fam.items():
    mset = {d['mod'] for d in ms}
    if len(mset) < 2 or len(mset) != len(ms):
        continue
    if any(all(h == x or h in anc(x) for x in mset) for h in mset):
        continue  # chain family
    own = {d['name'] for d in ms}
    hname = next((n for n in sorted(own, key=len) if outside[n] <= mset), None)
    if hname is not None:
        cand[stmt] = dict(members=ms, name=hname)


def undotted(text):
    return {t for t in TOKEN.findall(text) if '.' not in t}


# fixpoint: a copy may cite members of other candidate families that live in its own module
while True:
    where = {(d['mod'], d['name']): st for st, c in cand.items() for d in c['members']}
    drop = []
    for st, c in cand.items():
        c['pick'] = None
        own = {d['name'] for d in c['members']}
        for d in sorted(c['members'], key=lambda d: d['lines']):
            body = d['text']
            visible = anc(d['mod']) | {d['mod']}
            foreign = {t for t in undotted(body)
                       if len(t) > 2 and outside[t] & visible and t not in own and (d['mod'], t) not in where}
            if not foreign:
                c['pick'] = d
                break
        if c['pick'] is None:
            drop.append(st)
    if not drop:
        break
    for st in drop:
        del cand[st]

# rewrite each picked copy: public, host name, cited sibling members renamed to their hosts
plan = []
for st, c in cand.items():
    d = c['pick']
    text = re.sub(r'^((?:@\[[^\]]*\]\s*)?)private ', r'\1', d['text'], count=1, flags=re.M)
    text = re.sub(r'^@\[[^\]]*\]\s*', '', text, flags=re.M)  # attributes become local in members
    deps = set()
    for t in undotted(text):
        k = (d['mod'], t)
        if k in where and where[k] != st:
            deps.add(cand[where[k]]['name'])
            text = re.sub(r"(?<![\w.'])" + re.escape(t) + r"(?![\w'])", cand[where[k]]['name'], text)
    text = re.sub(r"^((?:theorem|lemma) )" + re.escape(d['name']) + r"(?![\w'])", r'\1' + c['name'], text,
                  count=1, flags=re.M)
    plan.append(dict(name=c['name'], copy=text, deps=sorted(deps),
                     members=[dict(mod=m['mod'], name=m['name'], private=m['private'], attr=m['attr'],
                                   lines=m['lines']) for m in c['members']],
                     saved=sum(m['lines'] for m in c['members']) - d['lines']))
plan.sort(key=lambda r: -r['saved'])
json.dump(plan, open(sys.argv[1], 'w', encoding='utf8'), indent=1, ensure_ascii=False)
for r in plan:
    attrs = sorted({m['attr'] for m in r['members'] if m['attr']})
    print(f"{r['saved']:4} {len(r['members']):2} {r['name']} {' '.join(attrs)} deps={r['deps']}")
print(len(plan), 'families,', sum(r['saved'] for r in plan), 'lines')
