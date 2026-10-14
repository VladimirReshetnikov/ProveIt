"""Remove unused explicit hypotheses from a lemma and the matching argument at every call site.

usage: python -X utf8 drop_hyp.py MODULE LEMMA VAR [VAR ...]
Prints the modules it edited, or `SKIP: reason` and edits nothing.  Call sites are recognised as
`LEMMA` followed by positional arguments; partial applications that stop before a removed argument,
`@LEMMA`, and named arguments for a removed binder make the lemma skipped.
"""
import re
import sys
from pathlib import Path

import stmtx

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
mod, lemma, drop = sys.argv[1], sys.argv[2], set(sys.argv[3:])
srcs = {f.stem: f.read_text(encoding='utf8') for f in GS.glob('*.lean')}
s = srcs[mod]
head = re.search(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:theorem|lemma) " + re.escape(lemma) + r"(?![\w'])", s, re.M)
if not head:
    sys.exit('SKIP: declaration not found')
end = stmtx.statement_end(s, head.end())
sig = s[head.end():end]

# leading binder groups of the signature, with their spans
groups, i = [], 0
while True:
    while i < len(sig) and sig[i].isspace():
        i += 1
    if i >= len(sig) or sig[i] not in '({[⦃':
        break
    depth, j = 0, i
    while j < len(sig):
        if sig[j] in '({[⦃':
            depth += 1
        elif sig[j] in ')}]⦄':
            depth -= 1
            if depth == 0:
                break
        j += 1
    groups.append((sig[i], i, j + 1))
    i = j + 1
explicit = []          # names of explicit binders in order
for kind, a, b in groups:
    body = sig[a + 1:b - 1]
    k = body.find(':')
    names = body[:k].split() if k > 0 else []
    if kind == '⦃':
        if any(n in drop for n in names):
            sys.exit('SKIP: strict-implicit binder')
        continue
    if kind == '(':
        explicit += names
    elif any(n in drop for n in names):
        sys.exit('SKIP: removed variable is not an explicit binder')
missing = drop - set(explicit)
if missing:
    sys.exit(f'SKIP: not explicit binders {missing}')
idx = sorted(explicit.index(n) for n in drop)

STOP = {'at', 'with', 'using', 'generalizing', 'then', 'else', 'fun', 'by', 'from', 'only', 'in', 'do'}
TOK = re.compile(r"[^\s()\[\]{}⟨⟩,;:|]+")


def parse_args(t, p, need):
    """Spans of up to `need` positional arguments starting at t[p:]; None on anything unclear."""
    spans = []
    while len(spans) < need:
        q = p
        while q < len(t) and t[q] in ' \t':
            q += 1
        if q < len(t) and t[q] == '\n':
            # continuation line: deeper indentation than the line holding the call
            ls = t.rfind('\n', 0, p) + 1
            ind = len(t[ls:]) - len(t[ls:].lstrip(' '))
            nl = q + 1
            nq = nl
            while nq < len(t) and t[nq] == ' ':
                nq += 1
            if nq - nl <= ind:
                break
            q = nq
        if q >= len(t):
            break
        c = t[q]
        if c in '(⟨':
            close = {'(': ')', '⟨': '⟩'}[c]
            depth, r = 0, q
            while r < len(t):
                if t[r] in '(⟨[{':
                    depth += 1
                elif t[r] in ')⟩]}':
                    depth -= 1
                    if depth == 0:
                        break
                r += 1
            named = re.match(r"\(\s*([^\s:()]+)\s*:=", t[q:])
            if named:
                if named.group(1) in drop:
                    return None   # named argument for a removed binder
                p = r + 1         # named arguments are not positional
                continue
            r += 1
            proj = re.match(r"(\.[\w'.]+)+", t[r:])   # `(h).le`, `(h).1.trans` belong to the argument
            if proj:
                r += proj.end()
            spans.append((q, r))
            p = r
            continue
        m = TOK.match(t, q)
        if not m or m.group(0) in STOP or m.group(0).startswith(('<;>', '=>', '·', '←', '%')) or \
                m.group(0) in ('|', ':=', '=', '<', '≤', '+', '-', '*', '/', '^', '∧', '∨', '→', '↔', '•', '∘'):
            break
        spans.append((m.start(), m.end()))
        p = m.end()
    return spans


def comment_spans(t):
    spans, i = [], 0
    while i < len(t):
        if t.startswith('--', i):
            j = t.find('\n', i)
            j = len(t) if j < 0 else j
            spans.append((i, j))
            i = j
        elif t.startswith('/-', i):
            depth, j = 1, i + 2
            while j < len(t) and depth:
                if t.startswith('/-', j):
                    depth += 1
                    j += 2
                elif t.startswith('-/', j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            spans.append((i, j))
            i = j
        else:
            i += 1
    return spans


edits = {}
for k, t in srcs.items():
    cs = comment_spans(t) if lemma in t else []
    occ = [m for m in re.finditer(r"(?<![\w'.@])" + re.escape(lemma) + r"(?![\w'])", t)
           if not any(a <= m.start() < b for a, b in cs)]
    if k == mod:
        occ = [m for m in occ if not (head.start() <= m.start() < end)]
    if not occ:
        continue
    if re.search(r"@" + re.escape(lemma) + r"(?![\w'])", t):
        sys.exit(f'SKIP: @{lemma} in {k}')
    for n in drop:
        if re.search(re.escape(lemma) + r"[^\n]*\(" + re.escape(n) + r"\s*:=", t):
            sys.exit(f'SKIP: named argument {n} in {k}')
    cuts = []
    for m in occ:
        before = t[max(0, m.start() - 40):m.start()]
        if re.search(r"(simp|rw|simp_rw|simp only|nth_rewrite|rewrite|unfold)\s*\[[^\]]*$", before):
            # rewrite-style use: arguments, if any, follow the same rules
            pass
        spans = parse_args(t, m.end(), max(idx) + 1)
        if spans is None:
            sys.exit(f'SKIP: unclear call in {k}')
        if len(spans) <= max(idx):
            sys.exit(f'SKIP: partial application in {k} at {t[m.start():m.start() + 60]!r}')
        for i2 in idx:
            a, b = spans[i2]
            # delete the argument and the whitespace in front of it
            a2 = a
            while a2 > 0 and t[a2 - 1] in ' \t':
                a2 -= 1
            cuts.append((a2, b))
    nt = t
    for a, b in sorted(cuts, reverse=True):
        nt = nt[:a] + nt[b:]
    edits[k] = nt

# the signature itself
t = edits.get(mod, s)
off = t.find(sig)
assert off >= 0
newsig = sig
for kind, a, b in sorted(groups, key=lambda g: -g[1]):
    body = newsig[a + 1:b - 1]
    k = body.find(':')
    if kind != '(' or k <= 0:
        continue
    names = body[:k].split()
    keep = [n for n in names if n not in drop]
    if keep == names:
        continue
    if not keep:
        a2 = a
        while a2 > 0 and newsig[a2 - 1] in ' \t':
            a2 -= 1
        newsig = newsig[:a2] + newsig[b:]
    else:
        newsig = newsig[:a + 1] + ' '.join(keep) + ' ' + body[k:].lstrip() + newsig[b - 1:]
newsig = re.sub(r'\n[ \t]+\n', '\n', newsig)
t = t[:off] + newsig + t[off + len(sig):]
edits[mod] = t
for k, nt in edits.items():
    if nt != srcs[k]:
        (GS / f'{k}.lean').write_text(nt, encoding='utf8', newline='\n')
print(' '.join(sorted(k for k, nt in edits.items() if nt != srcs[k])))
