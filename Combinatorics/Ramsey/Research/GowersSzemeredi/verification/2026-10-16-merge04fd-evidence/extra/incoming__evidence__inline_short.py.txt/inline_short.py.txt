"""Inline single-use lemmas whose proof has at most two lines into their only use.

usage: python -X utf8 inline_short.py single_use2.json
Candidates: lemma/theorem used by exactly one declaration of the same module, not paper-named, no
attribute, proof of at most two non-blank lines (a term, `fun ...`, `⟨...⟩` or a `by` block), one
application in the module (comments ignored), all explicit arguments supplied (named arguments for
implicit binders allowed).  The application becomes `(PROOF)` with the arguments substituted; if
that does not elaborate, `(show STATEMENT by TACTICS)` / `(show STATEMENT from TERM)`.  The lemma
(with docstring and any `set_option ... in` prefix) is deleted.  Kept only if the module compiles.
"""
import importlib.util
import json
import re
import sys
from pathlib import Path

import stmtx

HERE = Path(__file__).resolve().parent
GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
spec = importlib.util.spec_from_file_location('ph', Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Research\GowersSzemeredi\fejer-generators\prune_haves.py'))
ph = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ph)
spec2 = importlib.util.spec_from_file_location('idf', HERE / 'inline_defs.py')
src = (HERE / 'inline_defs.py').read_text(encoding='utf8').replace('\nmain()\n', '\n')
idf = {'__name__': 'idf', '__file__': str(HERE / 'inline_defs.py')}
exec(compile(src, 'inline_defs.py', 'exec'), idf)
binders, match_close, subst, blank_comments = idf['binders'], idf['match_close'], idf['subst'], idf['blank_comments']
PAPER = re.compile(r'^(lemma|theorem|corollary|proposition|prop|cor)_?\d|_holds$')
IDENT = re.compile(r"[A-Za-z_\u0370-\u03ff][\w'\u0370-\u03ff₀-₉]*")


def decl_span(s, hd):
    a = hd.start()
    while True:
        doc = s.rfind('/--', 0, a)
        if doc != -1 and s[s.index('-/', doc) + 2:a].strip() == '':
            a = doc
            continue
        prev = s.rfind('\n', 0, a - 1) + 1
        if a > 0 and re.fullmatch(r'(set_option|open)\b.*\bin\s*', s[prev:a]):
            a = prev
            continue
        return a


def parse_use(s, start, explicit, implicit):
    sub, p, count = {}, start, 0
    while count < len(explicit):
        q = p
        while q < len(s) and s[q] in ' \t':
            q += 1
        if q >= len(s) or s[q] == '\n':
            break
        if s[q] in '(⟨':
            r = match_close(s, q)
            named = re.match(r"\(\s*([^\s:()]+)\s*:=\s*", s[q:])
            if named and s[q] == '(':
                if named.group(1) not in implicit + explicit:
                    return None, None
                sub[named.group(1)] = s[q + named.end():r].strip()
                p = r + 1
                continue
            r += 1
            proj = re.match(r"(\.[\w'.]+)+", s[r:])
            if proj:
                r += proj.end()
            sub[explicit[count]] = s[q:r]
            count += 1
            p = r
            continue
        t = re.match(r"[^\s()\[\]{}⟨⟩,;:|]+", s[q:])
        if not t or not IDENT.match(t.group(0)) or t.group(0) in ('at', 'with', 'using', 'by', 'fun', 'from', 'then', 'else'):
            break
        sub[explicit[count]] = t.group(0)
        count += 1
        p = q + t.end()
    if count < len(explicit):
        return None, None
    return sub, p


def candidate_texts(s, x):
    name = x['name']
    short = name.split('.')[-1]
    hd = re.search(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:theorem|lemma) " + re.escape(name) + r"(?![\w'])",
                   s, re.M)
    if not hd or s[hd.start():hd.end()].lstrip().startswith('@['):
        return []
    j = stmtx.statement_end(s, hd.end())
    if j < 0:
        return []
    e = re.compile(r'\n\n(?=\S)').search(s, j)
    bend = e.start() if e else len(s)
    body = s[j + 2:bend].strip('\n')
    lines = [l for l in body.split('\n') if l.strip()]
    if not lines or len(lines) > 2 or re.search(r'\bwhere\b|\blet\b', body) or re.search(r'\n\s*[|·]', body):
        return []
    sig = s[hd.end():j]
    bs, k = binders(sig)
    m = re.match(r"\s*:\s*", sig[k:])
    if not m:
        return []
    stmt = ' '.join(sig[k + m.end():].split())
    explicit = [n for kk, ns, _ in bs if kk == '(' for n in ns]
    implicit = [n for kk, ns, _ in bs if kk in '{⦃' for n in ns]
    cf = blank_comments(s)
    a = decl_span(s, hd)
    uses = [u for u in re.finditer(r"(?<![\w'.@])" + re.escape(short) + r"(?![\w'])", cf) if not (a <= u.start() < bend)]
    if len(uses) != 1 or uses[0].start() < a:
        return []
    u = uses[0]
    sub, use_end = parse_use(s, u.end(), explicit, implicit)
    if sub is None:
        return []
    proof = ' '.join(l.strip() for l in lines)       # at most two lines: join them
    proof = subst(proof, sub)
    st = subst(stmt, sub)
    m_exact = re.fullmatch(r'by\s+exact\s+(.*)', proof)
    if m_exact and ';' not in m_exact.group(1) and '<;>' not in m_exact.group(1):
        proof = m_exact.group(1)                       # `by exact t` is just `t`
    if proof.startswith('by '):
        forms = [proof, f'show {st} {proof}']
    else:
        forms = [proof, f'show {st} from {proof}']
    # replace a surrounding `( ... )` instead of nesting; no parentheses after `:=` at a line end
    ua, ub = u.start(), use_end
    q = ub
    while q < len(s) and s[q] in ' \t':
        q += 1
    wrapped = ua > 0 and s[ua - 1] == '(' and q < len(s) and s[q] == ')'
    if wrapped:
        ua, ub = ua - 1, q + 1
    line_end = s.find('\n', ub)
    bare_ok = re.search(r':=\s*$', s[s.rfind('\n', 0, ua) + 1:ua]) and s[ub:line_end if line_end != -1 else len(s)].strip() == ''
    cut_end = e.start() + 2 if e else len(s)
    out = []
    for f in forms:
        f = f if (bare_ok and not f.startswith('show')) else '(' + f + ')'
        new = s[:ua] + f + s[ub:]
        new = new[:a] + new[cut_end:]
        out.append(re.sub(r'\n{3,}', '\n\n', new))
    return out


def main():
    res = json.load(open(sys.argv[1], encoding='utf8'))
    scratch = HERE / 'inline_short_scratch.lean'
    for x in res:
        if x['kind'] not in ('lemma', 'theorem') or x['user_mod'] != x['mod'] or PAPER.search(x['name'].split('.')[-1]):
            continue
        p = GS / f"{x['mod']}.lean"
        s = p.read_text(encoding='utf8')
        texts = candidate_texts(s, x)
        if not texts:
            continue
        for k, new in enumerate(texts):
            if ph.compiles(new, scratch):
                p.write_text(new, encoding='utf8', newline='\n')
                print(f"{x['mod']}.{x['name']}: inlined ({'bare' if k == 0 else 'show'}, {x['lines']} lines)", flush=True)
                break
        else:
            print(f"{x['mod']}.{x['name']}: kept (no inlined form compiles)", flush=True)


main()
