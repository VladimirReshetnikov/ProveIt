"""Inline single-use thin wrappers: declarations whose body is a one-line term, used once in their module.

usage: python -X utf8 inline_wrappers.py single_use.json
For each candidate W (explicit parameters p1..pn, body B), the single use `W a1 .. an` is replaced by
`(B[p := a])` and the declaration (with its docstring) is deleted.  Skipped: paper-named results
(lemma_/theorem_/corollary_/proposition_ prefixes), named or partial applications, bodies with
`by`, `fun`, anonymous constructors or several lines.  Each inlining is elaborated (prune_haves.compiles,
no olean) and kept only if the module compiles.  Prints the kept inlinings.
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
PAPER = re.compile(r'^(lemma|theorem|corollary|proposition|prop|cor)_\d')
TOK = re.compile(r"[^\s()\[\]{}⟨⟩,;:|]+")
IDENT = re.compile(r"[A-Za-z_\u0370-\u03ff][\w'\u0370-\u03ff₀-₉]*")


def comment_free(t):
    out, i = list(t), 0
    for m in re.finditer(r'/-.*?-/|--[^\n]*', t, flags=re.S):
        for k in range(m.start(), m.end()):
            if out[k] != '\n':
                out[k] = ' '
    return ''.join(out)


def explicit_params(sig):
    names, i = [], 0
    while True:
        while i < len(sig) and sig[i].isspace():
            i += 1
        if i >= len(sig) or sig[i] not in '({[⦃':
            return names
        depth, j = 0, i
        while j < len(sig):
            if sig[j] in '({[⦃':
                depth += 1
            elif sig[j] in ')}]⦄':
                depth -= 1
                if depth == 0:
                    break
            j += 1
        if sig[i] == '(':
            g = sig[i + 1:j]
            k = g.find(':')
            if k > 0:
                names += g[:k].split()
        i = j + 1


def parse_args(t, p, n):
    spans = []
    while len(spans) < n:
        q = p
        while q < len(t) and t[q] in ' \t':
            q += 1
        if q >= len(t) or t[q] == '\n':
            return None
        c = t[q]
        if c in '(⟨':
            if re.match(r"\(\s*[^\s:()]+\s*:=", t[q:]):
                return None
            depth, r = 0, q
            while r < len(t):
                if t[r] in '(⟨[{':
                    depth += 1
                elif t[r] in ')⟩]}':
                    depth -= 1
                    if depth == 0:
                        break
                r += 1
            r += 1
            proj = re.match(r"(\.[\w'.]+)+", t[r:])
            if proj:
                r += proj.end()
            spans.append((q, r))
            p = r
            continue
        m = TOK.match(t, q)
        if not m or not IDENT.match(m.group(0)) or m.group(0) in ('at', 'with', 'using', 'by', 'fun', 'from'):
            return None
        spans.append((m.start(), m.end()))
        p = m.end()
    return spans


def main():
    res = json.load(open(sys.argv[1], encoding='utf8'))
    scratch = HERE / 'inline_scratch.lean'
    for x in res:
        m, name = x['mod'], x['name']
        short = name.split('.')[-1]
        if PAPER.match(short) or x['user_mod'] != m or '.' in name:
            continue
        p = GS / f'{m}.lean'
        s = p.read_text(encoding='utf8')
        hd = re.search(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?(?:theorem|lemma|def|abbrev) "
                       + re.escape(name) + r"(?![\w'])", s, re.M)
        if not hd or s[hd.start():hd.end()].lstrip().startswith('@['):
            continue
        j = stmtx.statement_end(s, hd.end())
        e = re.compile(r'\n\n(?=\S)').search(s, j)
        bend = e.start() if e else len(s)
        body = s[j + 2:bend].strip()
        if '\n' in body or re.search(r'\bby\b|\bfun\b|=>|↦|⟨|\{|\bwhere\b|\blet\b', body):
            continue
        params = explicit_params(s[hd.end():j])
        cf = comment_free(s)
        uses = [u for u in re.finditer(r"(?<![\w'.@])" + re.escape(short) + r"(?![\w'])", cf)
                if not (hd.start() <= u.start() < bend)]
        if len(uses) != 1:
            continue
        u = uses[0]
        spans = parse_args(s, u.end(), len(params)) if params else []
        if spans is None or len(spans) != len(params):
            continue
        sub = {pn: s[a:b] for pn, (a, b) in zip(params, spans)}
        nb = re.sub(r"(?<![\w'.])(" + '|'.join(map(re.escape, params)) + r")(?![\w'₀-₉])",
                    lambda t: sub[t.group(1)] if IDENT.fullmatch(sub[t.group(1)]) else '(' + sub[t.group(1)] + ')',
                    body) if params else body
        use_end = spans[-1][1] if spans else u.end()
        a = hd.start()
        doc = s.rfind('/--', 0, a)
        if doc != -1 and s[s.index('-/', doc) + 2:a].strip() == '':
            a = doc
        cut_end = e.start() + 2 if e else len(s)
        new = s[:u.start()] + '(' + nb + ')' + s[use_end:]
        # delete the declaration (positions before the use are unchanged if the declaration comes first)
        if a < u.start():
            new = new[:a] + new[cut_end:]
        else:
            continue
        new = re.sub(r'\n{3,}', '\n\n', new)
        if ph.compiles(new, scratch):
            p.write_text(new, encoding='utf8', newline='\n')
            print(f'{m}.{name}: inlined ({x["lines"]} lines)', flush=True)
        else:
            print(f'{m}.{name}: kept (inlining does not compile)', flush=True)


main()
