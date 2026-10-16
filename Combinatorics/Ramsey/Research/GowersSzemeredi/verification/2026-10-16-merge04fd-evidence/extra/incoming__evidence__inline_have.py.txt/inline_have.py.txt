"""Inline single-use lemmas with short proofs at `have`/`exact` use sites, in idiomatic form.

usage: python -X utf8 inline_have.py single_use2.json MAXLINES
Candidates: lemma/theorem used by exactly one declaration of its own module, not paper-named, no
attribute, proof of at most MAXLINES non-blank lines.  The single use must be a whole line of one of
the forms
    have NAME := L args          have NAME : T := L args          exact L args
with all explicit arguments supplied.  Rewrites:
    have NAME : STATEMENT := by        exact L args  ->  the lemma's tactics, spliced in place
      <lemma tactics>                  (fallback: `exact show STATEMENT by` + tactics)
(term proofs become `:= TERM` / `exact TERM`).  Parameters are replaced by the arguments.  The lemma
(with docstring and `set_option ... in` prefix) is deleted.  Each rewrite is kept only if the module
elaborates.
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
src = (HERE / 'inline_short.py').read_text(encoding='utf8').replace('\nmain()\n', '\n')
ins = {'__name__': 'ins', '__file__': str(HERE / 'inline_short.py')}
exec(compile(src, 'inline_short.py', 'exec'), ins)
binders, blank_comments, decl_span, parse_use = (ins['binders'], ins['blank_comments'], ins['decl_span'],
                                                 ins['parse_use'])
match_close = ins['match_close']
IDENT = ins['IDENT']
PAPER = ins['PAPER']


def subst(text, sub):
    """Replace parameter names by argument texts; parenthesise compound arguments once."""
    if not sub:
        return text

    def wrap(arg):
        if IDENT.fullmatch(arg):
            return arg
        if arg.startswith('(') and match_close(arg, 0) == len(arg) - 1:
            return arg
        return '(' + arg + ')'
    pat = re.compile(r"(?<![\w'.])(" + '|'.join(map(re.escape, sub)) + r")(?![\w'₀-₉])")
    return pat.sub(lambda t: wrap(sub[t.group(1)]), text)


def reindent_block(lines, ind):
    base = min(len(l) - len(l.lstrip()) for l in lines if l.strip())
    return [(' ' * ind + l[base:]) if l.strip() else '' for l in lines]


def rewrites(s, x, maxlines):
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
    body = s[j + 2:bend]
    blines = [l for l in body.split('\n')]
    nonblank = [l for l in blines if l.strip()]
    if not nonblank or len(nonblank) > maxlines or re.search(r'\bwhere\b', body):
        return []
    sig = s[hd.end():j]
    bs, k = binders(sig)
    m = re.match(r"\s*:\s*", sig[k:])
    if not m:
        return []
    stmt_text = sig[k + m.end():].rstrip()
    explicit = [n for kk, ns, _ in bs if kk == '(' for n in ns]
    implicit = [n for kk, ns, _ in bs if kk in '{⦃' for n in ns]
    a = decl_span(s, hd)
    cut_end = e.start() + 2 if e else len(s)
    cf = blank_comments(s)
    uses = [u for u in re.finditer(r"(?<![\w'.@])" + re.escape(short) + r"(?![\w'])", cf) if not (a <= u.start() < bend)]
    if len(uses) != 1 or uses[0].start() < cut_end:
        return []
    u = uses[0]
    ls = s.rfind('\n', 0, u.start()) + 1
    le = s.find('\n', u.start())
    le = len(s) if le < 0 else le
    head = s[ls:u.start()]
    sub, use_end = parse_use(s, u.end(), explicit, implicit)
    if sub is None or s[use_end:le].strip():
        return []
    ind = len(head) - len(head.lstrip())
    mh = re.fullmatch(r'(\s*)have\s+([^\s:]+)\s*(?::\s*(.*?))?\s*:=\s*', head)
    me = re.fullmatch(r'(\s*)exact\s+', head)
    if not (mh or me):
        return []
    stmt = subst(stmt_text, sub)
    st_lines = stmt.split('\n')
    first = body.lstrip('\n')
    is_tac = first.lstrip().startswith('by')
    if is_tac:
        # tactics: the text after `by` on the first line (if any) and the following lines
        fl, *rest = first.split('\n')
        after_by = fl.lstrip()[2:].strip()
        tac_lines = ([after_by] if after_by else []) + [l for l in rest]
        tac_lines = [subst(l, sub) for l in tac_lines]
        while tac_lines and not tac_lines[-1].strip():
            tac_lines.pop()
        if not tac_lines:
            return []
    else:
        term_lines = [subst(l, sub) for l in first.rstrip().split('\n')]
    outs = []
    if mh:
        hname = mh.group(2)
        # the caller's own annotation reads best locally; the lemma's statement is the fallback
        stmt_variants = ([mh.group(3).strip()] if mh.group(3) else []) + [None]
    else:
        stmt_variants = [None]
    for annot in (stmt_variants if mh else [None]):
        if annot is not None:
            st_lines = [annot]
        else:
            st_lines = stmt.split('\n')
        outs.extend(build(mh, me, ind, st_lines, is_tac, tac_lines if is_tac else None,
                          None if is_tac else term_lines))
    res = []
    for o in outs:
        new = s[:ls] + o + s[le:]
        new = new[:a] + new[cut_end:]
        res.append(re.sub(r'\n{3,}', '\n\n', new))
    return res


def build(mh, me, ind, st_lines, is_tac, tac_lines, term_lines):
    outs = []
    if mh:
        hname = mh.group(2)
        stl = reindent_block(st_lines, ind + 4) if len(st_lines) > 1 else [st_lines[0].strip()]
        header = f"{' ' * ind}have {hname} : {stl[0].strip()}"
        more = stl[1:]
        if is_tac:
            block = reindent_block(tac_lines, ind + 2) if len(tac_lines) > 1 or tac_lines[0].startswith(' ') else [' ' * (ind + 2) + tac_lines[0].strip()]
            text = '\n'.join([header] + more[:-1] + [(more[-1] if more else header) + ' := by'])
            if more:
                text = '\n'.join([header] + more[:-1] + [more[-1] + ' := by'])
            else:
                text = header + ' := by'
            outs.append(text + '\n' + '\n'.join(block))
        else:
            tl = reindent_block(term_lines, ind + 2) if len(term_lines) > 1 else [' ' * (ind + 2) + term_lines[0].strip()]
            text = ('\n'.join([header] + more) + ' :=') if more else header + ' :='
            if len(term_lines) == 1 and len(text) + 1 + len(term_lines[0].strip()) <= 100:
                outs.append(text + ' ' + term_lines[0].strip())
            else:
                outs.append(text + '\n' + '\n'.join(tl))
    else:
        if is_tac:
            outs.append('\n'.join(reindent_block(tac_lines, ind)))
            stl = [l.strip() for l in st_lines]
            outs.append(f"{' ' * ind}exact show {' '.join(stl)} by\n" + '\n'.join(reindent_block(tac_lines, ind + 2)))
        else:
            tl = [l.strip() for l in term_lines]
            outs.append(f"{' ' * ind}exact {' '.join(tl)}" if len(tl) == 1 else
                        f"{' ' * ind}exact\n" + '\n'.join(reindent_block(term_lines, ind + 2)))
    return outs


def main():
    res = json.load(open(sys.argv[1], encoding='utf8'))
    maxlines = int(sys.argv[2])
    scratch = HERE / 'inline_have_scratch.lean'
    only = set(sys.argv[3:])
    for x in res:
        if x['kind'] not in ('lemma', 'theorem') or x['user_mod'] != x['mod'] or PAPER.search(x['name'].split('.')[-1]):
            continue
        if only and x['name'] not in only:
            continue
        p = GS / f"{x['mod']}.lean"
        s = p.read_text(encoding='utf8')
        texts = rewrites(s, x, maxlines)
        if not texts:
            continue
        for k, new in enumerate(texts):
            if ph.compiles(new, scratch):
                p.write_text(new, encoding='utf8', newline='\n')
                print(f"{x['mod']}.{x['name']}: inlined (form {k}, {x['lines']} lines)", flush=True)
                break
        else:
            print(f"{x['mod']}.{x['name']}: kept", flush=True)


main()
