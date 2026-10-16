"""Inline definitions that have exactly one application in the corpus.

usage: python -X utf8 inline_defs.py defs_once.json [NAME ...]
For each candidate def D (same-module user only):
  * every mention of D inside a tactic lemma list (`simp [.., D, ..]`, `rw [..]`, `dsimp only [..]`, ...)
    or an `unfold`/`delta` name list is removed (an emptied `rw`/`unfold`/`delta` step is deleted);
  * the single remaining mention must be an application `D a1 .. an` with all explicit arguments
    (named arguments `(x := e)` are allowed); it becomes `(body[params := args] : Type[...])`,
    or `({ fields } : Type)` for a `where` definition, or just `(body)` for a `Prop`;
  * the definition (with its docstring) is deleted.
The module is elaborated after each inlining (prune_haves.compiles, no olean) and the inlining is
kept only if it compiles.  Prints one line per candidate.
"""
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
IDENT = re.compile(r"[A-Za-z_\u0370-\u03ff][\w'\u0370-\u03ff₀-₉]*")
OPEN, CLOSE = '([{⟨⦃', ')]}⟩⦄'
LISTTAC = re.compile(r"(simp_rw|simp_all|simp|dsimp|rw|rwa|rewrite|nth_rewrite\s+\d+|simpa|norm_num|field_simp|push_cast)"
                     r"(\s+only)?(\s*\[)$")


def blank_comments(t):
    out = list(t)
    for m in re.finditer(r'/-.*?-/|--[^\n]*', t, flags=re.S):
        for k in range(m.start(), m.end()):
            if out[k] != '\n':
                out[k] = ' '
    return ''.join(out)


def match_close(t, i):
    depth = 0
    for j in range(i, len(t)):
        if t[j] in OPEN:
            depth += 1
        elif t[j] in CLOSE:
            depth -= 1
            if depth == 0:
                return j
    return -1


def binders(sig):
    """[(kind, names, text)] for the leading binder groups, and the index where they end."""
    out, i = [], 0
    while True:
        while i < len(sig) and sig[i].isspace():
            i += 1
        if i >= len(sig) or sig[i] not in '({[⦃':
            return out, i
        j = match_close(sig, i)
        g = sig[i + 1:j]
        k = g.find(':')
        names = g[:k].split() if k > 0 and all(IDENT.fullmatch(x) for x in g[:k].split()) else []
        out.append((sig[i], names, sig[i:j + 1]))
        i = j + 1


def parse_def(s, name):
    hd = re.search(r"^(@\[[^\]]*\]\s*)?(private |protected )?(noncomputable )?(def|abbrev) " + re.escape(name)
                   + r"(?![\w'])", s, re.M)
    if not hd or hd.group(1):
        return None
    a = hd.start()
    doc = s.rfind('/--', 0, a)
    if doc != -1 and s[s.index('-/', doc) + 2:a].strip() == '':
        a = doc
    e = re.compile(r'\n\n(?=\S)').search(s, hd.end())
    end = (e.start() + 2) if e else len(s)
    blk = s[hd.end():end]
    bs, k = binders(blk)
    rest = blk[k:]
    m = re.match(r"\s*:\s*", rest)
    if not m:
        return None
    # the type runs to the depth-0 `:=` or `where`
    depth, i = 0, m.end()
    while i < len(rest):
        c = rest[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0 and rest.startswith(':=', i):
            return dict(start=a, end=end, binders=bs, type=rest[m.end():i].strip(), form='term',
                        body=rest[i + 2:].strip('\n').rstrip())
        elif depth == 0 and re.match(r"\bwhere\b", rest[i:]) and (i == 0 or not (rest[i - 1].isalnum() or rest[i - 1] == '_')):
            return dict(start=a, end=end, binders=bs, type=rest[m.end():i].strip(), form='where',
                        body=rest[i + 5:].strip('\n').rstrip())
        i += 1
    return None


def subst(text, sub):
    if not sub:
        return text
    pat = re.compile(r"(?<![\w'.])(" + '|'.join(map(re.escape, sub)) + r")(?![\w'₀-₉])")
    return pat.sub(lambda t: sub[t.group(1)] if IDENT.fullmatch(sub[t.group(1)]) else '(' + sub[t.group(1)] + ')', text)


def reindent(text, ind):
    lines = text.split('\n')
    tail = [l for l in lines[1:] if l.strip()]
    base = min((len(l) - len(l.lstrip()) for l in tail), default=0)
    out = [lines[0].strip()]
    for l in lines[1:]:
        out.append((' ' * ind + l[base:]) if l.strip() else '')
    return '\n'.join(out)


def inline_one(s, name):
    d = parse_def(s, name)
    if d is None:
        return None, 'unsupported definition form'
    short = name.split('.')[-1]
    cf = blank_comments(s)
    occ = [m for m in re.finditer(r"(?<![\w'.@])" + re.escape(short) + r"(?![\w'])", cf)
           if not (d['start'] <= m.start() < d['end'])]
    edits = []            # (start, end, replacement)
    apps = []
    for m in occ:
        line_start = cf.rfind('\n', 0, m.start()) + 1
        before = cf[line_start:m.start()]
        # inside a tactic lemma list?
        lb = cf.rfind('[', 0, m.start())
        in_list = False
        if lb != -1 and match_close(cf, lb) > m.start():
            pre = cf[max(0, lb - 40):lb + 1]
            if LISTTAC.search(pre.replace('\n', ' ')):
                # a list mention only when the whole item is the name
                rb0 = match_close(cf, lb)
                item_start = max(cf.rfind(',', lb, m.start()), lb) + 1
                item_end = cf.find(',', m.end(), rb0)
                item = cf[item_start:item_end if item_end != -1 else rb0].strip()
                in_list = item in (short, '← ' + short, '←' + short)
        if in_list:
            rb = match_close(cf, lb)
            items = [x for x in re.split(r',', s[lb + 1:rb])]
            keep = [x for x in items if x.strip() not in (short, '← ' + short, '←' + short)]
            if len(keep) == len(items):
                return None, 'unrecognised list mention'
            if keep:
                edits.append((lb + 1, rb, ','.join(keep).strip() if not keep[0].startswith(' ') else ','.join(keep).lstrip()))
            else:
                kw = LISTTAC.search(cf[max(0, lb - 40):lb + 1].replace('\n', ' '))
                tac = kw.group(1)
                if tac.startswith(('rw', 'rewrite', 'nth_rewrite', 'simp_rw')):
                    # delete the whole step when it is alone on its line
                    ls = s.rfind('\n', 0, lb) + 1
                    le = s.find('\n', rb)
                    le = len(s) if le < 0 else le
                    if s[ls:lb].strip() and re.fullmatch(r'\s*(rw|rewrite|simp_rw|nth_rewrite\s+\d+)\s*', s[ls:lb]) \
                            and re.fullmatch(r'\]\s*', s[rb:le]):
                        edits.append((ls, le + 1, ''))
                    else:
                        return None, 'emptied rewrite inside a line'
                else:
                    sp = lb
                    while sp > 0 and s[sp - 1] == ' ':
                        sp -= 1
                    edits.append((sp, rb + 1, ''))
            continue
        um = re.search(r"\b(unfold|delta)\b([^\n]*)$", before)
        if um and re.fullmatch(r"[\s\w'.]*", um.group(2)):
            ls = line_start
            le = s.find('\n', m.end())
            le = len(s) if le < 0 else le
            names = (um.group(2) + short + s[m.end():le]).split()
            names = [x for x in names if x != short]
            if names and names[0] != 'at':
                edits.append((ls + um.start(2), le, ' ' + ' '.join(names)))
            elif not s[ls:ls + um.start()].strip() and not names:
                edits.append((ls, le + 1, ''))
            else:
                return None, 'unfold with other parts'
            continue
        apps.append(m)
    if len(apps) != 1:
        return None, f'{len(apps)} applications'
    m = apps[0]
    # keep named vocabulary of statements: the application must sit inside a proof
    import stmtx
    heads = [h for h in re.finditer(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?"
                                    r"(?:theorem|lemma|def|abbrev|instance|structure)\b", s, re.M) if h.start() < m.start()]
    if heads:
        se = stmtx.statement_end(s, heads[-1].end())
        if se == -1 or m.start() < se:
            return None, 'used in a statement'
    explicit = [n for k, ns, _ in d['binders'] if k == '(' for n in ns]
    implicit = [n for k, ns, _ in d['binders'] if k in '{⦃' for n in ns]
    sub, p, count = {}, m.end(), 0
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
                    return None, 'named argument for an unknown binder'
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
        return None, 'partial application'
    ls = s.rfind('\n', 0, m.start()) + 1
    ind = len(s[ls:]) - len(s[ls:].lstrip()) + 4
    typ = subst(d['type'], sub)
    a0, b0 = m.start(), p
    # replace a surrounding `( ... )` rather than nesting another pair
    q = p
    while q < len(s) and s[q] in ' \t':
        q += 1
    if a0 > 0 and s[a0 - 1] == '(' and q < len(s) and s[q] == ')':
        a0, b0 = a0 - 1, q + 1
    if d['form'] == 'term':
        body = reindent(subst(d['body'], sub), ind + 1)
        repl = f'({body})' if typ == 'Prop' else f'({body} : {typ})'
    else:
        # fields of a multi-line structure instance must share one column: start on a fresh line
        fields = reindent(subst(d['body'], sub), ind + 3)
        repl = '\n' + ' ' * ind + '({ ' + fields.strip() + ' } : ' + typ + ')'
        while a0 > 0 and s[a0 - 1] == ' ':
            a0 -= 1
    edits.append((a0, b0, repl))
    edits.append((d['start'], d['end'], ''))
    new = s
    for a, b, r in sorted(edits, key=lambda x: -x[0]):
        new = new[:a] + r + new[b:]
    return re.sub(r'\n{3,}', '\n\n', new), 'ok'


def main():
    cands = json.load(open(sys.argv[1], encoding='utf8'))
    only = set(sys.argv[2:])
    scratch = HERE / 'inline_defs_scratch.lean'
    for x in cands:
        if x['user_mod'] != x['mod'] or (only and x['name'] not in only):
            continue
        p = GS / f"{x['mod']}.lean"
        s = p.read_text(encoding='utf8')
        new, why = inline_one(s, x['name'])
        if new is None:
            print(f"{x['mod']}.{x['name']}: skipped ({why})", flush=True)
            continue
        if ph.compiles(new, scratch):
            p.write_text(new, encoding='utf8', newline='\n')
            print(f"{x['mod']}.{x['name']}: inlined ({x['lines']} lines)", flush=True)
        else:
            print(f"{x['mod']}.{x['name']}: kept (inlined form does not compile)", flush=True)


main()
