"""Statement extraction for Lean declarations: the text between the declaration name and the `:=`
that starts its proof.  A `:=` closes the statement only at bracket depth 0 and when it does not
belong to a `let`/`have` binding inside the statement (those are paired with the nearest unpaired
`let`/`have` keyword).  Comments and string literals are skipped."""
import re

OPEN, CLOSE = '([{⟨', ')]}⟩'
KW = re.compile(r"(?<![\w.'])(let|have)(?![\w'])")


def statement_end(s, i):
    """Index of the proof-introducing `:=` at or after position i, or -1."""
    depth = 0
    pending = 0
    n = len(s)
    while i < n:
        c = s[i]
        if s.startswith('--', i):
            j = s.find('\n', i)
            i = n if j < 0 else j
            continue
        if s.startswith('/-', i):
            j = s.find('-/', i + 2)
            i = n if j < 0 else j + 2
            continue
        if c == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            i = j + 1
            continue
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0:
            m = KW.match(s, i)
            if m:
                pending += 1
                i = m.end()
                continue
            if s.startswith(':=', i):
                if pending:
                    pending -= 1
                else:
                    return i
                i += 2
                continue
        i += 1
    return -1


def statement(s, i):
    j = statement_end(s, i)
    return None if j < 0 else s[i:j]


IDENT = re.compile(r"[A-Za-z_Ͱ-Ͽ][\w'Ͱ-Ͽ]*")


def binder_names(stmt):
    """Names bound by the leading binder groups `(x y : T)`, `{x : T}`, `[h : C]`, `⦃x : T⦄` of a
    signature, i.e. the balanced groups before the depth-0 `:`.  Type ascriptions inside the
    statement proper are not binders and are not returned."""
    names = []
    i, n = 0, len(stmt)
    while True:
        while i < n and stmt[i].isspace():
            i += 1
        if i >= n or stmt[i] not in '({[⦃':
            return names
        depth, j = 0, i
        while j < n:
            if stmt[j] in '({[⦃':
                depth += 1
            elif stmt[j] in ')}]⦄':
                depth -= 1
                if depth == 0:
                    break
            j += 1
        group = stmt[i + 1:j]
        k = group.find(':')
        if k > 0 and not group.startswith(':'):
            head = group[:k]
            if all(IDENT.fullmatch(t) for t in head.split()):
                names += [t for t in head.split() if t not in names]
        i = j + 1


def normalise(stmt):
    """Whitespace collapsed, `↦` read as `=>`, leading binder names renamed positionally."""
    stmt = ' '.join(stmt.replace('↦', '=>').split())
    ren = {n: f'v{k}' for k, n in enumerate(binder_names(stmt))}
    return re.sub(r"(?<![\w.'])" + IDENT.pattern, lambda t: ren.get(t.group(0), t.group(0)), stmt)
