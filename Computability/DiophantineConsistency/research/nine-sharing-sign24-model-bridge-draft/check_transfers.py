#!/usr/bin/env python3
"""Check drafted old/new Lean residual expressions and row indices as text."""
import hashlib
import json
import re
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
old_path = here.parent / 'nine-sharing-sign25-octic-ell-candidate/seed.json'
new_path = here.parent / 'nine-sharing-sign24-octic-q3-candidate/seed.json'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(old_path) == 'c95637ae24a57dba0ae1113a8256ed6f12d33f416f035f9cd4f92cffdbf59fc8'
assert digest(new_path) == '24a6dcf05b96112cfa332aafe4790a367c44b9a0cc033a74197f92d3520ab865'
old, new = json.loads(old_path.read_bytes()), json.loads(new_path.read_bytes())
assert old['residuals'][0]['gate'] == 'q3'
old_rows, new_rows = old['residuals'][1:], new['residuals']
assert len(old_rows) == len(new_rows) == 15
lex = re.compile(r'\s*(Expr\.constant|Expr\.var|[0-9]+|p|ℤ|[()+*:\-])')
ports = ['beta', 'K0', 'MC', 'MF']

def parse(line):
    tokens = []
    position = 0
    while position < len(line):
        match = lex.match(line, position)
        assert match, (line[position:position+30], position)
        tokens.append(match.group(1))
        position = match.end()
    i = 0
    def take(expected=None):
        nonlocal i
        assert i < len(tokens)
        token = tokens[i]
        i += 1
        if expected is not None: assert token == expected, (token, expected)
        return token
    def rec(depth=0):
        assert depth <= 80
        take('(')
        if tokens[i] == 'Expr.var':
            take(); n = int(take()); assert 1 <= n <= 25; take(')')
            return ['var', n]
        if tokens[i] == 'Expr.constant':
            take(); take('('); value = take()
            if value == 'p':
                j = int(take()); assert 0 <= j < 4; out = ['port', ports[j]]
            else:
                out = ['num', int(value)]; take(':'); take('ℤ')
            take(')'); take(')'); return out
        a = rec(depth+1); op = take(); assert op in ('+', '-', '*')
        b = rec(depth+1); take(')')
        return [{'+': 'add', '-': 'sub', '*': 'mul'}[op], a, b]
    out = rec()
    assert i == len(tokens)
    return out

files = [here / f'Sign24Transfers{i:02}.lean' for i in range(3)]
sources = [p.read_text() for p in files]
for i, (a, b) in enumerate(zip(old_rows, new_rows)):
    name = a['gate']
    assert name == b['gate']
    text = sources[i // 5]
    for role, row, dimension in [('old', a, 26), ('new', b, 25)]:
        prefix = f'def {role}{name} (p : Fin 4 → ℤ) : Expr (Fin {dimension}) :=\n  '
        assert text.count(prefix) == 1
        line = text.split(prefix, 1)[1].split('\n', 1)[0]
        assert parse(line) == row['expr'], (role, name)
    assert f'((SharingSeed25Octic.remainingResiduals p).drop {i}).head? = some (old{name} p)' in text
    if i == 0:
        assert f'SharingSeed24Octic.firstResidual p = new{name} p' in text
    else:
        assert f'((SharingSeed24Octic.remainingResiduals p).drop {i-1}).head? = some (new{name} p)' in text
    assert text.count(f'theorem {name}_eval ') == 1
for text in sources: assert 'sorry' not in text and 'admit' not in text
print(json.dumps({'status': 'PASS_SOURCE_ROWS_ONLY', 'transfers': 15,
                  'source_sha256': {p.name: digest(p) for p in files},
                  'scope': 'AST/offset text check, not Lean compilation or an all-model bridge'},
                 sort_keys=True, indent=2))
