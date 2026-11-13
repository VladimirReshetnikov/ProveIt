#!/usr/bin/env python3
"""Enumerate degree-three-preserving positive-cut substitution sequences."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
HERE = Path(__file__).resolve().parent
raw = (HERE.parent / 'nine-sharing-sign31-sextic-candidate' / 'seed.json').read_bytes()
assert hashlib.sha256(raw).hexdigest() == '827740a7f65961bd1a04ae424f4c8873a636285d2b1410bb72d0bee7e3e9e6c1'
source = json.loads(raw)

def replace(t, index, rhs):
    if t[0] == 'var' and t[1] == index: return rhs
    if t[0] in ('var', 'port', 'num'): return t
    assert t[0] in ('add', 'sub', 'mul') and len(t) == 3
    return [t[0], replace(t[1], index, rhs), replace(t[2], index, rhs)]

def degree(t):
    if t[0] == 'var': return 1
    if t[0] in ('port', 'num'): return 0
    a, b = degree(t[1]), degree(t[2])
    if t[0] == 'mul': return a + b
    assert t[0] in ('add', 'sub')
    return max(a, b)

def nonnegative_syntax(t):
    if t[0] in ('var', 'port'): return True  # ports are natural
    if t[0] == 'num': return t[1] >= 0
    return t[0] in ('add', 'mul') and nonnegative_syntax(t[1]) and nonnegative_syntax(t[2])

terminal = []
visited = 0
def walk(rows, path):
    global visited
    visited += 1
    options = []
    for row in rows:
        e = row['expr']
        if row['kind'] != 'positive' or e[0] != 'sub' or e[1][0] != 'var': continue
        index, rhs = e[1][1], e[2]
        if not nonnegative_syntax(rhs): continue
        # Existing AST uses no recursive cut definitions.
        assert replace(rhs, index, ['num', -1]) == rhs
        new = [dict(other, expr=replace(other['expr'], index, rhs)) for other in rows if other is not row]
        if max(degree(other['expr']) for other in new) <= 3:
            options.append((row['gate'], new))
    if not options:
        terminal.append(path)
    for gate, new in options:
        walk(new, path + [gate])

walk(source['residuals'], [])
out = {'status': 'PASS_RESTRICTED_SYNTACTIC_ENUMERATION', 'source_sha256': hashlib.sha256(raw).hexdigest(), 'visited_sequence_nodes': visited, 'terminal_paths': sorted(terminal), 'maximum_cuts_removed': max(map(len, terminal)), 'scope': 'fixed positive subtraction rows; nonnegative add/mul RHS; no cancellation; sequential substitutions; residual syntactic degree <= 3'}
print(json.dumps(out, indent=2, sort_keys=True))
