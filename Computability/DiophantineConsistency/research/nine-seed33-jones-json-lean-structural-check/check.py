#!/usr/bin/env python3
"""Compare one pinned JSON macro graph to the checked Lean recipe source.

This is a narrow external parser and is not a Lean theorem or JSON semantics.
"""
import copy
import hashlib
import json
import re
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
D = P.parents[1]
J = D / 'research/nine-seed33-jones-compact-macro-prototype/recipe.json'
L = D / 'research/nine-seed33-jones-compact-recipe-scoped-check/src/DiophantineConsistency/Sign33MacroRecipe.lean'
rawj, rawl = J.read_bytes(), L.read_bytes()
H = lambda x: hashlib.sha256(x).hexdigest()
if H(rawj) != '06154f18e49d5ac3ca49add3a9b8bb03717f14590d2ef14f892d04b7dc3a75b3' or H(rawl) != '6da2e67714b495c92c79dd89ac4a5c89bb0d613a00d626c53b6ac7b479190b32':
    raise RuntimeError('input pin mismatch')

TOKEN = re.compile(r'\s*(⟨[0-9]+,\s*by\s+decide⟩|\.[A-Za-z]+|[0-9]+|Int|[():])')


def lean_expr(s):
    tokens = []
    pos = 0
    while pos < len(s):
        m = TOKEN.match(s, pos)
        if not m:
            raise ValueError(('unknown Lean token', s[pos:pos + 24]))
        tokens.append(m.group(1))
        pos = m.end()
    i = 0

    def take(expected=None):
        nonlocal i
        if i >= len(tokens):
            raise ValueError('unexpected end')
        t = tokens[i]
        i += 1
        if expected is not None and t != expected:
            raise ValueError(('expected token', expected, t))
        return t

    def expr():
        op = take()
        if op == '(':
            a = expr()
            take(')')
            return a
        if op in ('.fixedY', '.fixedZ', '.pcoef', '.expo', '.index'):
            return (op[1:],)
        if op in ('.input', '.ref'):
            t = take()
            m = re.fullmatch(r'⟨([0-9]+),\s*by\s+decide⟩', t)
            if not m:
                raise ValueError('invalid finite index')
            return (op[1:], int(m.group(1)))
        if op == '.lit':
            return ('lit', int(take()))
        if op == '.constant':
            take('(')
            n = int(take())
            take(':')
            take('Int')
            take(')')
            return ('const', n)
        if op in ('.add', '.sub', '.mul', '.pow', '.sumRange'):
            return (op[1:], expr(), expr())
        if op == '.sumStar':
            return ('sumStar', expr())
        raise ValueError(('unknown constructor', op))

    out = expr()
    if i != len(tokens):
        raise ValueError('trailing Lean tokens')
    return out


def json_expr(x, names, binder=None):
    if not isinstance(x, list) or not x or not isinstance(x[0], str):
        raise ValueError('malformed JSON expression')
    op = x[0]
    if op in ('const', 'lit', 'var') and len(x) == 2 and type(x[1]) is int and x[1] >= 0:
        return ({'const': 'const', 'lit': 'lit', 'var': 'input'}[op], x[1])
    if op == 'ref' and len(x) == 2 and x[1] in names:
        return ('ref', names[x[1]])
    if op == 'fixed' and len(x) == 2 and x[1] in ('y', 'z'):
        return ('fixed' + x[1].upper(),)
    if op in ('pcoef', 'expo', 'index') and len(x) == 2 and binder == (x[1], 'star' if op != 'index' else 'range'):
        return (op,)
    if op in ('add', 'sub', 'mul', 'pow') and len(x) == 3:
        return (op, json_expr(x[1], names, binder), json_expr(x[2], names, binder))
    if op == 'sum_range' and len(x) == 4 and binder is None and isinstance(x[1], str):
        return ('sumRange', json_expr(x[2], names), json_expr(x[3], names, (x[1], 'range')))
    if op == 'sum_star' and len(x) == 3 and binder is None and isinstance(x[1], str):
        return ('sumStar', json_expr(x[2], names, (x[1], 'star')))
    raise ValueError(('unknown JSON form or binder', x))


def compare(data, text):
    rows = data['nodes']
    if (len(rows) != 45 or data['inputs'] != 9 or data['output'] != 'output'
            or data['schema'] != 'named-ring-dag-with-finite-sum-macros-v1'
            or data['seed'] != 'SharingSeed33.seed CurrentWindowCarry2011.ports'
            or data['seed_type'] != 'Expr (Fin 34)'
            or data['coefficient_definitions'] != {
                'z': 'ExecutableJones.indexZ seed 0', 'y': 'ExecutableJones.indexY seed 0',
                'pcoef': 'ExecutableJones.pCoefficient seed k',
                'expo': 'ExecutableJones.codingExpo 33 4 k',
                'star': 'ExecutableJones.codingStar 33 4'}):
        raise ValueError('graph shape')
    block = re.search(r'^def recipe : Dag 45 := by\n(.*?)\n\n/--', text, re.M | re.S)
    if not block:
        raise ValueError('Lean recipe definition')
    body = block.group(1).splitlines()
    lines = re.findall(r'^  let d([0-9]+) : Dag ([0-9]+) := \.snoc d([0-9]+) \((.*)\)$', block.group(1), re.M)
    if len(body) != 47 or body[0] != '  let d0 : Dag 0 := .nil' or body[-1] != '  exact d45' or len(lines) != 45:
        raise ValueError('Lean DAG shape')
    names = {}
    for i, (row, (idx, size, previous, exp)) in enumerate(zip(rows, lines)):
        if (int(idx), int(size), int(previous)) != (i + 1, i + 1, i):
            raise ValueError('Lean stage order')
        if row['name'] in names or lean_expr(exp) != json_expr(row['expr'], names):
            raise ValueError(('node mismatch', i, row['name']))
        names[row['name']] = i
    if names.get(data['output']) != 44:
        raise ValueError('output index')
    return len(rows)


data = json.loads(rawj)
text = rawl.decode('utf-8')
count = compare(data, text)
for i in range(count):
    bad = copy.deepcopy(data)
    bad['nodes'][i]['expr'] = ['const', 987654321]
    try:
        compare(bad, text)
    except ValueError:
        continue
    raise RuntimeError(('failed mutation control', i))
controls = []
bad = copy.deepcopy(data)
bad['seed'] = 'wrong seed'
controls.append((bad, text))
bad = copy.deepcopy(data)
bad['coefficient_definitions']['expo'] = 'wrong exponent'
controls.append((bad, text))
controls.append((data, text.replace('let d1 : Dag 1 := .snoc d0', 'let d1 : Dag 1 := .snoc d1', 1)))
controls.append((data, text.replace('.input ⟨0, by decide⟩', '.input ⟨8, by decide⟩', 1)))
for bad_data, bad_text in controls:
    try:
        compare(bad_data, bad_text)
    except ValueError:
        continue
    raise RuntimeError('failed metadata or Lean-source mutation control')
print(json.dumps({'status': 'PASS_EXTERNAL_STRUCTURAL_COMPARISON', 'nodes': count,
                  'rejected_single_node_mutations': count, 'json_sha256': H(rawj),
                  'rejected_metadata_and_lean_mutations': len(controls), 'lean_sha256': H(rawl),
                  'scope': 'Pinned JSON AST versus pinned Lean recipe source; no Lean JSON parser or PDF semantics.'}, sort_keys=True))
