#!/usr/bin/env python3
"""Independently replay the pinned Lean tree and the two literal path edits."""
from pathlib import Path
import hashlib, json, re
HERE = Path(__file__).resolve().parent
program = HERE / 'Program.lean'
raw = program.read_bytes()
if hashlib.sha256(raw).hexdigest() != 'abc6f530495511226b17a9a2feff9a015c7bf972de292c241c6a15af0b490411':
    raise ValueError('Program.lean hash mismatch')
text = raw.decode(); env = {}
def atom(s):
    if s.startswith('.leaf'):
        m = re.fullmatch(r'\.leaf \(\.(\w+)(?: (\d+))?\)', s)
        if not m: raise ValueError(s)
        return ('leaf', {'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}[m[1]], int(m[2]) if m[2] else None)
    return env[s]
for name, body in re.findall(r'^def (\w+) : Tree := \.node (.+)$', text, re.M):
    parts = re.findall(r'\.leaf \(\.(?:inc|dec|breakTo|continueTo) \d+\)|\.leaf \(\.halt\)|[A-Za-z]\w*', body)
    if len(parts) != 2: raise ValueError((name, body))
    env[name] = (atom(parts[0]), atom(parts[1]))
if re.findall(r'^def trie : Tree := (\w+)\s*$', text, re.M) != ['node172']: raise ValueError('root')
def leaves(t, path=''):
    if t[0] == 'leaf': yield [path, t[1], t[2]]
    else:
        yield from leaves(t[0], path+'0')
        yield from leaves(t[1], path+'1')
original = list(leaves(env['node172']))
def edit(rows, prefix, removed):
    gone = [i for i, row in enumerate(original) if row[0].startswith(prefix+'0')]
    if gone != removed: raise ValueError(('unexpected removed leaves', prefix, gone))
    return [[p[:len(prefix)]+p[len(prefix)+1:] if p.startswith(prefix+'1') else p, op, arg]
            for p, op, arg in rows if not p.startswith(prefix+'0')]
one = edit(original, '1010101110', [3773,3774,3775])
two = edit(original, '00011', [7,8])
both = edit(one, '00011', [7,8])
for name, rows in [('original',original), ('one',one), ('two',two), ('both',both)]:
    if rows != json.loads((HERE/(name+'.json')).read_text()): raise ValueError('site sequence mismatch: '+name)
    print(name, len(rows), 'rows verified')
