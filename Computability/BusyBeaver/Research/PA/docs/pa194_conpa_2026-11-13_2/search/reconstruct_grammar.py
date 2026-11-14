#!/usr/bin/env python3
"""Bind the recorded search winner to the final machine grammar, without search."""
from pathlib import Path
import hashlib
import json
P = Path(__file__).resolve().parent
D = json.loads((P / 'separate_input.json').read_text())
terms = [tuple(t) if isinstance(t, list) else t for t in D['terminals']]
word = list(map(int, (P / 'winner.word').read_text().split()))
shape = [tuple(map(int, line.split())) for line in (P / 'winner.shape').read_text().splitlines()]
if word != D['word']:
    raise ValueError('Search changed the emitter word')
values = [terms[t] for t in word]
for a, b in shape:
    if not (0 <= a < len(values) and 0 <= b < len(values)):
        raise ValueError('Invalid postorder child')
    values.append((values[a], values[b]))
rules, identities = {}, {}
def encode(t):
    if not (isinstance(t, tuple) and len(t) == 2):
        return t
    if t in identities:
        return identities[t]
    children = [encode(x) for x in t]
    name = 'g' + str(len(rules))
    identities[t] = name
    rules[name] = children
    return name
root = encode(values[-1])
result = {'root': root, 'rules': rules}
text = json.dumps(result, indent=2, sort_keys=True) + '\n'
expected = P.parent / 'pa194/grammar.json'
if text.encode() != expected.read_bytes():
    raise ValueError('Recorded winner differs from delivered grammar')
print(json.dumps({'status':'PASS', 'macro_tokens':len(word),
                  'recorded_iteration_slots':6245219,
                  'grammar_sha256':hashlib.sha256(text.encode()).hexdigest()}, indent=2))
