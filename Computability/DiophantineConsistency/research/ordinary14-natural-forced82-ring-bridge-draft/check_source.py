#!/usr/bin/env python3
"""Check source shape and finite ring controls, without invoking Lean."""
from pathlib import Path
import hashlib, json, random
P = Path(__file__).resolve().parent
D = P.parents[1]
def pin(path, expected):
    data = path.read_bytes()
    assert hashlib.sha256(data).hexdigest() == expected, str(path)
    return data
g82 = json.loads(pin(D / 'research/ordinary14-root74-natural-forced82/candidate.json',
                     '1532ea5ec5f8dee349353044b9618a2e8a633f618e6f7ef5f1d19630b53b6c8a'))
g86 = json.loads(pin(D / 'research/ordinary14-root74-natural-cancel86/candidate.json',
                     '0211a1bcac635af617090facdc3b7f98d18ad94579027df840532d87ae5a5170'))
ring = pin(P / 'RingNatural82To86.lean',
           '08e86ba4044b84a32ad7c2e496c61b454fcd4a5ee963b345d8fe75dc420c120e').decode()
model = pin(P / 'Natural82Model.lean',
            'e10b5e7dcc6169fd4730f3bf4e9058081efa1ac4e628de382dcbfc2dcf244854').decode()
assert g82['witnesses'] == g86['witnesses'] and g82['fixed_numerals'] == g86['fixed_numerals']
assert g82['domain'] == g86['domain'] == 'nonnegative integers'
assert len(g82['source']) == 82 and len(g86['source']) == 86
renames = {'f': 'n_f', 'r': 'n_r', 'y': 'n_y'}
expected = []
for n, op, x, y in g86['source']:
    if n in (*renames, 'zeta', 'g52'): continue
    if n == 'k': expected.extend([['kbase', '+', 'eta', 'n_zeta'], ['k', '+', 'kbase', 1]])
    elif n == 'r0': expected.append(['r0', '-', 'kbase', 'R'])
    else: expected.append([n, op, renames.get(x, x), renames.get(y, y)])
assert expected == g82['source']
for name, inp in renames.items(): assert [name, '+', inp, 1] in g86['source']
assert "fun j => if j = 3 ∨ j = 8 ∨ j = 11 then v j - 1 else v j" in ring
assert "theorem output_eval" in ring and "theorem restricted_eval" in ring and "theorem guard_eval" in ring
assert "def Related" in model and "def HasThreePredecessors" in model
assert "theorem exists_zero_iff_of_predecessors" in model
assert "(predecessors : ∀ v, InternalZero" in model
assert "theorem internalZero_iff_of_related" in model and "theorem related_embedding" in model
def calc(g, vals, modulus):
    e = vals.copy()
    for n, op, x, y in g['source']:
        x = x if type(x) is int else e[x]
        y = y if type(y) is int else e[y]
        e[n] = (x*y if op == '*' else x+y if op == '+' else x-y) % modulus
    return e
rng = random.Random(148286)
for modulus in (4, 17, 1009):
    for _ in range(100):
        a = {x: rng.randrange(-20, 21) for x in g82['witnesses'] + g82['fixed_numerals']}
        b = a.copy()
        for n in renames.values(): b[n] -= 1
        x, y = calc(g82, a, modulus), calc(g86, b, modulus)
        assert all(x[n] == y[n] for n in ('F0', 'F1', 'Fa', 'Fs', 'guard', 'out'))
print(json.dumps({'scope': 'source shape and finite ring controls only; no Lean or model theorem',
                  'input_translation_slots': [3, 8, 11], 'signed_modular_controls': 300,
                  'parent_rows': 86, 'candidate_rows': 82,
                  'existence_theorem_explicitly_assumes_predecessors': True}, sort_keys=True, indent=2))
