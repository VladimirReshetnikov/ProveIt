#!/usr/bin/env python3
"""Reproduce symbolic runtime audits, not a blank-start correctness certificate.

The symbolic executor is the busy-beaver project's pinned design prototype.
Its register-box summaries remain symbolic in all register values; only the
finite header gap is specialized for the 36/37 cases.  No Coq is invoked.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json
import re

if not __debug__:
    raise RuntimeError('Run with assertions enabled; Python -O and -OO are not supported.')

ROOT = Path(__file__).resolve().parent
HASHES = {
    'zfc_254.tm': 'd655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb',
    'zfc_253.tm': '84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95',
    'Prog254.v': '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746',
    'symexec.py': '5bf83da419c47b9c8d79fcc755e40048f599255c2f1b2cb4656dc04bb02bb85d',
}
for filename, expected in HASHES.items():
    assert hashlib.sha256((ROOT/'sources'/filename).read_bytes()).hexdigest() == expected, filename

base = {}
for line in (ROOT/'sources/zfc_254.tm').read_text().splitlines():
    if not line or line.startswith('#'):
        continue
    q, b, w, d, target = line.split()
    base[q, int(b)] = int(w), d, target
assert len(base) == 508
# This is the already-known runtime-only 252-state quotient in old 254 labels.
# Its prescribed exploratory start is old state 64.  It has no certified boot.
table = {key: val for key, val in base.items() if key[0] not in ('5', '8')}
table['3', 0] = 0, 'L', '48'
working = {q for q, bit in table}
assert len(working) == 252 and len(table) == 504
assert all(t in working or t == '254' for w, d, t in table.values())
box_states = {0, 1, 2, 3, 4, 6, 28, 31, 38, 40, 43, 44, 48, 56, 59, 60,
              63, 64, 69, 73, 75, 83, 85, 95, 97, 109, 112, 131}
protected = {(str(q), b) for q in box_states for b in (0, 1)} - {('3', 0)}
assert len(protected) == 55
assert all(table[pair] == base[pair] for pair in protected)

body = (ROOT/'sources/Prog254.v').read_text().split('Definition p254_tab', 1)[1]
body = body.split('[', 1)[1].split('].', 1)[0]
edge = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
nodes = re.findall(r'\((' + edge + r'),\s*(' + edge + r')\)', body)
assert len(nodes) == 6459
source = (ROOT/'sources/symexec.py').read_text()
source = 'SKIP =' + source.split('SKIP =', 1)[1].split('paths = json.load', 1)[0]
ns = {'T': table, 'D0': 38}
exec(compile(source, 'pinned_upstream_symexec.py', 'exec'), ns)
affine_tape_R = ns['tape_R']

def fixed_tape_R(p, extra, effects):
    return ns['cells'](p) + [('r', 0, 0, ns['D0'] + extra - len(p)),
                            ('b', 1), ('box', ('plain',) + effects)]

phys = (6, 7, 0, 2, 1, 8, 4, 3, 5)
cases = []
stack = [('CN 0', '')]
leaves = 0
while stack:
    instruction, p = stack.pop()
    kind, *args = instruction.split()
    arg = int(args[0]) if args else None
    if kind == 'CN':
        left, right = nodes[arg]
        stack.extend([(right, p + '1'), (left, p + '0')])
        continue
    leaves += 1
    for branch in ('z', 'p') if kind == 'CD' else ('-',):
        effects = ()
        if kind == 'CI' or kind == 'CD' and branch == 'p':
            q = ns['inc'](p)
            effects = (('inc' if kind == 'CI' else 'dec', phys[arg]),)
        elif kind == 'CD':
            q = ns['inc'](ns['strip']('0', 1, p))
            effects = (('dec0', phys[arg]),)
        elif kind == 'CB':
            q = ns['inc'](ns['strip']('0', arg, p))
        elif kind == 'CC':
            q = ns['strip']('1', arg, p)
        else:
            assert kind == 'CH'
            q = ''
        cases.append((p, instruction, branch, effects, q))
assert leaves == 6460 and len(cases) == 8391
assert max(map(lambda c: len(c[0]), cases)) == 34
pc_words = sorted({int(p.ljust(34, '0'), 2) for p, *_ in cases})
assert len(pc_words) == 6460
(ROOT/'results').mkdir(exist_ok=True)
(ROOT/'results/pc_words_34.txt').write_text(''.join(str(word) + '\n' for word in pc_words))

def audit(gap, affine):
    ns['D0'] = gap
    ns['tape_R'] = affine_tape_R if affine else fixed_tape_R
    counts, failures = Counter(), []
    maximum = 0
    for p, instruction, branch, effects, q in cases:
        if q is None:
            expected = ns['canon']([('b', 1)], [('r', 0, int(affine), gap + 1),
                                   ('b', 1), ('box', ('plain',) + effects)])
        else:
            expected = ns['canon']([('b', 1)], ns['tape_R'](q, 0, effects))
        try:
            result = ns['run']('96', [('b', 1)], ns['tape_R'](p, 0, ()),
                               branch, expected, fuel=2000)
            status = 'pass' if result[0] == ('halt' if instruction == 'CH' else 'ok') else 'wrong_status'
            maximum = max(maximum, result[1])
        except (ns['Fail'], KeyError) as error:
            status = str(error)
        counts[status] += 1
        if status != 'pass':
            failures.append({'path': p, 'op': instruction, 'branch': branch, 'result': status})
    return {'gap': f'{gap}+n, n>=0' if affine else gap,
            'run_parameter': 'arbitrary natural n' if affine else 'specialized to zero',
            'counts': dict(counts), 'max_executor_steps': maximum,
            'failures': failures}

report = {'scope': 'Python symbolic runtime audit; no blank boot or Coq build claimed',
          'states': len(working), 'protected_box_rows_unchanged': len(protected),
          'program_internal_nodes': len(nodes), 'program_leaves': leaves,
          'branch_cases': len(cases), 'fuel_per_case': 2000,
          'results': [audit(36, False), audit(37, False), audit(38, True)]}
print(json.dumps(report, indent=2))
assert all(row['counts'] == {'pass': len(cases)} for row in report['results'])
