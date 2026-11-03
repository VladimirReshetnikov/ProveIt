#!/usr/bin/env python3
"""Source and finite index review, not a Lean replay or model proof."""
from hashlib import sha256
from pathlib import Path
import json
import re
import subprocess
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is rejected')
ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / 'Lean/DiophantineConsistency'
RECEIPT = ROOT / 'reviews/adaptive-qm40-native-bounded-replay'
PINS = {
    'AdaptiveQM40Context': 'be48ed96bcb082715c99cd697bfa25ff21bd55aa789e868970b74e621422dece',
    'AdaptiveQM40Zeros': 'b90faa5bace82f3352b94c5d5fade8cc3477cab3017de5ac9dc35dc8a73ce482',
    'AdaptiveQM40Maps': '1f188ab84a8b545b4888c861e41d9e97b8d0f3752f32ffb6d1039d3a2ba8d3ce',
    'AdaptiveQM40Norm': '36dcc30e3e54afde0a1560a51b75107cf20c7f7925fc7d3302e6d593005b0c6d',
    'AdaptiveQM40Model': '51b92288131cac97f4c08dedf684587f21c2450a34d8a07a976a96178b5315ca',
    'AdaptiveQM40Checks': '3bdf7384a60cd8fe351395d5fe67b072d64571acc2b8d2f2325f75a4cf830f91',
}

def require(b, msg):
    if not b:
        raise ValueError(msg)

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

def check_sources():
    for name, pin in PINS.items():
        require(digest(MODEL / (name+'.lean')) == pin, 'workspace source: '+name)
        require(digest(RECEIPT / 'author/src/DiophantineConsistency' / (name+'.lean')) == pin,
                'author snapshot: '+name)
    for name, pin in {
        'ArithmeticAdaptiveQuotients2011.lean': '40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884',
        'ArithmeticSquareDivisibility.lean': 'f775c2050a794b1ea026cdec0950e42528260fa1d75a03f1ef625f258670e660',
    }.items():
        require(digest(MODEL / name) == pin, 'reviewed dependency source: '+name)
    require(digest(RECEIPT / 'terminal-observation.json') ==
            'd394d48c153d158b9f22d41642f3363ef4edc50ea343406e4ab163caee792d97', 'receipt')
    require(digest(RECEIPT / 'author/logs/AdaptiveQM40Model.log') ==
            'bd7779374a62ab0496c8444b1dfd1cb063c54987372940cf7e0e7045a4a80c5f', 'model log')
    require(digest(ROOT / 'research/adaptive-qm40-proof/verify_literal.py') ==
            '42fcda37bfba094571d429a045f5e4c1bc9961c16817a45670530d57dc10592a', 'literal checker')

check_sources()
context = (MODEL / 'AdaptiveQM40Context.lean').read_text()
def rest(name):
    match = re.search(r'^def '+name+r' : Fin 39 → Fin \d+ := !\[([^\]]+)\]$', context, re.M)
    require(match is not None, 'rest syntax: '+name)
    return list(map(int, match.group(1).split(',')))
old_rest, new_rest = rest('oldRest'), rest('newRest')
require(old_rest == [i for i in range(41) if i not in (24,30)], 'old rest coverage')
require(new_rest == [i for i in range(40) if i != 24], 'new rest coverage')

# These finite calculations independently mirror the reviewed definitions;
# they are not an evaluation or proof of Lean semantics.
old_index = [i if i < 1 else i+1 if i < 20 else i+2 for i in range(30)]
new_index = [i if i < 1 else i+1 for i in range(30)]
require(sorted(old_index) == [i for i in range(32) if i not in (1,21)], 'old residual coverage')
require(sorted(new_index) == [i for i in range(31) if i != 1], 'new residual coverage')
require(len(set(old_index)) == len(set(new_index)) == 30, 'residual collisions')

def project(v, t, i):
    return t if i == 24 else v[i] if i < 30 else v[i+1]
def extend(v, i):
    return v[15]*v[24] if i == 24 else v[15]*v[15] if i == 30 else v[i] if i < 30 else v[i-1]
old = list(range(1,42))
quotient = 3
old[24], old[30], old[34] = old[15]*quotient, old[15]**2, quotient**2-1
new = [project(old, quotient, i) for i in range(40)]
require(all(x > 0 for x in old+new), 'sample positivity')
require(old[24]**2 == old[30]*(1+old[34]) and new[24]**2 == 1+new[33], 'sample norm')
require(all(project(old, quotient, j) == old[i] for i,j in zip(old_rest,new_rest)), 'project rest')
require(all(extend(new, i) == new[j] for i,j in zip(old_rest,new_rest)), 'extend rest')
require([extend(new, i) for i in range(41)] == old, 'sample round trip')
require([project([extend(new,i) for i in range(41)], new[24], j) for j in range(40)] == new,
        'reverse round trip')

checker = ROOT / 'research/adaptive-qm40-proof/verify_literal.py'
out = subprocess.run([sys.executable, '-I', '-S', str(checker)], capture_output=True, text=True, check=False)
require(out.returncode == 0 and out.stdout.strip() ==
        'PASS: 40 named variables, 4 ports and all 166 Lean literal rows match the pinned DAG',
        'external literal check')
terminal = json.loads((RECEIPT / 'terminal-observation.json').read_text())
require(terminal['observed_completed_children'] == list(PINS), 'author completed children')
check_sources()
print(json.dumps({'status':'PASS_QM40_MODEL_SOURCE_REVIEW', 'old_common':len(old_index),
                  'new_common':len(new_index), 'rest_coordinates':len(old_rest),
                  'sample_quotient':quotient, 'external_literal_rows':166,
                  'scope':'source review and finite checks; no Lean replay or PDF binding'}, sort_keys=True))
