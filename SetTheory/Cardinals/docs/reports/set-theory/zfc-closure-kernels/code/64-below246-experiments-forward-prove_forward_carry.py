#!/usr/bin/env python3
"""Universal local proofs for an incomplete 244-state forward-carry proposal.

This is not a consistency machine: the exact collision certificate below
shows loss of the conditional branch under the inherited frame relation.
The symbolic rules are imported from the supplied 246-state research package.
"""
from pathlib import Path
import hashlib
import json
import os
import sys

HERE = Path(__file__).resolve().parent
BASE = Path(os.environ.get('ZFC246_BASE', str(HERE.parents[1] / 'context246' / 'zfc-context246')))
sys.path.insert(0, str(BASE / 'code'))
import check_macro_inductions as m


def derive(name, begin, end):
    """Use only the baseline checker's justified literal/induction rules."""
    c = begin.copy()
    cost, motion, trace = m.E(), m.E(), []
    for _ in range(1000):
        c.left, c.right = m.norm(c.left, c.state == 48 and c.side == 'L'), m.norm(c.right)
        if c.key() == end.key():
            return dict(name=name, status='PASS', universal=True, steps=str(cost),
                        head_motion=str(motion), trace=trace)
        answer = m.apply_list_induction(c, cost, motion, trace)
        if answer is None:
            cost, motion = m.literal_or_power(c, cost, motion, trace)
        else:
            cost, motion = answer
    raise AssertionError((name, 'symbolic proof did not close'))


def main():
    if not __debug__:
        raise SystemExit('Assertions are required; do not use -O.')
    source = BASE / 'machine' / 'zfc_prefix246_old.tm'
    assert hashlib.sha256(source.read_bytes()).hexdigest() == '303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee'
    m.TABLE[255, 0] = (1, 'L', 63)
    m.TABLE[255, 1] = (0, 'R', 95)
    for q in (112, 131):
        for b in (0, 1):
            del m.TABLE[q, b]
    assert len(m.TABLE) == 488
    assert all(t not in (112, 131) for w, d, t in m.TABLE.values())
    v = m.E.var('v')
    l, r = m.Context('arbitrary_left'), m.Context('arbitrary_right')
    for name, q, side, before, after in (
        ('seek73_block', 73, 'R', m.B(v), m.B(v)),
        ('carry95_block', 95, 'R', m.B(v), m.C(v)),
        ('return48_block', 48, 'L', m.B(v), m.B(v)),
    ):
        if side == 'R':
            begin = m.Conf(q, side, [l], before + [r])
            end = m.Conf(q, side, m.reverse(after) + [l], [r])
            motion = v + 2
        else:
            begin = m.Conf(q, side, m.reverse(before) + [l], [r])
            end = m.Conf(q, side, [l], after + [r])
            motion = (v + 2) * -1
        m.BLOCK_PROOFS[name] = m.prove(name, begin, end, v + 2, motion)
        m.DERIVED[q, side, 'B', side == 'L'] = (name, 'C' if q == 95 else 'B')
    word = m.prove_word_identity()
    x, y = m.E.var('x'), m.E.var('y')
    a, b = m.Blocks('B', 'pre'), m.Blocks('B', 'suf')
    l, z = m.Context('arbitrary_left'), m.Blank()
    positive = derive('positive_decrement',
        m.Conf(95, 'R', [l], [a, m.bit(0), m.bit(0), m.ones(x+1), b, z]),
        m.Conf(48, 'L', [m.bit(1), l], [a] + m.B(x) + [b, z]))
    zero = derive('zero_forward_carry',
        m.Conf(95, 'R', [l], [a, m.bit(0), m.bit(0)] + m.B(y) + [b, z]),
        m.Conf(48, 'L', [m.bit(1), l], [a] + m.B(m.E()) + m.B(y) + [b] + m.B(m.E(1)) + [z]))
    increment = derive('increment',
        m.Conf(73, 'R', [l], [a, m.bit(0), m.bit(0), m.ones(x), b, z]),
        m.Conf(48, 'L', [l], [a] + m.B(x+1) + [b] + m.B(m.E(1)) + [z]))
    out = dict(status='PASS', status_of_machine='INCOMPLETE; conditional branch collision',
        working_states=244, edited_rows={'255/0': [1, 'L', 63], '255/1': [0, 'R', 95]},
        removed_states=[112, 131], baseline_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        kernel_status='Ordinary symbolic-induction checker; no proof-assistant kernel endpoint.',
        block_theorems=list(m.BLOCK_PROOFS.values()), word_identity=word,
        macro_theorems=[positive, zero, increment])
    (HERE / 'forward-carry-inductions.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps({k: v for k, v in out.items() if k not in ('block_theorems', 'macro_theorems')}, indent=2))
    for theorem in out['macro_theorems']:
        print(theorem['name'], theorem['steps'], theorem['head_motion'])


if __name__ == '__main__':
    main()
