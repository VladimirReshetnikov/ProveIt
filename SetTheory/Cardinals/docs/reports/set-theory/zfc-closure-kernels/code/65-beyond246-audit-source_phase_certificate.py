#!/usr/bin/env python3
"""Exact arithmetic fetch and 220 literal register instructions to the phase.

Imported by probe_state204_safe_phase.py. No binary run of the very large
unary input prooflist is asserted: the fetch uses the inherited read/unpair
contract. The following register instructions are individually replayed from
the complete original Prog254.v decoder, without accelerated macros.
"""
from pathlib import Path
from math import isqrt
import re


def pair(x, y):
    return (x + y) * (x + y + 1) // 2 + y


def unpair(z):
    s = (isqrt(8 * z + 1) - 1) // 2
    y = z - s * (s + 1) // 2
    return s - y, y


def increment(pc):
    bits = list(pc)
    i = len(bits) - 1
    while i >= 0 and bits[i] == '1':
        bits[i] = '0'
        i -= 1
    if i < 0:
        return ''
    bits[i] = '1'
    return ''.join(bits)


def strip(pc, bit, count):
    i = len(pc)
    while count and i:
        i -= 1
        count -= pc[i] == bit
    return pc[:i]


def certificate(program):
    src = Path(program).read_text().split('Definition p254_tab', 1)[1]
    src = src.split('[', 1)[1].split('].', 1)[0]
    op = r'(?:CN|CI|CD|CB|CC) \d+|CH'
    tree = re.findall(r'\((' + op + r'),\s*(' + op + r')\)', src)
    assert len(tree) == 6459
    packed = pair(0, pair(0, 151)) + 1
    assert packed == 67611006
    command, rest = unpair(packed - 1)
    argument, tail = unpair(rest)
    assert (command, argument, tail) == (0, 0, 151)
    assert unpair(150) == (2, 14) and unpair(14) == (0, 4)
    assert unpair(3) == (2, 0) and unpair(0) == (0, 0)
    assert 4 * pair(0, 2) == 20 and 4 * pair(2, 20) == 1092
    regs = [0, 0, 0, 0, 2, 20, 0, 0, 151]
    initial = regs.copy()
    pc = '1111'  # Fresh MP body after read(A), read(D), and command dispatch.
    trace = []
    for step in range(1000):
        node, depth = 0, 0
        while True:
            bit = int(pc[depth]) if depth < len(pc) else 0
            edge = tree[node][bit].split()
            depth += 1
            if edge[0] != 'CN':
                break
            node = int(edge[1])
        leaf = (pc + '0' * depth)[:depth]
        kind = edge[0]
        r = int(edge[1]) if len(edge) > 1 else None
        if leaf == '1111111111':
            assert (step, kind, r, regs) == (
                220, 'CC', 2, [0, 2, 0, 0, 1, 0, 1, 0, 151])
            break
        trace.append({'step': step, 'leaf': leaf,
                      'instruction': edge, 'logical_before': regs.copy()})
        if kind == 'CI':
            regs[r] += 1
            pc = increment(leaf)
        elif kind == 'CD':
            if regs[r]:
                regs[r] -= 1
                pc = increment(leaf)
            else:
                pc = increment(strip(leaf, '0', 1))
        elif kind == 'CB':
            pc = increment(strip(leaf, '0', r))
        elif kind == 'CC':
            pc = strip(leaf, '1', r)
        else:
            raise AssertionError('Unexpected source halt')
    else:
        raise AssertionError('Source phase not reached within certificate bound')
    return {'starting_MP_root_logical': [0, 0, 0, 0, 2, 20, 0, 0, packed],
            'root_fetch': {'prooflist_minus_one': packed - 1,
                           'first_unpair': [command, rest],
                           'second_unpair': [argument, tail]},
            'after_fetch_and_dispatch_pc': '1111',
            'after_fetch_logical': initial,
            'literal_register_steps_after_fetch': len(trace),
            'phase_leaf': leaf, 'phase_logical': regs,
            'register_trace': trace,
            'theorem_code_2': 'C254.gen 0 C254.truth',
            'theorem_code_20': 'C254.mp theorem_code_2 (Code254.c254_k 2 0)',
            'tail_151': 'Two NIP(0) commands: 150=P(2,P(0,4)), 3=P(2,P(0,0))',
            'scope': 'Prepared original source phase; no mutant blank-reachability assertion'}
