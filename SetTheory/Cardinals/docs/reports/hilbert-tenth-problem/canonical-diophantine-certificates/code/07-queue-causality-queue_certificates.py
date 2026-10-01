#!/usr/bin/env python3
"""Exact causal Diophantine certificates for cyclic tag systems.

All witnesses are nonnegative integers.  The JSON residual roots denote one
ordinary integer polynomial: the sum of their squares.  Intermediate circuit
nodes are definitions, NOT additional existentially quantified variables.
Python 3.10+, standard library only.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from math import prod, factorial
from typing import Iterable, Sequence
import argparse
import json
from pathlib import Path


def bits(word: str) -> tuple[int, ...]:
    if any(c not in '01' for c in word):
        raise ValueError('a binary word may contain only 0 and 1')
    return tuple(int(c) for c in word)


def code(word: Sequence[int], base: int = 2) -> int:
    if base < 2 or any(not isinstance(a, int) or not 0 <= a < base for a in word):
        raise ValueError('invalid base or digit')
    return sum(a * base**i for i, a in enumerate(word))


@dataclass(frozen=True)
class CyclicTag:
    appendants: tuple[tuple[int, ...], ...]

    def __post_init__(self) -> None:
        if not self.appendants:
            raise ValueError('at least one appendant is required')
        for word in self.appendants:
            code(word)

    @classmethod
    def parse(cls, words: Sequence[str]) -> 'CyclicTag':
        return cls(tuple(bits(w) for w in words))

    def appendant(self, t: int) -> tuple[int, ...]:
        return self.appendants[t % len(self.appendants)]

    def run(self, initial: Sequence[int], horizon: int) -> tuple[list[tuple[int, ...]], list[int]]:
        if horizon < 0:
            raise ValueError('horizon must be nonnegative')
        code(initial)
        word = tuple(initial)
        states, read = [word], []
        for t in range(horizon):
            if not word:
                break
            bit = word[0]
            read.append(bit)
            word = word[1:] + (self.appendant(t) if bit else ())
            states.append(word)
        return states, read


class Circuit:
    """A topologically ordered arithmetic DAG with integer constants."""
    def __init__(self, names: Sequence[str]):
        if len(set(names)) != len(names):
            raise ValueError('duplicate variable names')
        self.names = list(names)
        self.nodes: list[dict] = []
        self.degrees: list[int] = []
        self._constants: dict[int, int] = {}
        self.variables = [self._node({'op': 'var', 'index': i}, 1) for i in range(len(names))]

    def _node(self, item: dict, degree: int) -> int:
        i = len(self.nodes)
        self.nodes.append(item)
        self.degrees.append(degree)
        return i

    def const(self, value: int) -> int:
        if not isinstance(value, int):
            raise TypeError('constants must be integers')
        if value not in self._constants:
            self._constants[value] = self._node({'op': 'const', 'value': str(value)}, 0)
        return self._constants[value]

    def add(self, a: int, b: int) -> int:
        return self._node({'op': 'add', 'args': [a, b]}, max(self.degrees[a], self.degrees[b]))

    def sub(self, a: int, b: int) -> int:
        return self._node({'op': 'sub', 'args': [a, b]}, max(self.degrees[a], self.degrees[b]))

    def mul(self, a: int, b: int) -> int:
        return self._node({'op': 'mul', 'args': [a, b]}, self.degrees[a] + self.degrees[b])

    def scale(self, a: int, value: int) -> int:
        return self.mul(a, self.const(value))

    def export(self, roots: Sequence[int], kind: str, metadata: dict, witness: Sequence[int] | None = None) -> dict:
        result = {
            'format': 'integer-polynomial-circuit-v1',
            'domain': 'nonnegative integers',
            'kind': kind,
            'variables': self.names,
            'nodes': self.nodes,
            'residual_roots': list(roots),
            'combination': 'sum_of_squares',
            'degree_upper_bound': 2 * max((self.degrees[i] for i in roots), default=0),
            'metadata': metadata,
        }
        if witness is not None:
            if len(witness) != len(self.names) or any(x < 0 for x in witness):
                raise ValueError('invalid witness')
            result['witness'] = [str(x) for x in witness]
        return result


def evaluate(certificate: dict, witness: Sequence[int]) -> tuple[int, list[int]]:
    if len(witness) != len(certificate['variables']) or any(type(x) is not int or x < 0 for x in witness):
        raise ValueError('witness must have the prescribed number of natural coordinates')
    values: list[int] = []
    for node in certificate['nodes']:
        op = node['op']
        if op == 'const':
            value = int(node['value'])
        elif op == 'var':
            value = witness[node['index']]
        else:
            a, b = (values[i] for i in node['args'])
            value = a + b if op == 'add' else a - b if op == 'sub' else a * b
        values.append(value)
    residuals = [values[i] for i in certificate['residual_roots']]
    return sum(r*r for r in residuals), residuals


def stream_values(program: CyclicTag, initial: Sequence[int], read: Sequence[int], terminal: Sequence[int] = ()) -> dict:
    """Evaluate the formulas without constructing a circuit (also for bad bits)."""
    T, n = len(read), len(initial)
    length = n
    guard = 1
    scale_prefix = 1
    appended_code = 0
    lengths = []
    for t, bit in enumerate(read):
        lengths.append(length)
        guard *= length
        app = program.appendant(t)
        appended_code += code(app) * bit * scale_prefix
        scale_prefix *= 1 + ((1 << len(app)) - 1) * bit
        length += len(app) * bit - 1
    content = (code(initial) + (1 << n) * appended_code
               - sum(b << i for i, b in enumerate(read))
               - (1 << T) * code(terminal))
    return {'length_residual': length - len(terminal), 'content_residual': content,
            'guard': guard, 'prefix_lengths': lengths,
            'boolean_residuals': [b*(b-1) for b in read]}


def stream_witness(program: CyclicTag, initial: Sequence[int], T: int, terminal: Sequence[int] = ()) -> list[int] | None:
    states, read = program.run(initial, T)
    if len(read) != T or states[-1] != tuple(terminal):
        return None
    guard = prod(len(s) for s in states[:-1])
    return read + [guard - 1]


def compile_stream(program: CyclicTag, initial: Sequence[int], T: int,
                   terminal: Sequence[int] = (), *, zero_slack: bool = False,
                   attach_witness: bool = True) -> dict:
    """T bits + one slack, degree <= max(4, 2T), O(T) DAG size.

    The optional zero_slack version has T variables and a larger bounded
    interpolation circuit.  T is a metalevel horizon, never a variable exponent.
    """
    if T < 1:
        raise ValueError('this compiler requires T >= 1; time zero is a constant test')
    code(initial); code(terminal)
    names = [f'b_{i}' for i in range(T)] + ([] if zero_slack else ['u'])
    c = Circuit(names)
    one = c.const(1)
    length = c.const(len(initial))
    guard = one
    prefix = one
    appended = c.const(0)
    read_code = c.const(0)
    roots = []
    lengths = []
    for t, b in enumerate(c.variables[:T]):
        roots.append(c.mul(b, c.sub(b, one)))
        lengths.append(length)
        guard = c.mul(guard, length)
        app = program.appendant(t)
        appended = c.add(appended, c.scale(c.mul(b, prefix), code(app)))
        prefix = c.mul(prefix, c.add(one, c.scale(b, (1 << len(app)) - 1)))
        length = c.add(c.sub(length, one), c.scale(b, len(app)))
        read_code = c.add(read_code, c.scale(b, 1 << t))
    roots.append(c.sub(length, c.const(len(terminal))))
    roots.append(c.sub(c.add(c.const(code(initial)), c.scale(appended, 1 << len(initial))),
                       c.add(read_code, c.const((1 << T) * code(terminal)))))
    if zero_slack:
        max_len = max(map(len, program.appendants))
        H = max(1, len(initial) + T * max(0, max_len - 1))
        for length_node in lengths:
            vanishing = one
            for r in range(1, H + 1):
                vanishing = c.mul(vanishing, c.sub(length_node, c.const(r)))
            roots.append(vanishing)
    else:
        roots.append(c.sub(c.sub(guard, c.variables[-1]), one))
    witness = stream_witness(program, initial, T, terminal) if attach_witness else None
    if zero_slack and witness is not None:
        witness = witness[:-1]
    return c.export(roots, 'cyclic-tag-zero-slack' if zero_slack else 'cyclic-tag-causal-stream',
                    {'appendants': [''.join(map(str, a)) for a in program.appendants],
                     'initial': ''.join(map(str, initial)), 'terminal': ''.join(map(str, terminal)),
                     'horizon': T}, witness)


def compile_quartic(program: CyclicTag, initial: Sequence[int], T: int,
                    *, attach_witness: bool = True) -> dict:
    """Exact first emptying: 3T-2 natural variables; 3T quadratic residuals."""
    if T < 1:
        raise ValueError('T must be positive')
    code(initial)
    names = [name for i in range(1, T) for name in (f'v_{i}', f's_{i}')] + [f'q_{i}' for i in range(T)]
    c = Circuit(names)
    v = [c.const(code(initial))] + c.variables[:2*(T-1):2] + [c.const(0)]
    s = [c.const(1 << len(initial))] + c.variables[1:2*(T-1):2] + [c.const(1)]
    qs = c.variables[2*(T-1):]
    roots = []
    for t, q in enumerate(qs):
        b = c.sub(v[t], c.scale(q, 2))
        app = program.appendant(t)
        roots.extend([
            c.mul(b, c.sub(b, c.const(1))),
            c.sub(c.sub(c.scale(v[t+1], 2), c.scale(q, 2)), c.scale(c.mul(b, s[t]), code(app))),
            c.sub(c.sub(c.scale(s[t+1], 2), s[t]), c.scale(c.mul(b, s[t]), (1 << len(app)) - 1)),
        ])
    states, read = program.run(initial, T) if attach_witness else ([], [])
    witness = None
    if attach_witness and len(read) == T and not states[-1]:
        witness = [x for word in states[1:-1] for x in (code(word), 1 << len(word))]
        witness += [code(word)//2 for word in states[:-1]]
    return c.export(roots, 'cyclic-tag-quartic',
                    {'appendants': [''.join(map(str, a)) for a in program.appendants],
                     'initial': ''.join(map(str, initial)), 'horizon': T}, witness)


def falling(x: int, d: int) -> int:
    if d < 0:
        raise ValueError('falling factorial order must be nonnegative')
    return prod(x-r for r in range(d))


def resource_guard(initial: Sequence[int], consumptions: Sequence[Sequence[int]],
                   productions: Sequence[Sequence[int]]) -> tuple[int, bool, list[tuple[int, ...]]]:
    if len(consumptions) != len(productions):
        raise ValueError('unequal event counts')
    dim = len(initial)
    if any(x < 0 for x in initial):
        raise ValueError('negative initial resource')
    marking = list(initial)
    G, legal = 1, True
    history = [tuple(marking)]
    for con, pro in zip(consumptions, productions):
        if len(con) != dim or len(pro) != dim or any(x < 0 for x in (*con, *pro)):
            raise ValueError('invalid resource event')
        legal = legal and all(x >= a for x, a in zip(marking, con))
        for x, a in zip(marking, con):
            G *= falling(x, a)
        marking = [x-a+b for x, a, b in zip(marking, con, pro)]
        history.append(tuple(marking))
    return G, legal, history


def tag_values(appendants: Sequence[Sequence[int]], deletion: int, initial: Sequence[int],
               consumed: Sequence[int], terminal: Sequence[int] = ()) -> dict:
    """Exact evaluation of the general d-tag formulas on alphabet digits.

    This routine evaluates the table interpolants on their digit domain.
    It is a direct formula checker, independent of the symbolic compiler below.
    """
    B = len(appendants)
    if deletion < 1 or len(consumed) % deletion:
        raise ValueError('invalid deletion number or consumed block length')
    for w in (*appendants, initial, consumed, terminal):
        code(w, B)
    T = len(consumed)//deletion
    length, prefix, appended, G = len(initial), 1, 0, 1
    lengths = []
    for j in range(T):
        lengths.append(length)
        G *= falling(length, deletion)
        app = appendants[consumed[deletion*j]]
        appended += code(app, B) * prefix
        prefix *= B**len(app)
        length += len(app) - deletion
    return {'length_residual': length-len(terminal),
            'content_residual': code(initial, B)+B**len(initial)*appended-code(consumed, B)-B**(deletion*T)*code(terminal, B),
            'guard': G, 'prefix_lengths': lengths}


def tag_run(appendants: Sequence[Sequence[int]], deletion: int, initial: Sequence[int], T: int) -> tuple[list[tuple[int, ...]], tuple[int, ...]]:
    word, consumed = tuple(initial), ()
    states = [word]
    for _ in range(T):
        if len(word) < deletion:
            break
        consumed += word[:deletion]
        word = word[deletion:] + tuple(appendants[word[0]])
        states.append(word)
    return states, consumed



def scaled_table_coefficients(values: Sequence[int]) -> list[int]:
    """Coefficients of (B-1)! times the degree < B table interpolant."""
    B = len(values)
    if B < 2 or any(type(v) is not int for v in values):
        raise ValueError('an integer table of size at least two is required')
    K = factorial(B-1)
    answer = [0]*B
    for a, value in enumerate(values):
        poly, denominator = [1], 1
        for b in range(B):
            if b == a:
                continue
            result = [0]*(len(poly)+1)
            for j, coefficient in enumerate(poly):
                result[j] -= b*coefficient
                result[j+1] += coefficient
            poly = result
            denominator *= a-b
        assert K % denominator == 0
        multiplier = value*(K//denominator)
        answer = [x+multiplier*y for x,y in zip(answer,poly)]
    return answer


def polynomial_at(c: Circuit, coefficients: Sequence[int], variable: int) -> int:
    """Integer-only Horner circuit, with no extra witness coordinates."""
    if not coefficients:
        return c.const(0)
    result = c.const(coefficients[-1])
    for coefficient in reversed(coefficients[:-1]):
        result = c.add(c.mul(result,variable),c.const(coefficient))
    return result


def compile_tag(appendants: Sequence[Sequence[int]], deletion: int,
                initial: Sequence[int], T: int, terminal: Sequence[int] = (),
                *, attach_witness: bool = True) -> dict:
    """Symbolic integer-polynomial d-tag compiler: d*T+1 natural variables.

    Table interpolation is cleared by K=(B-1)!, including every prefix product.
    No rational constants, division nodes, or unknown powers occur in the DAG.
    """
    B = len(appendants)
    if B < 2 or deletion < 1 or T < 1:
        raise ValueError('require alphabet size >= 2, deletion >= 1, and T >= 1')
    for word in (*appendants, initial, terminal):
        code(word,B)
    K = factorial(B-1)
    names = [f'z_{j}' for j in range(deletion*T)] + ['u']
    c = Circuit(names)
    digits, u = c.variables[:-1], c.variables[-1]
    one = c.const(1)
    roots = []
    for digit in digits:
        residual = one
        for a in range(B):
            residual = c.mul(residual,c.sub(digit,c.const(a)))
        roots.append(residual)
    mcoeff = scaled_table_coefficients([len(a) for a in appendants])
    acoeff = scaled_table_coefficients([code(a,B) for a in appendants])
    dcoeff = scaled_table_coefficients([B**len(a) for a in appendants])
    length = c.const(K*len(initial))
    lengths = []
    prefix, appended = one, c.const(0)
    for i in range(T):
        lengths.append(length)
        head = digits[deletion*i]
        mi = polynomial_at(c,mcoeff,head)
        ai = polynomial_at(c,acoeff,head)
        di = polynomial_at(c,dcoeff,head)
        appended = c.add(appended,c.scale(c.mul(ai,prefix),K**(T-i-1)))
        prefix = c.mul(prefix,di)
        length = c.add(c.sub(length,c.const(K*deletion)),mi)
    roots.append(c.sub(length,c.const(K*len(terminal))))
    read_code = c.const(0)
    for j, digit in enumerate(digits):
        read_code = c.add(read_code,c.scale(digit,B**j))
    content = c.sub(c.const(code(initial,B)),
                    c.add(read_code,c.const(B**(deletion*T)*code(terminal,B))))
    roots.append(c.add(c.scale(content,K**T),c.scale(appended,B**len(initial))))
    guard = c.const(falling(len(initial),deletion))
    for length_node in lengths[1:]:
        for r in range(deletion):
            guard = c.mul(guard,c.sub(length_node,c.const(K*r)))
    roots.append(c.sub(guard,c.scale(c.add(u,one),K**(deletion*(T-1)))))
    witness = None
    if attach_witness:
        states, consumed = tag_run(appendants,deletion,initial,T)
        if len(consumed) == deletion*T and states[-1] == tuple(terminal):
            G = prod(falling(len(word),deletion) for word in states[:-1])
            witness = list(consumed)+[G-1]
    return c.export(roots,'deletion-tag-causal-stream',
                    {'alphabet_size':B,'deletion':deletion,
                     'appendants':[list(a) for a in appendants],
                     'initial':list(initial),'terminal':list(terminal),'horizon':T},witness)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--appendants', nargs='+', default=['10', ''])
    parser.add_argument('--initial', default='1')
    parser.add_argument('--time', type=int, default=3)
    parser.add_argument('--mode', choices=['stream', 'quartic', 'zero-slack'], default='stream')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--no-witness', action='store_true',
                        help='construct the polynomial without running the tag system')
    args = parser.parse_args()
    p, w = CyclicTag.parse(args.appendants), bits(args.initial)
    if args.mode == 'quartic':
        cert = compile_quartic(p, w, args.time, attach_witness=not args.no_witness)
    else:
        cert = compile_stream(p, w, args.time, zero_slack=args.mode == 'zero-slack',
                              attach_witness=not args.no_witness)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(cert, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'output': str(args.output), 'variables': len(cert['variables']),
                      'residuals': len(cert['residual_roots']), 'degree_bound': cert['degree_upper_bound'],
                      'witness_found': 'witness' in cert}, indent=2))

if __name__ == '__main__':
    main()
