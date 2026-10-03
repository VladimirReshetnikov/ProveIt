#!/usr/bin/env python3
"""Complete paid SLPs for the pinned finite connected-network certificate.

Prototype APIs build(source, program, horizon, m=5, mode='row_diagonal'),
checked(source, packet), evaluate(source, packet, assignment, *, natural=True).
Program is an exact JSON descriptor; source is an explicitly supplied file.
All witnesses/parameters and all source residuals remain unchanged.
"""
from __future__ import annotations
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
import importlib.util
import json
import os
import py_compile
from pathlib import Path
import random
import sys
import tempfile

SOURCE_SHA256 = '3dd949eae682c7b57d2c3ee9f8e86dad5d40c156a33d6010568868bc1b9173e4'
MODES = ('direct', 'column_diagonal', 'row_diagonal', 'row_complement')
SCHEMA = 'connected-cross-routing-complete-slp-v1'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def exact_equal(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(exact_equal(a[k], b[k]) for k in a)
    if type(a) in (list, tuple):
        return len(a) == len(b) and all(exact_equal(x, y) for x, y in zip(a, b))
    return a == b


def require(condition, message):
    if not condition:
        raise ValueError(message)


def natural(n, name):
    require(type(n) is int and n >= 0, name + ' must be an exact natural')
    return n


@lru_cache(maxsize=8)
def _load(path):
    spec = importlib.util.spec_from_file_location('_connected_cross_routing_pinned', path)
    module = importlib.util.module_from_spec(spec)
    prior = sys.modules.get(spec.name)
    sys.modules[spec.name] = module
    try:
        data = Path(path).read_bytes()
        require(hashlib.sha256(data).hexdigest() == SOURCE_SHA256, 'execution source SHA256 mismatch')
        exec(compile(data, path, 'exec'), module.__dict__)
    finally:
        if prior is None:
            sys.modules.pop(spec.name, None)
        else:
            sys.modules[spec.name] = prior
    return module


def _module(source):
    path = Path(source).resolve()
    require(digest(path) == SOURCE_SHA256, 'source SHA256 mismatch')
    return _load(str(path))


def _program(mod, desc):
    require(type(desc) is dict and set(desc) == {'dimension', 'start', 'instructions'}, 'program fields')
    natural(desc['dimension'], 'dimension'); natural(desc['start'], 'start')
    require(type(desc['instructions']) is list and desc['instructions'], 'instruction list')
    instr = []
    for row in desc['instructions']:
        require(type(row) is dict and set(row) == {'op', 'counter', 'target', 'positive'}, 'instruction fields')
        require(type(row['op']) is str and row['op'] in ('INC', 'TEST', 'HALT'), 'instruction op')
        for key in ('counter', 'target', 'positive'):
            natural(row[key], key)
        instr.append(mod.Instruction(**row))
    return mod.Program(desc['dimension'], tuple(instr), desc['start'])


class _DAG:
    def __init__(self):
        self.gates = []
        self.cache = {}
        self.affine_cache = {}
        self.phase = 'shared_routing_forms'

    def op(self, op, a, b):
        if type(a) is int and type(b) is int:
            return {'add': lambda: a+b, 'sub': lambda: a-b, 'mul': lambda: a*b}[op]()
        if op == 'add':
            if a == 0: return b
            if b == 0: return a
        elif op == 'sub':
            if b == 0: return a
            if a == b: return 0
        else:
            if a == 0 or b == 0: return 0
            if a == 1: return b
            if b == 1: return a
        if op in ('add', 'mul') and (type(a).__name__, str(a)) > (type(b).__name__, str(b)):
            a, b = b, a
        key = (op, a, b)
        if key not in self.cache:
            name = 'g' + str(len(self.gates))
            self.cache[key] = name
            self.gates.append({'name': name, 'op': op, 'left': a, 'right': b, 'phase': self.phase})
        return self.cache[key]

    def add(self, a, b): return self.op('add', a, b)
    def sub(self, a, b): return self.op('sub', a, b)
    def mul(self, a, b): return self.op('mul', a, b)

    def sum(self, xs):
        out = 0
        for x in xs:
            out = self.add(out, x)
        return out

    def affine(self, row):
        key = tuple(sorted((name, c) for name, c in row.items() if c))
        if key in self.affine_cache:
            return self.affine_cache[key]
        grouped = {}
        for name, c in key:
            if name:
                grouped.setdefault(c, []).append(name)
        pos, neg = [], []
        for c in sorted(grouped):
            names = grouped[c]
            unit_key = tuple((x, 1) for x in names)
            term = self.affine_cache.get(unit_key)
            if term is None:
                term = self.sum(names)
                self.affine_cache[unit_key] = term
            term = self.mul(abs(c), term)
            (pos if c > 0 else neg).append(term)
        const = row.get('', 0)
        if const > 0: pos.append(const)
        elif const < 0: neg.append(-const)
        out = self.sub(self.sum(pos), self.sum(neg))
        self.affine_cache[key] = out
        return out


def _counts(gates):
    totals = Counter(g['op'] for g in gates)
    phases = {}
    for phase in ('shared_routing_forms', 'all_linear_residuals', 'residual_squares', 'squared_residual_sum', 'routing_cross_sum', 'final_addition'):
        c = Counter(g['op'] for g in gates if g['phase'] == phase)
        phases[phase] = {'multiplications': c['mul'], 'additions_subtractions': c['add'] + c['sub'], 'total': sum(c.values())}
    return {'multiplications': totals['mul'], 'additions_subtractions': totals['add'] + totals['sub'], 'total': len(gates), 'phases': phases}


def build(source, program, horizon, m=5, mode='row_diagonal'):
    mod = _module(source)
    p = _program(mod, program)
    natural(horizon, 'horizon')
    require(type(m) is int and m >= 3 and m % 2 == 1, 'm must be an exact odd integer >=3')
    require(type(mode) is str and mode in MODES, 'unknown routing mode')
    cert = mod.compile_certificate(p, horizon, m)
    dag = _DAG()
    r = len(p.branches); d = p.dimension
    shared = []
    for t in range(horizon):
        bs = [f'b{t}_{branch.tag}' for branch in p.branches]
        aa = [[f'a{t}_{branch.tag}_{j}' for j in range(d)] for branch in p.branches]
        bsum = dag.affine(dict.fromkeys(bs, 1))
        asum = [dag.affine({aa[k][j]: 1 for k in range(r)}) for j in range(d)]
        shared.append({'selector_sum': bsum, 'routed_column_sums': asum, 'selectors': bs, 'routed_by_branch': aa})
    dag.phase = 'all_linear_residuals'
    rows = [dag.affine(row) for row in cert.rows]
    dag.phase = 'residual_squares'
    squares = [dag.mul(x, x) for x in rows]
    dag.phase = 'squared_residual_sum'
    sos = dag.sum(squares)
    dag.phase = 'routing_cross_sum'
    if mode == 'direct':
        cross = dag.sum(dag.mul(a, b) for a, b in cert.cross_terms)
    else:
        cross_t = []
        for s in shared:
            bs, aa, B = s['selectors'], s['routed_by_branch'], s['selector_sum']
            if r <= 1:
                cross_t.append(0)
            elif mode == 'column_diagonal':
                terms = []
                for j in range(d):
                    terms.append(dag.sub(dag.mul(B, s['routed_column_sums'][j]), dag.sum(dag.mul(bs[k], aa[k][j]) for k in range(r))))
                cross_t.append(dag.sum(terms))
            else:
                ars = [dag.affine(dict.fromkeys(row, 1)) for row in aa]
                if mode == 'row_diagonal':
                    total_a = dag.sum(s['routed_column_sums'])
                    cross_t.append(dag.sub(dag.mul(B, total_a), dag.sum(dag.mul(bs[k], ars[k]) for k in range(r))))
                else:
                    cs = []
                    for k in range(r):
                        complement = dag.affine({b: 1 for i, b in enumerate(bs) if i != k}) if r <= 3 else dag.sub(B, bs[k])
                        cs.append(dag.mul(complement, ars[k]))
                    cross_t.append(dag.sum(cs))
        cross = dag.sum(cross_t)
    dag.phase = 'final_addition'
    out = dag.add(sos, cross)
    return {'schema': SCHEMA, 'source_sha256': SOURCE_SHA256, 'program': deepcopy(program), 'horizon': horizon, 'm': m,
            'mode': mode, 'domain': 'natural witnesses and parameters; signed internal registers',
            'signed_identity_scope': 'same polynomial on all integer input tuples; signed zero semantics not claimed',
            'variables': list(cert.variables), 'parameters': list(cert.parameters), 'linear_rows': [dict(x) for x in cert.rows],
            'direct_cross_terms': [list(x) for x in cert.cross_terms], 'shared_forms': shared,
            'residual_registers': rows, 'squared_residual_register': sos, 'cross_register': cross,
            'gates': dag.gates, 'output': out, 'counts': _counts(dag.gates),
            'source_counts': {'witnesses': len(cert.variables), 'parameters': d, 'linear_residuals': len(cert.rows), 'cross_occurrences': len(cert.cross_terms), 'degree': 2}}


def checked(source, packet):
    require(type(packet) is dict, 'packet must be an exact dict')
    try:
        canonical = build(source, packet['program'], packet['horizon'], packet['m'], packet['mode'])
    except KeyError as exc:
        raise ValueError('missing packet descriptor') from exc
    require(exact_equal(packet, canonical), 'packet differs from canonical complete source')
    return canonical


def _eval(packet, assignment):
    env = dict(assignment)
    def value(x): return x if type(x) is int else env[x]
    for gate in packet['gates']:
        a, b = value(gate['left']), value(gate['right'])
        env[gate['name']] = a+b if gate['op'] == 'add' else a-b if gate['op'] == 'sub' else a*b
    return value(packet['output']), env


def evaluate(source, packet, assignment, *, natural=True):
    packet = checked(source, packet)
    require(type(natural) is bool, 'natural must be an exact bool')
    require(type(assignment) is dict and set(assignment) == set(packet['variables'] + packet['parameters']), 'exact assignment interface required')
    require(all(type(v) is int and (not natural or v >= 0) for v in assignment.values()), 'exact domain required')
    return _eval(packet, assignment)[0]


# Independent expanded polynomial arithmetic. It does not use source.expanded().
def _padd(a, b, sign=1):
    out = dict(a)
    for mon, c in b.items(): out[mon] = out.get(mon, 0) + sign*c
    return {m: c for m, c in out.items() if c}


def _pmul(a, b):
    out = {}
    for m, c in a.items():
        for n, d in b.items():
            key = tuple(sorted(m+n)); out[key] = out.get(key, 0) + c*d
    return {m: c for m, c in out.items() if c}


def _expanded(packet):
    env = {x: {(x,): 1} for x in packet['variables'] + packet['parameters']}
    def val(x): return ({(): x} if x else {}) if type(x) is int else env[x]
    for gate in packet['gates']:
        a, b = val(gate['left']), val(gate['right'])
        env[gate['name']] = _pmul(a, b) if gate['op'] == 'mul' else _padd(a, b, 1 if gate['op'] == 'add' else -1)
    return val(packet['output']), env, val


def _poly_digest(poly):
    return hashlib.sha256(json.dumps([[list(m), c] for m, c in sorted(poly.items())], separators=(',', ':')).encode()).hexdigest()


def _desc(d, instructions, start=0):
    return {'dimension': d, 'start': start, 'instructions': [{'op': op, 'counter': counter, 'target': target, 'positive': positive} for op, counter, target, positive in instructions]}


def _fixtures():
    return [
        ('halt', _desc(1, [('HALT', 0, 0, 0)]), [0, 1]),
        ('divergent', _desc(1, [('INC', 0, 0, 0), ('HALT', 0, 0, 0)]), [0, 1, 4]),
        ('countdown', _desc(1, [('TEST', 0, 1, 0), ('HALT', 0, 0, 0)]), [0, 1, 3, 7]),
        ('transfer', _desc(2, [('TEST', 0, 2, 1), ('INC', 1, 0, 0), ('HALT', 0, 0, 0)]), [0, 1, 3, 7]),
        ('five_branches', _desc(3, [('TEST', 0, 3, 1), ('INC', 1, 2, 0), ('TEST', 2, 0, 1), ('HALT', 0, 0, 0)], 1), [0, 1, 4]),
        ('eight_branches', _desc(2, [('TEST', j%2, 4, (j+1)%4) for j in range(4)] + [('HALT', 0, 0, 0)]), [1, 3]),
        ('four_branches_six_counters', _desc(6, [('TEST', 2, 2, 1), ('TEST', 5, 2, 0), ('HALT', 0, 0, 0)]), [1, 3]),
    ]


def run(source):
    require(__debug__, 'run without Python -O')
    mod = _module(source)
    rng = random.Random(20261003)
    checks = Counter()
    def ck(label, condition):
        if not condition: raise AssertionError(label)
        checks[label] += 1
    def reject(fn):
        try: fn()
        except (ValueError, TypeError): checks['guard_rejections'] += 1
        else: raise AssertionError('guard accepted malformed call')
    cases, emitted = [], {}
    for label, desc, horizons in _fixtures():
        p = _program(mod, desc)
        for T in horizons:
            m = 3 if T == 0 else 5
            cert = mod.compile_certificate(p, T, m)
            # Reconstruct source expansion independently from every literal row and cross term.
            expected = {}
            for row in cert.rows:
                rp = {(x,) if x else (): c for x, c in row.items()}
                expected = _padd(expected, _pmul(rp, rp))
            for x, y in cert.cross_terms:
                expected = _padd(expected, {tuple(sorted((x, y))): 1})
            packets = [build(source, desc, T, m, mode) for mode in MODES]
            counts = {}
            for packet in packets:
                poly, penv, val = _expanded(packet)
                ck('complete_symbolic_polynomial_identities', poly == expected)
                ck('exact_degree_two', max(map(len, poly), default=0) == 2)
                for row, ref in zip(cert.rows, packet['residual_registers']):
                    ck('literal_affine_rows', val(ref) == {(x,) if x else (): c for x, c in row.items()})
                ck('source_counts', packet['source_counts'] == {'witnesses': (p.dimension+3)*(T+1)+1+T*((p.dimension+1)*len(p.branches)+sum(i.op=='TEST' for i in p.instructions)), 'parameters': p.dimension, 'linear_residuals': p.dimension+5+T*(5+2*p.dimension+2*sum(i.op=='TEST' for i in p.instructions)), 'cross_occurrences': p.dimension*len(p.branches)*(len(p.branches)-1)*T, 'degree': 2})
                ck('paid_gate_ledger', packet['counts'] == _counts(packet['gates']))
                available = set(packet['variables'] + packet['parameters'])
                for gate in packet['gates']:
                    ck('acyclic_exact_gate', gate['op'] in ('add','sub','mul') and gate['name'] not in available and all(type(x) is int or type(x) is str and x in available for x in (gate['left'], gate['right'])))
                    available.add(gate['name'])
                counts[packet['mode']] = packet['counts']
                for signed in (False, True):
                    for _ in range(4):
                        assignment = {x: rng.randrange(-5 if signed else 0, 8) for x in cert.variables + cert.parameters}
                        ck('complete_tuple_evaluations', evaluate(source, packet, assignment, natural=not signed) == cert.energy(assignment, natural=not signed))
                if (label in ('countdown', 'transfer') and T in (3, 7)) or (label == 'five_branches' and T == 4):
                    emitted[label + '_T' + str(T) + '_' + packet['mode']] = packet
            cases.append({'program': label, 'dimension': p.dimension, 'branches': len(p.branches), 'horizon': T, 'm': m, 'source_counts': packets[0]['source_counts'], 'expanded_polynomial_terms': len(expected), 'polynomial_sha256': _poly_digest(expected), 'counts': counts, 'best_modes': [mode for mode in MODES if counts[mode]['total'] == min(v['total'] for v in counts.values())]})
    # General complete-count differences: shared non-routing source is unchanged.
    for case in cases:
        R, d, T = case['branches'], case['dimension'], case['horizon']
        if R >= 2 and T:
            direct, col, row = (case['counts'][key] for key in ('direct', 'column_diagonal', 'row_diagonal'))
            ck('exact_column_savings_formula', direct['multiplications'] - col['multiplications'] == T*d*(R*R-2*R-1) and direct['additions_subtractions'] - col['additions_subtractions'] == T*d*(R*R-2*R-1))
            ck('exact_row_savings_formula', col['multiplications'] - row['multiplications'] == T*(d-1)*(R+1) and col['additions_subtractions'] == row['additions_subtractions'])
            if R >= 4:
                comp = case['counts']['row_complement']
                ck('exact_large_complement_savings_formula', row['multiplications'] - comp['multiplications'] == T and comp['additions_subtractions'] - row['additions_subtractions'] == T*(R-d))
    # Exact natural accepting fibres are unchanged: fixed source witnesses, mutations, and input binding.
    for label, desc, inputs in [('halt', _fixtures()[0][1], [(0,), (3,)]), ('countdown', _fixtures()[2][1], [(0,), (2,), (6,)]), ('transfer', _fixtures()[3][1], [(0,0), (2,1), (3,0)])]:
        p = _program(mod, desc)
        for initial in inputs:
            T = len(p.trace(initial, 30))-1
            witness = mod.canonical_assignment(p, initial, T)
            for mode in MODES:
                packet = build(source, desc, T, mode=mode)
                ck('canonical_natural_zeros', evaluate(source, packet, witness) == 0)
                for name in witness:
                    bad = dict(witness); bad[name] += 1
                    ck('single_coordinate_false_witnesses', evaluate(source, packet, bad) > 0)
    desc = _fixtures()[4][1]
    packet = build(source, desc, 1)
    assignment = dict.fromkeys(packet['variables'] + packet['parameters'], 1)
    for value in (True, 1.0, -1): reject(lambda value=value: build(source, desc, value))
    for value in (True, 3.0, 2, -3): reject(lambda value=value: build(source, desc, 1, m=value))
    for value in (True, 'unknown', 0): reject(lambda value=value: build(source, desc, 1, mode=value))
    for value in (True, 3.0):
        bad = deepcopy(desc); bad['dimension'] = value
        reject(lambda bad=bad: build(source, bad, 1))
    for path, value in [(('horizon',), True), (('horizon',), 1.0), (('counts','total'), packet['counts']['total']+1), (('source_sha256',), 'x'), (('gates',0,'left'), 1.0), (('linear_rows',0,'q0'), True)]:
        bad = deepcopy(packet); at = bad
        for key in path[:-1]: at = at[key]
        at[path[-1]] = value
        reject(lambda bad=bad: checked(source, bad))
    for value in (True, 1.0, -1):
        bad = dict(assignment); bad[next(iter(bad))] = value
        reject(lambda bad=bad: evaluate(source, packet, bad))
    bad = dict(assignment); bad['extra'] = 0
    reject(lambda: evaluate(source, packet, bad))
    bad = dict(assignment); bad.pop(next(iter(bad)))
    reject(lambda: evaluate(source, packet, bad))
    for value in (0, 1, None): reject(lambda value=value: evaluate(source, packet, assignment, natural=value))
    bad = deepcopy(packet); bad['linear_rows'][0].clear(); bad['program']['instructions'].clear()
    ck('defensive_build', exact_equal(packet, build(source, desc, 1)))
    huge = dict(assignment); huge[next(iter(huge))] = 10**150+1
    ck('huge_integer_evaluation', evaluate(source, packet, huge) == mod.compile_certificate(_program(mod, desc), 1).energy(huge))
    # Source authentication still runs before a warm private module cache is reused.
    with tempfile.TemporaryDirectory(prefix='connected-cross-source-guard-') as tmp:
        copy = Path(tmp)/'substrate.py'; copy.write_bytes(Path(source).read_bytes())
        ck('private_source_replay', exact_equal(build(copy, desc, 1), packet))
        copy.write_bytes(copy.read_bytes()+b'\n# altered source\n')
        reject(lambda: build(copy, desc, 1))
    # A matching timestamp/size .pyc must never replace the pinned source bytes.
    with tempfile.TemporaryDirectory(prefix='connected-cross-bytecode-guard-') as tmp:
        copy = Path(tmp)/'substrate.py'
        source_bytes = Path(source).read_bytes()
        prefix = b'raise RuntimeError("FORGED_BYTECODE_EXECUTED")\n#'
        copy.write_bytes(prefix + b'x'*(len(source_bytes)-len(prefix)))
        stamp = copy.stat().st_mtime_ns
        py_compile.compile(str(copy), doraise=True, invalidation_mode=py_compile.PycInvalidationMode.TIMESTAMP)
        copy.write_bytes(source_bytes); os.utime(copy, ns=(stamp, stamp))
        ck('cold_forged_bytecode_ignored', exact_equal(build(copy, desc, 1), packet))
    # Exhausted symbolic routing census independent of machine instruction coefficients.
    census = []
    for r in range(2, 9):
        for d in range(1, 9):
            instructions = [('INC', j%d, (j+1) % (r+1), 0) for j in range(r)] + [('HALT', 0, 0, 0)]
            desc = _desc(d, instructions)
            entries = {mode: build(source, desc, 1, mode=mode) for mode in MODES}
            reference, _, _ = _expanded(entries['direct'])
            for mode, item in entries.items():
                poly, _, _ = _expanded(item)
                ck('routing_census_complete_identity', poly == reference)
            census.append({'branches': r, 'dimension': d, 'costs': {mode: item['counts'] for mode, item in entries.items()}, 'best_modes': [mode for mode, item in entries.items() if item['counts']['total'] == min(x['counts']['total'] for x in entries.values())]})
    return {'schema': SCHEMA, 'status': 'passed', 'source_sha256': SOURCE_SHA256, 'helper_sha256': digest(__file__), 'counting': 'Every emitted binary +,-,* costs one; multiplication by a nontrivial integer constant is charged. Constants and input wires are free. Exact constant folding, identities with 0/1 and literal structural CSE are applied. Coefficient groups share previously emitted selector/column sums.', 'domain': 'Unchanged natural coordinates, fixed program and external horizon; identical polynomial also on all signed tuples.', 'checks': dict(sorted(checks.items())), 'total_checks': sum(checks.values()), 'cases': cases, 'routing_census': census, 'complete_emitted_packets': emitted}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--expect', type=Path)
    args = parser.parse_args()
    result = run(args.source)
    if args.expect:
        require(exact_equal(result, json.loads(args.expect.read_text())), 'receipt mismatch')
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'status': result['status'], 'total_checks': result['total_checks'], 'cases': len(result['cases']), 'routing_census': len(result['routing_census']), 'emitted_packets': len(result['complete_emitted_packets'])}, sort_keys=True))


if __name__ == '__main__': main()
