#!/usr/bin/env python3
"""Original local graph emission and static metadata only.

Do not execute this file after its author packet is frozen. It never
evaluates an arithmetic source, imports an earlier emitter, reads saved
row arrays, or propagates degrees. Its rows implement the new handwritten
inverse-pair proof at a52-raw-word / six-increment boundary.
"""
from pathlib import Path
import hashlib
import json
import sys


ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs')
BASE = ROOT / 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
STEM = Path('/tmp/positive7_inverse_pair_action_pascal')


def sha(data):
    return hashlib.sha256(data).hexdigest()


class Graph:
    def __init__(self):
        self.source = []
        self.stages = []

    def op(self, name, op, left, right):
        self.source.append([name, op, left, right])
        return name

    def stage(self, label, start):
        rows = self.source[start:]
        self.stages.append({
            'name': label, 'first_zero_based_row': start,
            'end_exclusive': len(self.source), 'rows': len(rows),
            'M': sum(row[1] == '*' for row in rows),
            'A': sum(row[1] in ('+', '-') for row in rows),
        })


def port(slot, coord):
    return f'selected_{slot}_{coord}'


def decode_a(g, slot):
    p = f'a{slot}_'
    z = lambda i: port(slot, i)
    u = g.op(p+'u', '-', z(4), z(7))
    h = g.op(p+'h', '-', u, z(7))
    v2 = g.op(p+'v2', '+', z(2), h)
    v3 = g.op(p+'v3', '+', z(3), h)
    v5 = g.op(p+'v5', '+', z(5), h)
    t6 = g.op(p+'t6', '+', z(6), h)
    v6 = g.op(p+'v6', '+', t6, h)
    return (v2, v3), (v5, v6)


def upper_pair(g, prefix, pos, neg):
    dl = g.op(prefix+'dl', '-', neg[0], pos[0])
    sm = g.op(prefix+'sm', '+', pos[1], neg[1])
    dm = g.op(prefix+'dm', '-', neg[1], pos[1])
    dl2 = g.op(prefix+'dl2', '+', dl, dl)
    aa = g.op(prefix+'A', '+', dl2, sm)
    return aa, dm


def decode_b_or_z(g, slot, include_last):
    p = f'd{slot}_'
    z = lambda i: port(slot, i)
    u = g.op(p+'u', '-', z(4), z(7))
    h = g.op(p+'h', '-', u, z(7))
    v1 = g.op(p+'v1', '-', z(1), z(4))
    v2 = g.op(p+'v2', '+', z(2), h)
    v3 = g.op(p+'v3', '+', z(3), h)
    w2 = g.op(p+'w2', '+', v2, v3)
    t1 = g.op(p+'t1', '+', v1, v2)
    w1 = g.op(p+'w1', '+', t1, w2)
    v5 = g.op(p+'v5', '+', z(5), h)
    if not include_last:
        return (w1, w2), (u, v5)
    t6 = g.op(p+'t6', '+', z(6), h)
    v6 = g.op(p+'v6', '+', t6, h)
    return (w1, w2, v3), (u, v5, v6)


def lower12_pair(g, prefix, pos, neg):
    dx = g.op(prefix+'dx', '-', neg[0], pos[0])
    sx = g.op(prefix+'sx', '+', pos[0], neg[0])
    dy = g.op(prefix+'dy', '-', neg[1], pos[1])
    aa = g.op(prefix+'A', '*', 12, dx)
    bb = g.op(prefix+'B', '*', 144, sx)
    cc = g.op(prefix+'C', '*', 24, dy)
    tt = g.op(prefix+'T', '+', bb, cc)
    return aa, tt


def conjugated_forms(g, prefix, triple, t):
    tx = g.op(prefix+'tx', '*', t, triple[0])
    ll = g.op(prefix+'L', '+', tx, triple[1])
    ly = g.op(prefix+'Ly', '+', ll, triple[1])
    tly = g.op(prefix+'tLy', '*', t, ly)
    mm = g.op(prefix+'M', '+', tly, triple[2])
    return ll, mm


def return_lower_chart(g, prefix, pair, t):
    aa, dd = pair
    ta = g.op(prefix+'tA', '*', t, aa)
    d2 = g.op(prefix+'D2', '+', dd, dd)
    qq = g.op(prefix+'q', '-', ta, d2)
    cc = g.op(prefix+'C', '*', t, qq)
    bb = g.op(prefix+'B', '-', dd, ta)
    return aa, bb, cc


def emit_local():
    g = Graph()
    start = len(g.source)
    ap = decode_a(g, 0)
    am = decode_a(g, 1)
    a_first = upper_pair(g, 'af_', ap[0], am[0])
    a_second = upper_pair(g, 'as_', ap[1], am[1])
    g.stage('a_pair', start)

    start = len(g.source)
    bp = decode_b_or_z(g, 2, False)
    bm = decode_b_or_z(g, 3, False)
    b_first = lower12_pair(g, 'bf_', bp[0], bm[0])
    b_second = lower12_pair(g, 'bs_', bp[1], bm[1])
    g.stage('b_pair_before_shared_U', start)

    z_pairs = []
    for label, pos_slot, neg_slot, t in [('z1', 4, 5, 4), ('z2', 6, 7, 8)]:
        start = len(g.source)
        pos = decode_b_or_z(g, pos_slot, True)
        neg = decode_b_or_z(g, neg_slot, True)
        pos_forms = tuple(conjugated_forms(g, f'{label}p{i}_', pos[i], t) for i in range(2))
        neg_forms = tuple(conjugated_forms(g, f'{label}m{i}_', neg[i], t) for i in range(2))
        pair = tuple(upper_pair(g, f'{label}u{i}_', pos_forms[i], neg_forms[i]) for i in range(2))
        result = tuple(return_lower_chart(g, f'{label}v{i}_', pair[i], t) for i in range(2))
        z_pairs.append(result)
        g.stage(label+'_pair_before_shared_U', start)

    start = len(g.source)
    z1, z2 = z_pairs
    a0 = g.op('joint_A0', '+', z1[0][0], z2[0][0])
    b0_first = g.op('joint_B0_first', '+', b_first[0], z1[0][1])
    b0 = g.op('joint_B0', '+', b0_first, z2[0][1])
    c0_first = g.op('joint_C0_first', '+', b_first[1], z1[0][2])
    c0 = g.op('joint_C0', '+', c0_first, z2[0][2])
    b02 = g.op('joint_B02', '+', b0, b0)
    q0 = g.op('joint_q0', '-', a0, b02)
    g1 = g.op('joint_G1', '+', q0, c0)
    g2 = g.op('joint_G2', '-', b0, c0)
    out_a = g.op('out_a', '+', g1, a_first[0])
    out_b = g.op('out_b', '+', g2, a_first[1])
    out_c = c0
    d_first = g.op('out_d_first', '+', a_second[0], z1[1][0])
    out_d = g.op('out_d', '+', d_first, z2[1][0])
    e_first = g.op('out_e_first', '+', a_second[1], b_second[0])
    e_next = g.op('out_e_next', '+', e_first, z1[1][1])
    out_e = g.op('out_e', '+', e_next, z2[1][1])
    f_first = g.op('out_f_first', '+', b_second[1], z1[1][2])
    out_f = g.op('out_f', '+', f_first, z2[1][2])
    g.stage('shared_U_and_all_coordinate_aggregation', start)
    return g, [out_a, out_b, out_c, out_d, out_e, out_f]


def static_audit(g, inputs, outputs):
    known = set(inputs)
    definitions = {}
    for row in g.source:
        if len(row) != 4:
            raise ValueError('row shape')
        name, op, left, right = row
        if name in known or op not in ('+', '-', '*'):
            raise ValueError('name or operation')
        for operand in (left, right):
            if not isinstance(operand, int) and operand not in known:
                raise ValueError('forward/unknown dependency')
        definitions[name] = row
        known.add(name)
    live = set()
    pending = list(outputs)
    while pending:
        name = pending.pop()
        if isinstance(name, int) or name in live:
            continue
        if name not in known:
            raise ValueError('unknown output dependency')
        live.add(name)
        if name in definitions:
            pending.extend(definitions[name][2:])
    if set(definitions) - live or set(inputs) - live:
        raise ValueError('dead row or raw port')
    mm = sum(row[1] == '*' for row in g.source)
    aa = sum(row[1] in ('+', '-') for row in g.source)
    if (len(inputs), len(outputs), mm, aa, len(g.source)) != (52, 6, 30, 168, 198):
        raise ValueError('unexpected static census')
    expected = [(0,24),(6,26),(12,50),(12,50),(0,18)]
    if [(s['M'],s['A']) for s in g.stages] != expected:
        raise ValueError('stage census mismatch')
    return {'M': mm, 'A': aa, 'total': len(g.source), 'raw_ports': len(inputs),
            'outputs': len(outputs), 'topology': 'PASS', 'all_rows_live': True,
            'all_raw_ports_live': True, 'arithmetic_evaluation': False,
            'degree_propagation': False}


def bind(path, spans):
    data = path.read_bytes()
    lines = data.splitlines(keepends=True)
    return {'path':str(path), 'sha256':sha(data), 'bytes':len(data),
            'line_count':len(lines), 'read_spans':[
                {'first':a,'last':b,'sha256':sha(b''.join(lines[a-1:b]))}
                for a,b in spans]}


def main():
    retained = [(2,3,4,5,6,7),(2,3,4,5,6,7),
                (1,2,3,4,5,7),(1,2,3,4,5,7),
                (1,2,3,4,5,6,7),(1,2,3,4,5,6,7),
                (1,2,3,4,5,6,7),(1,2,3,4,5,6,7)]
    labels = ['a+','a-','b+','b-','z1+','z1-','z2+','z2-']
    ports = [{'name':port(slot,i),'slot':slot,'label':labels[slot],
              'one_based_coordinate':i} for slot in range(8) for i in retained[slot]]
    inputs = [p['name'] for p in ports]
    g, outputs = emit_local()
    audit = static_audit(g, inputs, outputs)
    note = STEM.with_suffix('.md')
    data = {
        'schema':'original-local-inverse-pair-graph/v1',
        'note':bind(note, [(1,len(note.read_bytes().splitlines()))]),
        'emitter':bind(Path(__file__), []),
        'dependencies':[
            bind(Path('/tmp/positive7_paid_sparse_action_pascal.md'),[(1,353)]),
            bind(BASE/'positive7_selected_action_structure_pascal.md',[(1,193)]),
            bind(ROOT/'docs/incoming/README.md',[(426,440)]),
        ],
        'method':{
            'proof':'handwritten identities; no numerical scientific tests',
            'emission':'original definitions from new proof, no earlier row arrays read',
            'audit':'static operation labels, dependencies, consumers and liveness only',
            'supplied_or_frozen_code_execution':False,
            'saved_scientific_array_evaluation':False,
            'repo_or_git_mutation':False,
        },
        'supplied':inputs, 'port_map':ports,
        'supplied_domain':'raw selected words, computed by the outer positive-hat interface; local identities hold over all integers',
        'source':g.source,
        'source_sha256':sha(json.dumps(g.source,separators=(',',':')).encode()),
        'outputs':outputs,
        'output_order':['a','b','c','d','e','f'],
        'stages':g.stages, 'audit':audit,
        'local_gate_constants':sorted({arg for row in g.source for arg in row[2:] if isinstance(arg,int)}),
        'paid_successors':{
            'relator_append':'24r M +24r A; or N_R of each with fixed-pattern pruning',
            'unscaled_action':'(40+24r)M+(189+24r)A',
            'recurrence_fused_action':'(42+24r)M+(189+24r)A',
            'saving_from_old_paired_block':'144M, unchanged A',
        },
        'scope':'Local paired increment only; no new complete wrapper, universal numerical bound or degree claim',
    }
    output = Path(sys.argv[1]) if len(sys.argv)>1 else STEM.with_suffix('.json')
    output.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'output':str(output),'audit':audit,'sha256':sha(output.read_bytes())},sort_keys=True))


if __name__ == '__main__':
    main()
