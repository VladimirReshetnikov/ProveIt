#!/usr/bin/env python3
"""Pointwise rewrites of the two pinned valuation-separated circuits.

Only the inert parent JSON is read.  No inherited builder, proof search,
Lean compiler or external program is called.
"""
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OPS = {'add', 'sub', 'mul'}
PARENTS = {
    'integer12_degree2400': ('prime_separated12_degree2400', 208,
        'c9a715eed7018d09adf93a9a009745dca3cc8989c16ad8133e5a10ab3be97b51'),
    'integer12_degree2912': ('prime_separated12_degree2912', 202,
        '9bcdd541db09c0d8a7a7d83c5c315aa55ba17e0948cfe765ecf62b3e062a7a34'),
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def encoded(data):
    return (json.dumps(data, indent=2)+'\n').encode()


class DAG:
    def __init__(self, nodes=()):
        self.nodes = list(nodes)
        self.memo = {tuple(n): i for i, n in enumerate(self.nodes)}

    def emit(self, node):
        key = tuple(node)
        if key not in self.memo:
            self.memo[key] = len(self.nodes)
            self.nodes.append(list(node))
        return self.memo[key]

    def literal(self, n):
        return self.emit(('integer', n))

    def op(self, tag, a, b):
        left, right = self.nodes[a], self.nodes[b]
        if left[0] == right[0] == 'integer':
            x, y = left[1], right[1]
            return self.literal(x+y if tag == 'add' else x-y if tag == 'sub' else x*y)
        if tag == 'mul':
            if left == ['integer', 0] or right == ['integer', 0]:
                return self.literal(0)
            if left == ['integer', 1]:
                return b
            if right == ['integer', 1]:
                return a
        if tag == 'add':
            if left == ['integer', 0]:
                return b
            if right == ['integer', 0]:
                return a
        if tag == 'sub':
            if right == ['integer', 0]:
                return a
            if a == b:
                return self.literal(0)
        if tag in ('add', 'mul') and a > b:
            a, b = b, a
        return self.emit((tag, a, b))

    def add(self, *args):
        value = args[0]
        for x in args[1:]:
            value = self.op('add', value, x)
        return value

    def sub(self, value, *args):
        for x in args:
            value = self.op('sub', value, x)
        return value

    def mul(self, *args):
        value = args[0]
        for x in args[1:]:
            value = self.op('mul', value, x)
        return value

    def scale(self, n, x):
        return self.mul(self.literal(n), x)

    def square(self, x):
        return self.mul(x, x)


def locate_norm(d, x, a, b, c, e, cn, delta):
    """Match every old norm gate, without importing the old implementation."""
    def square(t):
        A, B, C, F = t
        return (
            d.add(d.square(A), d.mul(c, d.square(B)), d.mul(e, d.square(C)),
                  d.mul(c, e, d.square(F))),
            d.scale(2, d.add(d.mul(A, B), d.mul(e, C, F))),
            d.scale(2, d.add(d.mul(A, C), d.mul(c, B, F))),
            d.scale(2, d.add(d.mul(A, F), d.mul(B, C))))
    t2 = (d.add(d.square(x), c, e), d.scale(-2, x), d.scale(-2, x), d.literal(2))
    q = (d.sub(d.mul(delta, d.sub(t2[0], a, b)), cn),
         d.mul(delta, t2[1]), d.mul(delta, t2[2]), d.mul(delta, t2[3]))
    tn = d.mul(delta, delta, a, b)
    rn = d.mul(delta, cn)
    z64 = d.mul(d.literal(64), tn, rn)
    first_square = square(q)
    first = (d.sub(first_square[0], d.scale(4, d.add(tn, d.mul(rn, d.add(a, b))))),)+first_square[1:]
    second = square(first)
    f = tuple(d.sub(second[i], d.mul(z64, t2[i])) for i in range(4))
    g0 = d.sub(d.add(d.square(f[0]), d.mul(e, f[2], f[2])),
               d.mul(c, d.add(d.square(f[1]), d.mul(e, f[3], f[3]))))
    g1 = d.scale(2, d.sub(d.mul(f[0], f[2]), d.mul(c, f[1], f[3])))
    out = d.sub(d.square(g0), d.mul(e, g1, g1))
    return dict(output=out, t2=t2, q=q, first_square=first_square, f=f)


def transform(parent, name):
    old = DAG(parent['nodes'])
    n = parent['named_registers']
    old_length = len(old.nodes)
    rs = [n['A0'], old.mul(old.literal(9), n['S2'], n['Df']),
          old.mul(old.literal(81), n['S2'], n['Dt']),
          old.mul(old.literal(729), n['S2'], n['Dg'])]
    args = [n['center']]+[rs[i] for i in parent['norm_integer_order']]+[
        n['cn'], n['delta'] if parent['variant'] == 'rational' else old.literal(1)]
    cut = locate_norm(old, *args)
    require(cut['output'] == parent['output'] and len(old.nodes) == old_length,
            'the complete stored norm matches the pinned signature')
    x, a, b, c, e, cn, delta = args
    q, first, f, t2 = cut['q'], cut['first_square'], cut['f'], cut['t2']
    require(q[1] == q[2], 'equal middle coordinates in the first square')
    d = DAG()
    mapping, replacements, cutsets, labels = {}, {}, {}, {}

    def replace(index, cuts, label, body):
        require(index not in replacements and all(v < index for v in cuts),
                'distinct acyclic replacement')
        replacements[index] = body
        cutsets[index] = cuts
        labels[index] = label

    replace(t2[0], [x, c, e], 'shared_outer_radicand_sum',
            lambda: d.add(d.square(visit(x)), d.add(visit(c), visit(e))))
    replace(first[0], [q[0], q[1], q[3], c, e], 'symmetric_first_scalar',
            lambda: d.add(d.square(visit(q[0])),
                          d.mul(d.add(visit(c), visit(e)), d.square(visit(q[1]))),
                          d.mul(visit(c), visit(e), d.square(visit(q[3])))))
    replace(first[1], [q[0], q[1], q[3], e], 'factored_first_u',
            lambda: d.mul(d.scale(2, visit(q[1])),
                          d.add(visit(q[0]), d.mul(visit(e), visit(q[3])))))
    replace(first[2], [q[0], q[1], q[3], c], 'factored_first_v',
            lambda: d.mul(d.scale(2, visit(q[1])),
                          d.add(visit(q[0]), d.mul(visit(c), visit(q[3])))))

    def polarized_norm():
        A, B, C, F = [visit(i) for i in f]
        cc, ee = visit(c), visit(e)
        cd = d.mul(cc, ee)
        h = d.add(d.sub(d.square(A), d.mul(cc, B, B), d.mul(ee, C, C)),
                  d.mul(cd, F, F))
        k = d.sub(d.mul(A, F), d.mul(B, C))
        return d.sub(d.square(h), d.scale(4, d.mul(cd, k, k)))
    replace(parent['output'], list(f)+[c, e], 'polarized_final_biquadratic_norm', polarized_norm)

    one = old.literal(1)
    qnode = old.nodes[n['q']]
    require(qnode[0] == 'add' and one in qnode[1:], 'q has its original +1')
    betaJ = qnode[2] if qnode[1] == one else qnode[1]
    qminusone = old.op('sub', n['q'], one)
    replace(qminusone, [betaJ], 'cancel_radix_minus_one', lambda: visit(betaJ))

    DD, II = n['Delta'], n['I2']
    strong = old.mul(DD, II)
    replace(n['Q'], [DD, II], 'shared_strong_product',
            lambda: d.mul(visit(DD), visit(strong)))
    require(len(old.nodes) == old_length, 'all source helpers are already in the stored circuit')

    def visit(index):
        if index in mapping:
            return mapping[index]
        if index in replacements:
            result = replacements[index]()
        else:
            node = old.nodes[index]
            result = (d.op(node[0], visit(node[1]), visit(node[2]))
                      if node[0] in OPS else d.emit(node))
        mapping[index] = result
        return result

    output = visit(parent['output'])
    live, pending = set(), [output]
    while pending:
        i = pending.pop()
        if i not in live:
            live.add(i)
            if d.nodes[i][0] in OPS:
                pending.extend(d.nodes[i][1:])
    remap = {i: j for j, i in enumerate(sorted(live))}
    nodes = [[node[0], remap[node[1]], remap[node[2]]] if node[0] in OPS else node
             for i, node in enumerate(d.nodes) if i in live]
    mapping = {i: remap[j] for i, j in mapping.items() if j in live}
    counts = dict(sorted(Counter(node[0] for node in nodes if node[0] in OPS).items()))
    child = copy.deepcopy(parent)
    child.update(name=name, nodes=nodes, output=remap[output],
        named_registers={k: mapping[v] for k, v in n.items() if v in mapping},
        operations=sum(counts.values()), operation_counts=counts,
        coefficient_binding='source/inherited/root_fusion/coefficients/BINDING.json',
        semantic_proof='README.md',
        exact_polynomial_relation='Pointwise equal to the pinned parent over every commutative ring.',
        parent_equation='source/equations/'+parent['name']+'.json',
        parent_operations=parent['operations'],
        degree_method='Exact leading monomial of the actual child over formal fixed ports; see DEGREE.json.')
    certificate = {
        'parent_sha256': hashlib.sha256(encoded(parent)).hexdigest(),
        'child_sha256': hashlib.sha256(encoded(child)).hexdigest(),
        'retained_remap': {str(i): j for i, j in sorted(mapping.items())},
        'replacements': [dict(old_node=i, new_node=mapping[i], cuts=cutsets[i], label=labels[i])
                         for i in sorted(replacements)],
    }
    return child, certificate


def build_all():
    outputs, certificates = {}, {}
    for name, (old_name, count, digest) in PARENTS.items():
        path = ROOT/'source/equations'/(old_name+'.json')
        require(hashlib.sha256(path.read_bytes()).hexdigest() == digest, 'pinned complete parent')
        child, certificate = transform(json.loads(path.read_text()), name)
        require(child['operations'] == count, 'actual complete optimized operation total')
        outputs[name] = child
        certificates[name] = certificate
    return outputs, certificates


def main():
    from leading import leading_certificate
    outputs, certificates = build_all()
    (ROOT/'certificates').mkdir(exist_ok=True)
    metrics = []
    for name, packet in outputs.items():
        (ROOT/(name+'.json')).write_bytes(encoded(packet))
        (ROOT/'certificates'/(name+'.json')).write_bytes(encoded(certificates[name]))
        metrics.append({k: packet[k] for k in ['name', 'domain', 'variable_count', 'exact_degree',
                                              'operations', 'operation_counts', 'parent_operations']})
    (ROOT/'METRICS.json').write_bytes(encoded(metrics))
    (ROOT/'DEGREE.json').write_bytes(encoded({name: leading_certificate(packet)
                                            for name, packet in outputs.items()}))
    print(json.dumps(metrics, indent=2))


if __name__ == '__main__':
    main()
