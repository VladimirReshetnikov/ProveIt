#!/usr/bin/env python3
"""Independent exact cut/remap certificates for the whole optimized circuits.

All acceptance checks use exceptions under normal and optimized Python.
Polynomial identities use sparse integer coefficients, never modular hashes.
Modular comparisons below are supplementary transcription diagnostics only.
"""
import argparse
import ast
from collections import Counter, defaultdict
import copy
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
OPS = {'add', 'sub', 'mul'}
PORT_HASHES = {
    'beta': '6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea',
    'K0': '18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af',
    'MC': '3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777',
    'MF': '78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722',
    'cone_A': '66463b4c98a7cd43faffe6cc0462f7f4fa65b7fd9bc57cba38789e585d59c615',
    'cone_B': '42be64ea01465eb227e9c993dba41affc2d9244aed8ec8f33d3268bda7c6b401',
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2)+'\n').encode()


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    out = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(out)
    return out


def normalize(nodes, root, cuts):
    """Exact Z-polynomial in free cut atoms, with full new-input rejection."""
    cache, visited = {}, set()
    def walk(i):
        if i in cache:
            return cache[i]
        visited.add(i)
        if i in cuts:
            value = {(cuts[i],): 1}
        else:
            node = nodes[i]
            if node[0] == 'integer':
                value = {(): node[1]} if node[1] else {}
            else:
                need(node[0] in OPS, 'identity encountered an undeclared variable/coefficient')
                left, right = walk(node[1]), walk(node[2])
                out = defaultdict(int)
                if node[0] == 'mul':
                    for u, a in left.items():
                        for v, b in right.items():
                            out[tuple(sorted(u+v))] += a*b
                else:
                    for u, a in left.items():
                        out[u] += a
                    for u, a in right.items():
                        out[u] += (-a if node[0] == 'sub' else a)
                value = {u: a for u, a in out.items() if a}
        cache[i] = value
        return value
    return walk(root), visited


def prove_circuit(parent, child, certificate):
    """An induction certificate, covering every new node and the final output."""
    need(certificate['parent_sha256'] == sha(encoded(parent)), 'certificate parent SHA')
    need(certificate['child_sha256'] == sha(encoded(child)), 'certificate child SHA')
    mapping = {int(i): j for i, j in certificate['retained_remap'].items()}
    entries = certificate['replacements']
    replacements = {r['old_node']: r for r in entries}
    need(len(replacements) == len(entries), 'unique replacement nodes')
    covered, identities = set(), []
    for i, j in sorted(mapping.items()):
        need(0 <= i < len(parent['nodes']) and 0 <= j < len(child['nodes']), 'remap range')
        if i in replacements:
            r = replacements[i]; cuts = r['cuts']
            need(r['new_node'] == j and all(k < i and k in mapping for k in cuts), 'acyclic mapped cuts')
            need(len(set(cuts)) == len(cuts), 'unique old cut atoms')
            need(len({mapping[k] for k in cuts}) == len(cuts), 'unique new cut atoms')
            before, unused = normalize(parent['nodes'], i, {k: k for k in cuts})
            after, reached = normalize(child['nodes'], j, {mapping[k]: k for k in cuts})
            need(before == after, 'exact local integer-polynomial identity: '+r['label'])
            covered.update(reached)
            identities.append(dict(label=r['label'], old_node=i, new_node=j, monomials=len(before)))
        else:
            expected = list(parent['nodes'][i])
            if expected[0] in OPS:
                need(expected[1] in mapping and expected[2] in mapping, 'retained dependency closure')
                expected[1:] = [mapping[expected[1]], mapping[expected[2]]]
                if expected[0] in ('add', 'mul') and expected[1] > expected[2]:
                    expected[1:] = expected[:0:-1]
            need(child['nodes'][j] == expected, 'unchanged leaf/gate after operand remap')
            covered.add(j)
    need(set(replacements).issubset(mapping), 'all replacements reached from output')
    need(covered == set(range(len(child['nodes']))), 'every child node has an exact justification')
    need(parent['output'] in mapping and mapping[parent['output']] == child['output'], 'same output by induction')
    need(parent['variables'] == child['variables'] and parent['domain'] == child['domain'], 'same tuple/domain')
    return {'exact_local_identities': identities, 'unchanged_mapped_nodes': len(mapping)-len(entries),
            'all_child_nodes_justified': len(covered), 'whole_pointwise_identity': True,
            'coefficient_ring': 'Z; valid by the same ring identities over any commutative ring'}


def census(packet):
    degrees = []; counts = Counter()
    for i, node in enumerate(packet['nodes']):
        if node[0] in OPS:
            need(len(node) == 3 and all(type(k) is int and 0 <= k < i for k in node[1:]), 'DAG topology')
            counts[node[0]] += 1
            degrees.append(degrees[node[1]]+degrees[node[2]] if node[0] == 'mul'
                           else max(degrees[node[1]], degrees[node[2]]))
        else:
            need(node[0] in ('variable', 'integer', 'coefficient') and len(node) == 2, 'allowed leaf')
            degrees.append(1 if node[0] == 'variable' else 0)
    live, todo = set(), [packet['output']]
    while todo:
        i = todo.pop()
        if i not in live:
            live.add(i)
            if packet['nodes'][i][0] in OPS:
                todo.extend(packet['nodes'][i][1:])
    need(len(live) == len(packet['nodes']), 'whole circuit live')
    need({n[1] for n in packet['nodes'] if n[0] == 'variable'} == set(packet['variables']), 'all coordinates live')
    need({n[1] for n in packet['nodes'] if n[0] == 'coefficient'} == set(PORT_HASHES), 'same six fixed ports live')
    need(dict(counts) == packet['operation_counts'] and sum(counts.values()) == packet['operations'], 'actual gate count')
    return dict(variables=len(packet['variables']), operations=sum(counts.values()),
                operation_counts=dict(sorted(counts.items())), all_nodes_live=True,
                syntactic_degree_upper_bound=degrees[packet['output']])


def degree_certificates():
    """Exact parent witnesses, transported by the whole polynomial identity."""
    # Replay only the pinned finite degree-certificate function.  No inherited
    # emitter, main routine, array generator, or machine simulation is run.
    helper_path = ROOT/'source/inherited/root_fusion/verification/exact_polynomial.py'
    exact = module('interpolation_parent_exact_ring', helper_path)
    tree = ast.parse((ROOT/'source/build_trace13.py').read_text())
    functions = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'exact_degree']
    need(len(functions) == 1, 'unique pinned trace degree function')
    env = {'require': need}
    exec(compile(ast.Module(body=functions, type_ignores=[]), '<pinned finite degree certificate>', 'exec'), env)
    trace = env['exact_degree'](exact.Ring)
    need(trace['degree'] == 1072 and trace['selected_coefficient'] == '2^976*3^640*beta^480', 'trace exact degree witness')

    def accumulate(factors, coefficient):
        monomial = Counter(); powers = list(coefficient)
        for exponent, variables, constants in factors:
            for v, e in variables.items():
                monomial[v] += exponent*e
            powers = [x+exponent*y for x, y in zip(powers, constants)]
        return dict(sorted(monomial.items())), powers
    a0 = ({'j': 4, 'w': 1, 'v': 1}, (7, 5, 4))
    Y0 = ({'j': 3, 'v': 1}, (4, 3, 3))
    I0 = ({'s': 1, 'r': 1, 'c': 2}, (0, 0, 0))
    product, pc = accumulate([(544, *a0), (128, *Y0), (160, *I0),
        (1, {'c': 64, 's': 32, 'h': 64, 'T': 192}, (0, 0, 0)),
        (1, {'s': 64}, (0, 0, 0))], (704, 16, 0))
    compact, cc = accumulate([(1728, *a0), (1088+256, *I0),
        (1, {'T': 256}, (512, 0, 0))], (448, 0, 0))
    need(sum(product.values()) == 4832 and pc == [5024, 3120, 2560], 'product12 exact leading coefficient')
    need(sum(compact.values()) == 16000 and cc == [13056, 8640, 6912], 'compact12 exact leading coefficient')
    out = {
        'integer12_degree4832': dict(exact_degree=4832, monomial=product, coefficient_powers_2_3_beta=pc,
            highest_radicand_degrees=[70, 190, 212, 250, 302], center_degree=35),
        'integer12_degree16000': dict(exact_degree=16000, monomial=compact, coefficient_powers_2_3_beta=cc,
            highest_radicand_degrees=[70, 410, 570, 786, 1000], center_degree=35),
        'integer13_trace_degree1072': trace,
    }
    return {'method': 'Exact parent leading-form witness plus certified whole-polynomial equality; trace cancellations are not estimated by syntactic degree.',
            'witnesses': out}


def evaluate(packet, variables, ports, prime):
    values = []
    for node in packet['nodes']:
        tag = node[0]
        if tag == 'variable':
            value = variables[node[1]]
        elif tag == 'coefficient':
            value = ports[node[1]]
        elif tag == 'integer':
            value = node[1]
        elif tag == 'add':
            value = values[node[1]]+values[node[2]]
        elif tag == 'sub':
            value = values[node[1]]-values[node[2]]
        else:
            value = values[node[1]]*values[node[2]]
        values.append(value % prime)
    return values[packet['output']]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=ROOT/'CHECKS.json')
    args = ap.parse_args()
    manifest_path = ROOT/'MANIFEST.json'
    if manifest_path.exists():
        for r in json.loads(manifest_path.read_text())['files']:
            raw = (ROOT/r['path']).read_bytes()
            need(len(raw) == r['bytes'] and sha(raw) == r['sha256'], 'candidate manifest item')
    pins = json.loads((ROOT/'SOURCE_PINS.json').read_text())
    need(pins['archive_sha256'] == 'f44b903de17a70316787ff57562a3d8fe3bdec12791e266318cedb49e7125f72', 'arrival pin')
    for r in pins['files']:
        raw = (ROOT/r['path']).read_bytes()
        need(len(raw) == r['bytes'] and sha(raw) == r['sha256'], 'unchanged source member')
    need(len(pins['files']) == 138, 'complete parent source inventory')
    binding_path = ROOT/'source/inherited/root_fusion/coefficients/BINDING.json'
    binding = json.loads(binding_path.read_text()); ports = {}; raw_bytes = 0
    for name, r in binding['payloads'].items():
        raw = gzip.decompress((binding_path.parent/r['file']).read_bytes())
        need(sha(raw) == PORT_HASHES[name] == r['raw_sha256'], 'whole fixed coefficient bytes')
        ports[name] = int.from_bytes(raw, 'little'); raw_bytes += len(raw)
    need(ports['beta'] == 2**1064921-1 and ports['cone_A'] == 2**1113
         and ports['cone_B'] == 2**666104 and raw_bytes == 615883, 'actual whole fixed tuple')
    builder = module('shared_interpolation_builder', ROOT/'build.py')
    rebuilt, certificates = builder.build_all()
    results = {}; negative_controls = []
    rng = random.Random(138107248)
    for name, child in rebuilt.items():
        path = ROOT/(name+'.json'); cert_path = ROOT/'certificates'/(name+'.json')
        need(path.read_bytes() == encoded(child) and cert_path.read_bytes() == encoded(certificates[name]), 'deterministic full rebuild')
        parent_path = ROOT/child['parent_equation']
        parent = json.loads(parent_path.read_text()); cert = json.loads(cert_path.read_text())
        proof = prove_circuit(parent, child, cert)
        counts = census(child)
        need((ROOT/child['coefficient_binding']).resolve() == binding_path.resolve(), 'literal coefficient binding')
        trials = 0
        for prime in (1000000007, 1000000009, 2147483647):
            pports = {k: v % prime for k, v in ports.items()}
            for k in range(32):
                variables = {v: rng.randrange(prime) for v in child['variables']}
                if k < 4:
                    for v in [('c',), ('v',), ('s',), ('r',)][k]:
                        if v in variables:
                            variables[v] = 0
                need(evaluate(parent, variables, pports, prime) == evaluate(child, variables, pports, prime), 'supplementary full-value diagnostic')
                trials += 1
        # Operation/topology-preserving tampering must fail the exact proof.
        bad = copy.deepcopy(child)
        bad['nodes'][bad['output']][0] = 'add'
        bad_cert = copy.deepcopy(cert); bad_cert['child_sha256'] = sha(encoded(bad))
        try:
            prove_circuit(parent, bad, bad_cert)
        except ValueError:
            negative_controls.append(name+': final subtraction changed to addition')
        else:
            raise ValueError('changed output escaped exact proof')
        bad = copy.deepcopy(child)
        beta = next(i for i, n in enumerate(bad['nodes']) if n == ['coefficient', 'beta'])
        bad['nodes'][beta][1] = 'MC'
        bad_cert = copy.deepcopy(cert); bad_cert['child_sha256'] = sha(encoded(bad))
        try:
            prove_circuit(parent, bad, bad_cert)
        except ValueError:
            negative_controls.append(name+': beta leaf changed to MC')
        else:
            raise ValueError('changed fixed binding escaped retained gate proof')
        results[name] = dict(sha256=sha(path.read_bytes()), parent_sha256=sha(parent_path.read_bytes()),
            parent_operations=parent['operations'], saved_operations=parent['operations']-child['operations'],
            structure=counts, pointwise_identity=proof, supplementary_modular_diagnostics=trials)
    degree = degree_certificates()
    need((ROOT/'DEGREE.json').read_bytes() == encoded(degree), 'deterministic exact-degree certificate')
    for name, item in results.items():
        exact_degree = degree['witnesses'][name].get('exact_degree', degree['witnesses'][name].get('degree'))
        need(exact_degree == rebuilt[name]['exact_degree'], 'same certified exact polynomial degree')
        if 'trace' not in name:
            need(item['structure']['syntactic_degree_upper_bound'] == exact_degree, 'twelve-variable degree upper bound')
    metrics = json.loads((ROOT/'METRICS.json').read_text())
    need([(r['name'], r['operations']) for r in metrics] == [(n, c['operations']) for n, c in rebuilt.items()], 'actual metric export')
    receipt = dict(status='PASS', python_optimized=not __debug__, original_source_members=138,
        whole_source34_raw_bytes=raw_bytes, whole_source34_raw_hashes=PORT_HASHES,
        circuits=results, degree_certificate=degree, negative_controls_rejected=negative_controls,
        scope='Exact local ring identities and complete circuit remap prove pointwise parent equality. Parent ordinary calibration remains inherited; no Lean/internal-ZFC claim.')
    args.output.write_bytes(encoded(receipt))
    print(json.dumps({k: receipt[k] for k in ('status', 'python_optimized', 'original_source_members', 'negative_controls_rejected')}, indent=2))


if __name__ == '__main__':
    main()
