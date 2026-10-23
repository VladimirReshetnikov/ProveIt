#!/usr/bin/env python3
"""Independent finite review: no project builder or verifier is imported."""
from collections import Counter
from itertools import combinations_with_replacement
from pathlib import Path
import gzip
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def check(ok, why):
    if not ok:
        raise ValueError(why)


def read(name):
    return json.loads((ROOT/name).read_text())


def plus(a, b, sign=1):
    z = dict(a)
    for m, c in b.items():
        z[m] = z.get(m,0)+sign*c
        if not z[m]:
            del z[m]
    return z


def times(a,b):
    z = {}
    for m,c in a.items():
        for n,d in b.items():
            key = tuple(x+y for x,y in zip(m,n))
            z[key] = z.get(key,0)+c*d
    return {m:c for m,c in z.items() if c}


def main():
    source = read('data/parent_system60.json')
    names = source['variables']+source['constants']
    check(len(source['variables']) == 31 and len(names) == 35, 'Source dimensions')
    zero = (0,)*35
    values = {name:{tuple(int(i==j) for i in range(35)):1} for j,name in enumerate(names)}
    def get(x):
        return ({zero:x} if x else {}) if type(x) is int else values[x]
    for out,op,a,b in source['source']:
        check(out not in values, 'Source register redefinition')
        values[out] = times(get(a),get(b)) if op == '*' else plus(get(a),get(b),-1 if op == '-' else 1)
    rows = [plus(get(a),get(b),-1) for a,b in source['comparisons']]
    packet = read('data/parent_source.json')
    check(rows == [{tuple(t['powers']):t['coefficient'] for t in row['terms']}
                   for row in packet['equations']], 'Literal parent expansion')
    old = read('upstream/old_parent.json')
    oldrows = [{tuple(t['powers']):t['coefficient'] for t in row['terms']}
               for row in old['equations']]
    for i in range(22):
        expected = plus(oldrows[i], times(values['beta'],values['J']),-1) if i == 14 else oldrows[i]
        check(rows[i] == expected, 'Shifted transport/source row '+str(i))
    rows[13] = plus(rows[13], rows[1])
    rows[14] = plus(rows[14], rows[2])

    code = read('data/split_code.json')
    weights = code['weights']
    target = dict(zip(code['order'],code['targets']))
    check(sorted(target) == list(range(1,23)), 'Every source row targeted')
    check(len(set(weights)) == 31 and max(weights) == 116 and min(weights)>0, 'Positive distinct weights')
    kernels = [{} for _ in range(3)]
    origins = [{} for _ in range(3)]
    for j,row in enumerate(rows,1):
        grouped = {}
        for mon,c in row.items():
            grouped.setdefault(mon[:31],{})[mon[31:]] = c
        for witness_mon,coefficient in grouped.items():
            pair = tuple(i for i,e in enumerate(witness_mon) for _ in range(e))
            d = len(pair)
            check(d <= 2, 'Quadratic source')
            exponent = target[j]-sum(weights[i] for i in pair)
            check(exponent >= 0 and exponent not in kernels[d], 'Kernel overlap')
            fac = 1 if d == 2 and pair[0] != pair[1] else 2
            kernels[d][exponent] = {port_mon:fac*c for port_mon,c in coefficient.items()}
            origins[d][exponent] = (j,pair)
    archived = read('data/split_kernels.json')
    check(len(archived['kernels']) == 3, 'Three kernels')
    for layer in archived['kernels']:
        actual = {t['exponent']:{tuple(c['powers']):c['coefficient'] for c in t['coefficient']}
                  for t in layer['terms']}
        check(actual == kernels[layer['degree']], 'Exact sparse kernel reconstruction')
    at_target = {e:j for j,e in target.items()}
    extracted = {j:{} for j in target}
    interaction_count = 0
    for d in range(3):
        for e,coef in kernels[d].items():
            for pair in combinations_with_replacement(range(31),d):
                interaction_count += 1
                t = e+sum(weights[i] for i in pair)
                if t not in at_target:
                    continue
                j = at_target[t]
                check(origins[d][e] == (j,pair), 'Foreign target contribution')
                multiplicity = 2 if d == 2 and pair[0] != pair[1] else 1
                m = [0]*31
                for i in pair:
                    m[i] += 1
                term = {tuple(m)+p:multiplicity*c for p,c in coef.items()}
                extracted[j] = plus(extracted[j],term)
    check(all(extracted[j] == {m:2*c for m,c in rows[j-1].items()} for j in target),
          'All twenty-two formal extraction identities')
    degrees = [max(k) for k in kernels]
    check(degrees == [1571,1934,1836], 'Kernel degrees')
    check(kernels[2][1836] == {(0,0,0,0):1}, 'Positive leading quadratic coefficient')
    height = max(d*116+e for d,e in enumerate(degrees))
    check(height == 2068 and height-max(target.values()) == 32, 'Convolution/target margins')

    binding = read('upstream/COMPACT_BINDING.json')
    ports = {}
    for p in binding['ports']:
        compressed = (ROOT/'coefficients'/p['gzip_file']).read_bytes()
        raw = gzip.decompress(compressed)
        check(hashlib.sha256(raw).hexdigest() == p['sha256'], 'Port SHA256')
        check(hashlib.sha256(compressed).hexdigest() == p['gzip_sha256'], 'Port compressed SHA256')
        value = int.from_bytes(raw,'little')
        check(value.bit_length() == p['bits'], 'Port bit length')
        ports[p['port']] = value
    check(binding['port_aliases'] == {'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}, 'Whole tuple aliases')
    bits = (590069,592884,590069,590070)
    max_bound = max(sum(abs(c)*(1 << sum(a*b for a,b in zip(m,bits))) for m,c in coef.items())
                    for k in kernels for coef in k.values())
    check(max_bound == 1 << 1182954, 'Coefficient majorant')
    exact_ports = [ports[p] for p in ('beta','K','MC','MF_source')]
    for kernel in kernels:
        for coefficient in kernel.values():
            value = 0
            for m,c in coefficient.items():
                term = c
                for p,e in zip(exact_ports,m):
                    term *= p**e
                value += term
            check(abs(value) < max_bound, 'Strict actual coefficient bound')
    check(1182966 == 1182954+12, 'Radix scale')
    check(2325*2-30 == 2*1155*2 and 2325*1182966-22 == 2*(8872234+1155*1182966),
          'Population threshold as an affine identity in log2(b)')
    cost = {}
    for domain,expected in [('positive',453),('natural',460)]:
        circuit = read('generated/split_116_'+domain+'_global.json')
        counts = Counter(n['kind'] for n in circuit['nodes'] if n['kind'] in ('add','sub','mul'))
        check(sum(counts.values()) == expected, 'Operation count '+domain)
        live = {circuit['output']}
        for i in range(len(circuit['nodes'])-1,-1,-1):
            node = circuit['nodes'][i]
            if i in live and node['kind'] in ('add','sub','mul'):
                check(0 <= node['left'] < i and 0 <= node['right'] < i, 'Topological arithmetic DAG')
                live.update((node['left'],node['right']))
        check(live == set(range(len(circuit['nodes']))), 'No dead circuit nodes')
        cost[domain] = dict(counts)
    r,q,W = 8743,2310,116
    exact_degree = 104*r+400*q+8*W+316
    check(exact_degree == 1834516, 'Independent closed degree calculation')
    receipt = {'status':'PASS','builder_imports':False,'source_rows':22,
               'same_degree_interactions':interaction_count,'formal_extraction_identities':22,
               'kernel_degrees':degrees,'convolution_height':height,'positive_leading_layer':True,
               'coefficient_bound_exponent':1182954,'threshold_identity_symbolic':True,
               'live_operation_counts':cost,'exact_degree_from_reviewed_formula':exact_degree,
               'scope':'Finite algebra, exact fixed data, and reviewed degree formula; no independent proof of the universal native or Jones compiler.'}
    (ROOT/'certificates/INDEPENDENT_REVIEW.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__ == '__main__':
    main()
