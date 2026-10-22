#!/usr/bin/env python3
"""Independent inert-data audit of the fixed-marker circuits.

Reads JSON arrays; does not import or execute the author's generator or any
upstream Python. Source equality proves preservation at the stated interfaces.
Finite evaluations and exact degree diagnostics supplement the handwritten
proof; they do not prove compiler universality or its ZFC interpretation.
"""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json
import argparse


def need(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    def pairs(items):
        out = {}
        for k, v in items:
            need(k not in out, 'duplicate JSON key: '+k)
            out[k] = v
        return out
    return json.loads(path.read_text(), object_pairs_hook=pairs)


def run(rows, values):
    env = dict(values)
    for dst, op, left, right in rows:
        a = env[left] if isinstance(left, str) else left
        b = env[right] if isinstance(right, str) else right
        need(op in ('+', '-', '*'), 'unsupported operator')
        env[dst] = a+b if op == '+' else a-b if op == '-' else a*b
    return env


def closure(rows, outputs):
    defs = {r[0]: r[2:] for r in rows}
    need(len(defs) == len(rows), 'duplicate row')
    found = set()
    todo = list(outputs)
    while todo:
        atom = todo.pop()
        if isinstance(atom, str) and atom not in found:
            found.add(atom)
            todo.extend(defs.get(atom, []))
    return found


def interface(packet, outputs):
    known = set(packet['free'])
    need(len(known) == len(packet['free']), 'duplicate free port')
    need(known == set(packet['witnesses']) | set(packet['fixed_numerals']), 'interface split')
    for row in packet['source']:
        name, op, *args = row
        need(name not in known, 'multiply defined symbol')
        need(all(type(x) is int or isinstance(x,str) and x in known for x in args), 'forward reference')
        known.add(name)
    need(closure(packet['source'], outputs) == known, 'dead/missing declared value')
    ledger = Counter(row[1] for row in packet['source'])
    need(packet['total'] == len(packet['source']), 'total count mismatch')
    need(packet['M'] == ledger['*'], 'multiplication count mismatch')
    need(packet['A'] == ledger['+']+ledger['-'], 'addition count mismatch')


def plus(a,b,p,sign=1):
    out = [0]*max(len(a),len(b))
    for j,x in enumerate(a): out[j] = x
    for j,x in enumerate(b): out[j] = (out[j]+sign*x)%p
    while len(out)>1 and not out[-1]: out.pop()
    return out


def times(a,b,p):
    out = [0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j] = (out[i+j]+x*y)%p
    while len(out)>1 and not out[-1]: out.pop()
    return out


def poly_run(rows, values, p):
    env = {k:list(v) for k,v in values.items()}
    for name,op,lhs,rhs in rows:
        a = env[lhs] if isinstance(lhs,str) else [lhs%p]
        b = env[rhs] if isinstance(rhs,str) else [rhs%p]
        env[name] = times(a,b,p) if op=='*' else plus(a,b,p,1 if op=='+' else -1)
    return env


def audit(upstream, artifacts):
    variants_path = artifacts/'fixed_marker_variants.json'
    systems_path = artifacts/'fixed_marker_systems.json'
    variants = read_json(variants_path)
    systems = read_json(systems_path)
    pins = {str(p):sha256(p.read_bytes()).hexdigest() for p in (variants_path,systems_path)}
    deleted = set('scaled_t odd_index gamma_sum index_product index_rhs difference_multiple '
                  'exponent_partial modulus_multiple exponent_rhs mu2 kappa2 scaled_kappa2 norm_input'.split())
    aliases = {'scaled_t':'twice_cell_bits', 'gamma_sum':'gamma', 'norm_input':'norm_marker'}
    insert = [['marker_error','-','W','marker_constant'],
              ['marker_error_square','*','marker_error','marker_error'],
              ['norm_marker','+','marker_error_square',1]]
    details = {}
    for key, child in variants.items():
        path = upstream/child['parent_file']
        pins[str(path)] = sha256(path.read_bytes()).hexdigest()
        need(pins[str(path)] == child['parent_sha256'], 'upstream hash mismatch')
        parent = read_json(path)['packet']
        expected = []
        for name,op,lhs,rhs in parent['source']:
            if name in deleted: continue
            expected.append([name,op,aliases.get(lhs,lhs) if isinstance(lhs,str) else lhs,
                             aliases.get(rhs,rhs) if isinstance(rhs,str) else rhs])
            if name == 'W': expected += insert
        need(child['source'] == expected, 'literal source reconstruction: '+key)
        need(child['witnesses'] == [s for s in parent['witnesses'] if s not in ('delta','rho','sigma')]+['gamma'], 'witness map')
        need('x' not in child['free'] and 'inner_bits' not in child['free'], 'old input remains')
        interface(child,[child['output']])
        source_hash = sha256(json.dumps(child['source'],separators=(',',':')).encode()).hexdigest()
        # All-value factor decomposition: independently traverse output with
        # the complete factors as formal cut variables. The output operations
        # can only multiply them and subtract the declared constant target.
        cuts = set(child['factors']) | {'A'}
        definitions = {r[0]:r for r in child['source']}
        def product_cut(name):
            if type(name) is int: return ('integer',name)
            if name in cuts: return ('factor',name)
            _,op,lhs,rhs = definitions[name]
            return (op,product_cut(lhs),product_cut(rhs))
        tree = product_cut(child['output'])
        target = ('integer',1) if key in ('fixed_marker76','fixed_marker82') else ('factor','A')
        need(tree[0]=='-' and tree[2]==target,'wrong product target')
        def leaves(node):
            if node[0]=='factor': return [node[1]]
            need(node[0]=='*','nonmultiplicative finalizer')
            return leaves(node[1])+leaves(node[2])
        need(Counter(leaves(tree[1]))==Counter(child['factors']), 'missing/repeated final factor')
        details[key] = {'rows':len(expected),'witnesses':len(child['witnesses']),
                        'M':child['M'],'A':child['A'],'source_sha256':source_hash,
                        'full_literal_reconstruction':'PASS','formal_factor_cut':'PASS'}
    # Systems are exactly dependency-closed subarrays of the reviewed full
    # polynomials with the specified direct equality interfaces.
    expected_comparisons = {
        'fixed_marker74_system':[['norm_first',1],['norm_main',1],['norm_index',1],['norm_transport',1],['norm_aux',1],['norm_strong','A'],['W','marker_constant']],
        'fixed_marker76_system':[['norm_first',1],['norm_main',1],['norm_index',1],['norm_transport',1],['norm_aux',1],['ic22','R16'],['W','marker_constant']],
        'fixed_marker82_system':[['norm_first',1],['norm_main',1],['norm_index',1],['norm_transport',1],['ng_A2','ng_four'],['W','marker_constant']],
    }
    for key, comparisons in expected_comparisons.items():
        packet = systems[key]
        base = variants[key.removesuffix('_system')]
        need(packet['comparisons']==comparisons,'changed comparison contract')
        outputs = [v for pair in comparisons for v in pair]
        live = closure(base['source'],outputs)
        need(packet['source']==[r for r in base['source'] if r[0] in live], 'system is not exact live source')
        interface(packet,outputs)
        details[key] = {'rows':packet['total'],'M':packet['M'],'A':packet['A'],
                        'equations':len(comparisons),'witnesses':len(packet['witnesses']),
                        'exact_live_source':'PASS'}
    # Confirm the proposed two dead ordinary-strong rows are precisely
    # redundant after replacing Ns=1 by ic22=R16.
    ordinary_rows = {r[0]:r for r in variants['fixed_marker76']['source']}
    need(ordinary_rows['strong_difference']==['strong_difference','-','ic22','R16'], 'ordinary strong difference')
    need(ordinary_rows['norm_strong']==['norm_strong','+','strong_difference',1], 'ordinary strong unit')
    # The six-equation eliminated-root system uses the actual local norm.
    root_rows = {r[0]:r for r in variants['fixed_marker82']['source']}
    need(root_rows['ng_K']==['ng_K','-','ng_A2','ng_four'], 'root norm difference')
    need(root_rows['ng_unit']==['ng_unit','+','ng_K',1], 'root norm unit')
    sos = systems['fixed_marker76_sos']
    interface(sos,[sos['output']])
    core = systems['fixed_marker76_system']
    need(sos['source'][:len(core['source'])]==core['source'], 'SOS core modified')
    checks = 0
    for j in range(32):
        values = {name:Fraction((j+5)*(i+7)%31-15,i%5+1) for i,name in enumerate(sos['free'])}
        env = run(sos['source'],values)
        expected = sum((env[a]-(env[b] if isinstance(b,str) else b))**2 for a,b in core['comparisons'])
        need(env[sos['output']]==expected,'SOS residual sum')
        checks += 1
    details['fixed_marker76_sos'] = {'rows':sos['total'],'M':sos['M'],'A':sos['A'],
        'rational_residual_checks':checks,'witnesses':len(sos['witnesses'])}
    # Independent full univariate coefficient executions use different
    # assignments and moduli from the author's checks. They establish degree
    # attainment at these diagnostic slices; uniform bounds are proved in
    # fixed_marker_review.md, not inferred from this test.
    degree_checks = {}
    for key,packet in {**variants,**systems}.items():
        rows = packet['source']
        records = []
        for seed,prime in ((3,1000033),(7,1000037)):
            constants = {'Bm1':30,'Kconstant':11,'twice_cell_bits':12,
                         'MC':6,'MF':18,'marker_constant':2048}
            values = {name:[constants[name]] if name in constants else [i+1,seed+i]
                      for i,name in enumerate(packet['free'])}
            env = poly_run(rows,values,prime)
            if 'output' in packet:
                coefficients = env[packet['output']]
                degree = len(coefficients)-1
                need(degree==packet['exact_degree'],'degree diagnostic: '+key)
                records.append({'modulus':prime,'degree':degree,'leading_coefficient':coefficients[-1]})
            else:
                residuals = [plus(env[a],env[b] if isinstance(b,str) else [b],prime,-1)
                             for a,b in packet['comparisons']]
                degrees = [len(r)-1 for r in residuals]
                need(max(degrees)==packet['max_residual_degree'],'residual degree diagnostic')
                records.append({'modulus':prime,'degrees':degrees})
        degree_checks[key]=records
    return {'status':'PASS','scope':'Independent source/algebra checks plus handwritten mathematical proof; not kernel checked.',
            'pins':pins,'circuits':details,'degree_diagnostics':degree_checks}


if __name__=='__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--upstream',type=Path,required=True)
    parser.add_argument('--artifacts',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    receipt = audit(args.upstream,args.artifacts)
    args.output.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':receipt['status'],'circuits':receipt['circuits']},sort_keys=True))
