#!/usr/bin/env python3
"""Literal shared-square76/96 graph and current2011 whole-port audit.

Standard library only. No project/incoming program is imported or executed.
Default and -O are read-only; --write materializes this new packet only.
"""
import argparse
from collections import Counter
from copy import deepcopy
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / 'research/thirteen-grouped-squares96'
PARENT_SHA = '05710557a8029ebdb378a6ac156f25e79b848eb10e673c01008acb415fc3e39d'
PARENT_AUDIT_SHA = '2b656fd647f284edceb22068748c08020b6a5bab4ef0af0469104f0be8795801'
PARENT_CERT_SHA = '9f224ce9b83e9f2900238131df536e9b0034bb0daf5a65adbabb0c72357ea923'
PARENT_PROOF_SHA = '6f2a4e7376dc05772fd98f7753f61ca9bf9c5081eb218a769da12d85ae7bf895'
PARENT_LEAN_SHA = '1b9aca9cb96c390ab074001c36680567969c6a33b6e556798b8394500d3cd424'
LEAN_SHA = '7f09a4e8448d643e09c5bfb2289f2d7640b1a0a5a2b2600fc53cce07d640eb97'
CHECKS_SHA = '257513f1fd8c9ea4825d9c144c877c7f359b1aa09620e4602e35849a72320126'
ZERO_SET_PROOF_SHA = 'ed2d33cca9c948c5d9ce8c96997caee6b5e4b8305ae2616e19c9eab929c28fe3'
NATIVE = ROOT / 'research/padding-staircase-independent'
PROOF_SHA = '69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8'
CERT_SHA = 'fae49c56a9c57d394335c8a47da395f000a0c25cb8267d1330104eddbbc7850f'
ARRAY_SHA = '43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93'
VARIABLES = ['J','F','alpha','f','i','T','s','w','n','eta','zeta','m','gamma']
PORTS = ['beta','K0','MC','MF']
SYMBOLS = VARIABLES + PORTS
ZERO = (0,) * len(SYMBOLS)

def require(ok, message):
    if not ok:
        raise ValueError(message)


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def pinned(path, digest):
    raw = path.read_bytes()
    require(sha(raw) == digest, 'Pinned input differs: ' + str(path))
    return raw


def add(a, b, sign=1):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + sign*c
        if not out[m]:
            del out[m]
    return out


def mul(a, b):
    out = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            m = tuple(x+y for x,y in zip(ma, mb))
            out[m] = out.get(m, 0) + ca*cb
    return {m:c for m,c in out.items() if c}


def const(n):
    return {ZERO:n} if n else {}


def power(a, n):
    out = const(1)
    for _ in range(n):
        out = mul(out, a)
    return out


def symbol(name):
    m = list(ZERO)
    m[SYMBOLS.index(name)] = 1
    return {tuple(m):1}


def product(factors, coefficient=1):
    out = const(coefficient)
    for a,n in factors:
        out = mul(out, power(a,n))
    return out


def degree(a):
    return max((sum(m[:13]) for m in a), default=-1)


def leading(a):
    d = degree(a)
    return {m:c for m,c in a.items() if sum(m[:13]) == d}


def rows(a):
    return [[list(m),c] for m,c in sorted(a.items())]


def evaluator(graph, cuts=None):
    cache = {s:symbol(s) for s in SYMBOLS} if cuts is None else dict(cuts)
    gates = {r[0]:r for r in graph['source']}
    def get(n):
        if type(n) is int:
            return const(n)
        if n not in cache:
            _,op,l,r = gates[n]
            a,b = get(l),get(r)
            cache[n] = mul(a,b) if op == '*' else add(a,b,1 if op == '+' else -1)
        return cache[n]
    return get


def record(n):
    require(type(n) is int and n>0,'Positive whole integer')
    raw = n.to_bytes((n.bit_length()+7)//8,'big')
    return {'bits':n.bit_length(),'bytes':len(raw),'sha256':sha(raw)}


def dependence_witnesses(graph, values):
    """Exact unequal modular outputs certify genuine polynomial dependence.

    These witnesses are not a test of the zero-set theorem. For unknowns,
    the other thirteen-coordinate inputs are positive and every fixed port
    is the actual whole current integer. For a port, only that port changes.
    """
    fixed = dict(zip(PORTS, (values[n] for n in ('beta','K','MC','MF_source'))))
    modulus = 1000003
    def evaluate(inputs):
        env = {k:v % modulus for k,v in inputs.items()}
        for name,op,l,r in graph['source']:
            a = l if type(l) is int else env[l]
            b = r if type(r) is int else env[r]
            env[name] = (a*b if op == '*' else a+b if op == '+' else a-b) % modulus
        return env['polynomial']
    witnesses = {}
    for leaf in SYMBOLS:
        for base in range(1,10):
            inputs = dict(fixed, **{v:base for v in VARIABLES})
            changed = dict(inputs)
            changed[leaf] += 1
            before, after = evaluate(inputs), evaluate(changed)
            if before != after:
                witnesses[leaf] = {'all_unknowns_before':base,'increment':1,
                                   'before':before,'after':after}
                break
        require(leaf in witnesses, 'Actual polynomial depends on '+leaf)
    return {'modulus':modulus,'whole_port_residues':{k:v%modulus for k,v in fixed.items()},
            'witnesses':witnesses,
            'scope':'Unequal modular values prove dependence, not zero-set equivalence.'}


OLD_ROWS = {
    'scaled_f2':['scaled_f2','*','Delta','f2'],
    'Theta':['Theta','-','scaled_f2','Delta'],
    'normalized_Ns':['normalized_Ns','-','f2','strong_term'],
    'resZ':['resZ','-','normalized_Ns',1],
}
REPLACEMENTS = {
    'scaled_f2':['f2minus1','-','f2',1],
    'Theta':['Theta','*','Delta','f2minus1'],
    'normalized_Ns':['resZ','-','f2minus1','strong_term'],
    'resZ':None,
}


def expected_graph(parent):
    gates = {r[0]:r for r in parent['source']}
    require(all(gates[n] == r for n,r in OLD_ROWS.items()), 'Exact four retired parent rows')
    out = deepcopy(parent)
    out.update(name='thirteen_positive2011_shared_squares76_degree96',
        operations=76, operation_counts={'*':42,'+':18,'-':16}, exact_degree=96,
        arithmetic_proof='../../Lean/DiophantineConsistency/ThirteenSharedSquares96.lean',
        arithmetic_proof_sha256=LEAN_SHA,
        parent_polynomial='../thirteen-grouped-squares96/polynomial.json',
        parent_polynomial_sha256=PARENT_SHA, zero_set_proof='PROOF.md',
        zero_set_proof_sha256=ZERO_SET_PROOF_SHA,
        proof_boundary='Identical polynomial over every commutative ring. Entire positive zero set and current external Lean consistency endpoint inherited; no HA/internal ZFC derivation or minimum claim.')
    out['source'] = []
    for row in parent['source']:
        replacement = REPLACEMENTS.get(row[0],row)
        if replacement is not None:
            out['source'].append(deepcopy(replacement))
    del out['display_scalar_names']['normalized_Ns']
    out['display_scalar_names'].update(f2minus1='h',resZ='z=Z-1')
    return out


def check_graph(graph, parent):
    require(graph == expected_graph(parent), 'Whole expected graph and metadata')
    require(graph['witnesses'] == VARIABLES and graph['fixed_numerals'] == PORTS,
            'Exact13 coordinate and4 port order')
    known, gates = set(SYMBOLS), {}
    for name,op,l,r in graph['source']:
        require(type(name) is str and name not in known and op in ('+','-','*'), 'Legal unique gate')
        require(all(type(x) is int or type(x) is str and x in known for x in (l,r)),
                'Integer leaves and topological order')
        known.add(name); gates[name] = (op,l,r)
    require(len(gates) == 76 and Counter(r[1] for r in graph['source']) == {'*':42,'+':18,'-':16},
            'All76 paid binary operations')
    live = set()
    def visit(x):
        if type(x) is int or x in live:
            return
        live.add(x)
        if x in gates:
            visit(gates[x][1]); visit(gates[x][2])
    visit('polynomial')
    require(live == known, 'Every gate, variable and port is live')
    unchanged = [r for r in parent['source'] if r[0] not in OLD_ROWS]
    new_names = {r[0] for r in REPLACEMENTS.values() if r is not None}
    require(len(unchanged) == 73 and unchanged == [r for r in graph['source'] if r[0] not in new_names],
            'Every73 unchanged parent row and order exact')
    require(all(n in gates for n in graph['display_scalar_names']), 'All displayed aliases refer to live gates')
    return {'operations':dict(sorted(Counter(r[1] for r in graph['source']).items())),
            'live_gates':76,'live_variables':13,'live_ports':4,
            'unchanged_rows':73,'retired_rows':OLD_ROWS,'replacement_rows':REPLACEMENTS}


def check_identity(graph, parent):
    P,D,F,S,V,Y = [symbol(n) for n in VARIABLES[:6]]
    cuts = dict(zip(['product0','Delta','f2','strong_term','V2','y2'],[P,D,F,S,V,Y]))
    h = add(F,const(1),-1)
    U = add(mul(mul(D,h),add(V,Y,-1)),Y)
    Zminus1 = add(h,S,-1)
    expected = add(add(power(add(P,const(1),-1),2),power(add(U,const(1),-1),2)),
                   power(Zminus1,2))
    new = evaluator(graph,cuts)('polynomial')
    old = evaluator(parent,cuts)('polynomial')
    require(new == expected == old, 'Entire actual new and parent graph polynomial identity')
    controls = []
    for mutation in ('shared_minus_two','unshared_aux_coefficient','omitted_strong_one',
                     'missing_square','wrong_residual','wrong_group'):
        bad = deepcopy(graph); gates = {r[0]:r for r in bad['source']}
        if mutation == 'shared_minus_two': gates['f2minus1'][3] = 2
        elif mutation == 'unshared_aux_coefficient': gates['Theta'][3] = 'f2'
        elif mutation == 'omitted_strong_one': gates['resZ'][2] = 'f2'
        elif mutation == 'missing_square': gates['sqU'][3] = 1
        elif mutation == 'wrong_residual': gates['resU'][3] = 2
        else: gates['resPQ'][2] = 'f2'
        require(evaluator(bad,cuts)('polynomial') != expected, 'Algebra rejects '+mutation)
        controls.append(mutation)
    return {'cut_symbols':dict(zip(cuts,VARIABLES[:6])),
            'complete_common_cut_polynomial':rows(expected),
            'identity_witness_maps':True,'algebraic_negative_controls':controls,
            'scope':'Exact polynomial identity in independent shared-gate variables. Every other row is unchanged; the Lean proof establishes uniform actual-formula equality over any commutative ring.'}


def check_degree(graph, parent_cert):
    full = evaluator(graph)
    main = full('N1')
    main_root = add(full('X'),mul(symbol('gamma'),full('H')))
    main_alt = add(add(power(main_root,2),product([(full('a'),1),(full('c'),1),(main_root,1)],2)),
                   mul(full('H'),power(full('c'),2)),-1)
    require(main == main_alt and degree(main) == 18 and len(main) == 323,
            'Entire323-term main norm cancellation')
    leaders = {s:symbol(s) for s in SYMBOLS}
    cancellations = []
    for name,op,l,r in graph['source']:
        a = const(l) if type(l) is int else leaders[l]
        b = const(r) if type(r) is int else leaders[r]
        if op == '*': result = mul(a,b)
        elif degree(a) > degree(b): result = a
        elif degree(b) > degree(a): result = b if op == '+' else mul(const(-1),b)
        else: result = add(a,b,1 if op == '+' else -1)
        if not result:
            cancellations.append(name); result = leading(full(name))
        require(bool(result), 'Nonzero gate leader '+name)
        leaders[name] = result
    require(cancellations == ['N1'], 'All leading cancellations accounted for')
    q0 = mul(symbol('beta'),symbol('J'))
    k0 = add(symbol('eta'),symbol('zeta'))
    C0 = add(add(q0,symbol('F'),-1),symbol('alpha'),-1)
    w,s,f,t,i,gamma = [symbol(n) for n in ('w','s','f','T','i','gamma')]
    factors = {'N0':product([(w,2),(s,4),(k0,2),(q0,14)],-1),
               'N1':product([(gamma,1),(w,2),(s,3),(k0,1),(q0,11)],8),
               'Na':product([(q0,22),(k0,4),(s,6),(w,4),(f,6),(t,4),(C0,2)],-16),
               'resZ':product([(i,2),(w,2),(s,6),(k0,4),(q0,22)],-1)}
    require(all(leaders[n] == v for n,v in factors.items()), 'Every complete factor leader')
    require([degree(v) for v in factors.values()] == [22,18,48,36], 'Exact four factor degrees')
    require([degree(leaders[n]) for n in ('sqPQ','sqU','sqZ')] == [80,96,72],
            'Exact three residual-square degrees')
    expected = product([(q0,44),(k0,8),(s,12),(w,8),(f,12),(t,8),(C0,4)],256)
    require(leaders['polynomial'] == expected and degree(expected) == 96 and len(expected) == 135,
            'Entire135-term degree96 leader')
    chosen = {'J':48,'beta':48,'eta':8,'w':8,'s':12,'f':12,'T':8}
    require(expected.get(tuple(chosen.get(n,0) for n in SYMBOLS)) == 256,
            'Selected nonzero specialized coefficient256beta48')
    all_leaders = {n:{'degree':degree(leaders[n]),'terms':len(leaders[n]),
                      'sha256':sha(encoded(rows(leaders[n]))),
                      'complete_leader':rows(leaders[n])} for n,_,_,_ in graph['source']}
    old = parent_cert['exact_degree']
    for n,entry in all_leaders.items():
        if n != 'f2minus1':
            require(entry == old['all_gate_leaders'][n], 'Entire matching gate leader '+n)
    require(rows(expected) == old['complete_leader'] and old['exact_degree'] == 96,
            'Complete parent and new output leaders equal')
    return {'exact_degree':96,'symbols':SYMBOLS,
            'selected_unknown_monomial':{n:e for n,e in chosen.items() if n in VARIABLES},
            'selected_coefficient':'256*beta^48',
            'complete_main_norm_terms':len(main),'main_norm_sha256':sha(encoded(rows(main))),
            'complete_factor_leaders':{n:rows(v) for n,v in factors.items()},
            'complete_leader':rows(expected),'cancellations':cancellations,
            'matching_parent_gate_leaders':75,'all_gate_leaders':all_leaders}



def check_ports(graph):
    pinned(NATIVE/'PROOF.md',PROOF_SHA)
    cert = json.loads(pinned(NATIVE/'certificate.json',CERT_SHA))
    c = json.loads(pinned(NATIVE/'coefficients.json',ARRAY_SHA))
    require(len(c) == 3297 and all(type(x) is int and x>=0 for x in c),'All3297 actual coefficients')
    require(all(e <= 1005 for e,v in enumerate(c) if v), 'All reflected exponents are natural')
    rp = lambda e: 1 << (47*e)
    G = lambda n: sum(rp(e) for e in range(n))
    beta = rp(2011)-1
    K = rp(18)+rp(1004)+rp(2020)+sum(v*rp(1005-e) for e,v in enumerate(c) if v)
    MC = beta-G(951)-rp(960)*G(26)-rp(1004)
    native = 8*G(917)-4+((1<<45)-4)*rp(1005)+rp(960)*G(9)+rp(987)*G(8)+rp(1004)
    values = {'beta':beta,'K':K,'MC':MC,'MF_source':beta+native}
    records = {n:record(v) for n,v in values.items()}
    require(records == cert['constant_ports'] and 0<MC<beta<beta+native<2*beta,
            'All four current2011 integers and scalar boxes')
    binding = graph['coefficient_binding']
    require((HERE/binding['ordinary_proof']).resolve() == NATIVE/'PROOF.md'
            and (HERE/binding['certificate']).resolve() == NATIVE/'certificate.json',
            'Actual current native source paths')
    for alias,name in {'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}.items():
        entry = binding['ports'][alias]
        raw = gzip.decompress(pinned(HERE/binding['path']/entry['file'],entry['gzip_sha256']))
        require(int.from_bytes(raw,'big') == values[name] and sha(raw) == entry['raw_sha256']
                and len(raw) == entry['raw_bytes'] and values[name].bit_length() == entry['bits'],
                'Complete materialized integer '+alias)
    require(sum(v['bytes'] for v in records.values()) == binding['raw_bytes'] == 47313,'Whole raw port bytes')
    return {'ports':records,'raw_bytes':47313,'source_coefficients_sha256':ARRAY_SHA,
            'selected_actual_leader_coefficient_magnitude':record(256*beta**48),
            'selected_actual_leader_coefficient_sign':1,'MF_shifted_exactly_once':True,
            'actual_polynomial_dependence':dependence_witnesses(graph,values)}


def negative_controls(graph, parent):
    failures = []
    for name in ('missing_square','wrong_residual','wrong_group','old_product_output',
                 'shared_minus_two','unshared_aux_coefficient','omitted_strong_one','wrong_port','rational_leaf','extra_variable','dead_gate','old_squared_carrier'):
        bad = deepcopy(graph); gates = {r[0]:r for r in bad['source']}
        if name == 'missing_square': gates['sqU'][3] = 1
        elif name == 'wrong_residual': gates['resZ'][3] = 2
        elif name == 'wrong_group': gates['resPQ'][2] = 'N0'
        elif name == 'old_product_output': gates['polynomial'][:] = ['polynomial','*','Na','resZ']
        elif name == 'shared_minus_two': gates['f2minus1'][3] = 2
        elif name == 'unshared_aux_coefficient': gates['Theta'][3] = 'f2'
        elif name == 'omitted_strong_one': gates['resZ'][2] = 'f2'
        elif name == 'wrong_port': bad['coefficient_binding']['ports']['MF']['bits'] -= 1
        elif name == 'rational_leaf': gates['four_carrier'][2] = 4.0
        elif name == 'extra_variable': bad['witnesses'].append('unused')
        elif name == 'dead_gate': bad['source'].append(['unused_gate','+','f',1])
        else: gates['LB'][2] = 'V2'
        try:
            check_graph(bad,parent)
        except ValueError as error:
            failures.append({'mutation':name,'rejected_by':str(error)})
        else:
            raise ValueError('Corrupted graph accepted: '+name)
    return failures


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='write this graph, port copies and certificate')
    args = parser.parse_args()
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenGroupedSquares96.lean',PARENT_LEAN_SHA)
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenSharedSquares96.lean',LEAN_SHA)
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenSharedSquares96Checks.lean',CHECKS_SHA)
    pinned(PARENT/'audit.py',PARENT_AUDIT_SHA)
    parent_cert = json.loads(pinned(PARENT/'CERTIFICATE.json',PARENT_CERT_SHA))
    pinned(PARENT/'PROOF.md',PARENT_PROOF_SHA)
    pinned(HERE/'PROOF.md',ZERO_SET_PROOF_SHA)
    parent = json.loads(pinned(PARENT/'polynomial.json',PARENT_SHA))
    graph = expected_graph(parent)
    graph_bytes = encoded(graph)
    if args.write:
        (HERE/'coefficients').mkdir(exist_ok=True)
        for entry in graph['coefficient_binding']['ports'].values():
            raw = pinned(PARENT/'coefficients'/entry['file'],entry['gzip_sha256'])
            (HERE/'coefficients'/entry['file']).write_bytes(raw)
        (HERE/'polynomial.json').write_bytes(graph_bytes)
    else:
        require((HERE/'polynomial.json').read_bytes() == graph_bytes,'Whole deterministic graph bytes')
    receipt = {'schema':'thirteen_shared_squares2011_76_96_v1',
        'audit_sha256':sha(Path(__file__).read_bytes()),
        'parent_graph_sha256':PARENT_SHA,'parent_audit_sha256':PARENT_AUDIT_SHA,
        'parent_certificate_sha256':PARENT_CERT_SHA,'parent_lean_sha256':PARENT_LEAN_SHA,
        'parent_proof_sha256':PARENT_PROOF_SHA,'lean_source_sha256':LEAN_SHA,
        'lean_checks_sha256':CHECKS_SHA,'zero_set_proof_sha256':ZERO_SET_PROOF_SHA,
        'graph_sha256':sha(graph_bytes),'graph':check_graph(graph,parent),
        'whole_cut_identity':check_identity(graph,parent),'exact_degree':check_degree(graph,parent_cert),
        'current_ports':check_ports(graph),'negative_controls':negative_controls(graph,parent),
        'scope':'Exact full graph and parent polynomial identity, complete all-gate leaders, entire current ports. Uniform ring identity and inherited current external endpoint separately Lean-proved; no HA/internal ZFC derivation or global minimum claim.'}
    require(receipt['current_ports'] == parent_cert['current_ports'], 'Complete actual port receipt and dependence witnesses unchanged')
    data = encoded(receipt)
    if args.write:
        (HERE/'CERTIFICATE.json').write_bytes(data)
    else:
        require((HERE/'CERTIFICATE.json').read_bytes() == data,'Deterministic certificate bytes')
    print(json.dumps({'status':'PASS','variables':13,'operations':76,'exact_degree':96,
        'raw_port_bytes':47313,'graph_sha256':sha(graph_bytes),'certificate_sha256':sha(data)},sort_keys=True))


if __name__ == '__main__':
    main()


