#!/usr/bin/env python3
"""Read-only by default: exact corrected-strong73/126 DAG and current2011 ports.

No project module or incoming script is imported or executed. Sparse polynomial
arithmetic uses seventeen independent symbols; the last four have degree zero.
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
PARENT = ROOT / 'research/thirteen-variable-normalized-independent/polynomial.json'
PARENT_SHA = '50c7d99e5a1abb19f83c9c3b243995d965ecb3d1d39d509d13fd3b18dcec95d4'
CURRENT = ROOT / 'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
CURRENT_SHA = 'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
NATIVE = ROOT / 'research/padding-staircase-independent'
PROOF_SHA = '69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8'
CERT_SHA = 'fae49c56a9c57d394335c8a47da395f000a0c25cb8267d1330104eddbbc7850f'
ARRAY_SHA = '43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93'
LEAN_SHA = '57729066535acf1909d30ea5de0b4b78e1ac6f1ae11a126e1c2c4526cc546efe'
CHECKS_SHA = '481f520df1e3ff05efc7869e9c118596e3b9967cac097527c1a7de77ddfe109f'
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


def expected_graph(parent, current):
    out = deepcopy(parent)
    out.update(name='thirteen_positive2011_corrected_strong73_degree126',
               operations=73, operation_counts={'*':40,'+':17,'-':16}, exact_degree=126,
               proof='README.md', arithmetic_proof='../../Lean/DiophantineConsistency/ThirteenCorrectedStrong.lean',
               parent_polynomial='../thirteen-variable-normalized-independent/polynomial.json',
               parent_polynomial_sha256=PARENT_SHA,
               proof_boundary='Same strictly positive integer zero set at identical coordinates; first factor is proved one separately from either zero. External Lean current2011 consistency endpoint; no internal ZFC proof or minimum claim.')
    out['arithmetic_proof_sha256'] = LEAN_SHA
    out['coefficient_binding'] = deepcopy(current['coefficient_binding'])
    out['coefficient_binding']['path'] = '../../candidates/one-page-padding-staircase-carrier65-2011/coefficients/'
    result = []
    for row in parent['source']:
        if row[0] == 'intermediate':
            result.extend([['residual_first','-','N0',1],
                           ['corrected_Dc2','+','Dc2','residual_first'],
                           ['intermediate','*','hi2','corrected_Dc2']])
        else:
            result.append(list(row))
    out['source'] = result
    return out


def check_graph(graph, parent, current):
    require(graph == expected_graph(parent,current), 'Complete expected graph and metadata')
    require(graph['witnesses'] == VARIABLES and graph['fixed_numerals'] == PORTS,
            'Exact coordinate and four-port order')
    known, gates = set(SYMBOLS), {}
    for name,op,l,r in graph['source']:
        require(type(name) is str and name not in known and op in ('+','-','*'), 'Legal unique gate')
        require(all(type(x) is int or type(x) is str and x in known for x in (l,r)),
                'Integer leaves and topological order')
        known.add(name)
        gates[name] = (op,l,r)
    require(len(gates) == 73 and Counter(r[1] for r in graph['source']) == {'*':40,'+':17,'-':16},
            'All73 paid binary gates')
    live = set()
    def visit(x):
        if type(x) is int or x in live:
            return
        live.add(x)
        if x in gates:
            visit(gates[x][1]); visit(gates[x][2])
    visit('polynomial')
    require(live == known, 'All73 gates,13 coordinates and4 ports remain live')
    return {'operations':dict(sorted(Counter(r[1] for r in graph['source']).items())),
            'live_gates':73,'live_variables':13,'live_ports':4,
            'added_rows':['residual_first','corrected_Dc2'],'changed_rows':['intermediate']}


def check_identity(graph, parent):
    delta,f,b,i,c,P,Q,U = [symbol(n) for n in VARIABLES[:8]]
    cuts = {'Delta':delta,'f2':power(f,2),'hi':mul(b,i),'c2':power(c,2),
            'Dc2':mul(delta,power(c,2)),'N0':P,'N1':Q,'Na':U}
    old, new = evaluator(parent,cuts), evaluator(graph,cuts)
    A = product([(b,2),(i,2),(c,2)])
    correction = product([(P,1),(Q,1),(U,1),(A,1),(add(P,const(1),-1),1)])
    require(new('polynomial') == add(old('polynomial'),correction,-1),
            'Whole literal DAG correction identity over independent common cuts')
    corrected = add(old('normalized_Ns'),mul(A,add(P,const(1),-1)),-1)
    require(new('normalized_Ns') == corrected, 'Exact corrected strong factor')
    bad = deepcopy(graph)
    next(r for r in bad['source'] if r[0] == 'residual_first')[1] = '+'
    require(evaluator(bad,cuts)('polynomial') != new('polynomial'), 'P+1 corruption rejected algebraically')
    return {'identity':'p_corrected=p71-P*Q*U*(b*i*c)^2*(P-1)',
            'cut_symbols':dict(zip(['delta','f','b','i','c','P','Q','U'],VARIABLES[:8])),
            'complete_new_cut_polynomial':rows(new('polynomial')),
            'complete_difference':rows(correction),'wrong_sign_negative':True}


def check_degree(graph):
    full = evaluator(graph)
    # Full expansion, not leading-term guessing, resolves both cancellations.
    main = full('N1')
    main_root = add(full('X'),mul(symbol('gamma'),full('H')))
    main_alt = add(add(power(main_root,2),product([(full('a'),1),(full('c'),1),(main_root,1)],2)),
                   mul(full('H'),power(full('c'),2)),-1)
    require(main == main_alt and degree(main) == 18,'Entire main norm cancellation')
    coefficient = full('corrected_Dc2')
    first = mul(add(mul(add(mul(const(2),full('X')),const(1)),power(full('Y'),2)),full('H')),
                power(full('c'),2))
    second = product([(full('E'),2),(symbol('eta'),1),
                      (add(product([(full('k'),1),(full('Y'),1)],2),symbol('eta')),1)])
    third = product([(full('E'),1),(full('k'),2),(full('Y'),1)])
    alternative = add(add(add(add(first,second),third,-1),power(full('tau'),2)),const(1),-1)
    require(coefficient == alternative and degree(coefficient) == 20,'Entire corrected coefficient cancellation')
    leaders = {s:symbol(s) for s in SYMBOLS}
    cancellations = []
    for name,op,l,r in graph['source']:
        a = const(l) if type(l) is int else leaders[l]
        b = const(r) if type(r) is int else leaders[r]
        if op == '*':
            result = mul(a,b)
        elif degree(a) > degree(b):
            result = a
        elif degree(b) > degree(a):
            result = b if op == '+' else mul(const(-1),b)
        else:
            result = add(a,b,1 if op == '+' else -1)
        if not result:
            cancellations.append(name)
            result = leading(full(name))
        require(bool(result), 'Nonzero gate leader '+name)
        leaders[name] = result
    require(cancellations == ['N1','corrected_Dc2'],'All leading cancellations accounted for')
    q0 = mul(symbol('beta'),symbol('J'))
    k0 = add(symbol('eta'),symbol('zeta'))
    C0 = add(add(q0,symbol('F'),-1),symbol('alpha'),-1)
    w,s,f,t,i,gamma = [symbol(n) for n in ('w','s','f','T','i','gamma')]
    require(leaders['corrected_Dc2'] == product([(w,1),(s,4),(k0,2),(q0,13)],2),
            'Complete new coefficient leader')
    factors = {'N0':product([(w,2),(s,4),(k0,2),(q0,14)],-1),
               'N1':product([(gamma,1),(w,2),(s,3),(k0,1),(q0,11)],8),
               'Na':product([(q0,22),(k0,4),(s,6),(w,4),(f,10),(t,4),(C0,2)],-16),
               'normalized_Ns':product([(i,2),(w,1),(s,6),(k0,4),(q0,21)],-2)}
    require(all(leaders[n] == v for n,v in factors.items()), 'Every complete factor leader')
    require([degree(v) for v in factors.values()] == [22,18,52,34], 'Exact four factor degrees')
    expected = product([(q0,68),(gamma,1),(i,2),(k0,11),(w,9),(s,19),(f,10),(t,4),(C0,2)],-256)
    require(leaders['polynomial'] == expected and degree(expected) == 126,'Entire degree126 leader')
    chosen = {'J':70,'beta':70,'gamma':1,'i':2,'eta':11,'w':9,'s':19,'f':10,'T':4}
    require(expected.get(tuple(chosen.get(n,0) for n in SYMBOLS)) == -256,
            'Selected nonzero coefficient -256*beta^70')
    return {'exact_degree':126,'symbols':SYMBOLS,'selected_coefficient':'-256*beta^70',
            'complete_main_norm_terms':len(main),'main_norm_sha256':sha(encoded(rows(main))),
            'complete_corrected_coefficient_terms':len(coefficient),
            'corrected_coefficient_sha256':sha(encoded(rows(coefficient))),
            'complete_corrected_coefficient_leader':rows(leaders['corrected_Dc2']),
            'complete_factor_leaders':{n:rows(v) for n,v in factors.items()},
            'complete_leader':rows(expected),'cancellations':cancellations,
            'all_gate_leaders':{n:{'degree':degree(leaders[n]),'terms':len(leaders[n]),
                                  'sha256':sha(encoded(rows(leaders[n])))} for n,_,_,_ in graph['source']}}


def record(n):
    require(type(n) is int and n>0,'Positive whole integer')
    raw = n.to_bytes((n.bit_length()+7)//8,'big')
    return {'bits':n.bit_length(),'bytes':len(raw),'sha256':sha(raw)}


def check_ports(graph):
    pinned(NATIVE/'PROOF.md',PROOF_SHA)
    cert = json.loads(pinned(NATIVE/'certificate.json',CERT_SHA))
    c = json.loads(pinned(NATIVE/'coefficients.json',ARRAY_SHA))
    require(len(c) == 3297 and all(type(x) is int and x>=0 for x in c),'All3297 actual coefficients')
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
            'selected_actual_leader_coefficient_magnitude':record(256*beta**70),
            'selected_actual_leader_coefficient_sign':-1,'MF_shifted_exactly_once':True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='write graph and deterministic certificate')
    args = parser.parse_args()
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenCorrectedStrong.lean',LEAN_SHA)
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenCorrectedStrongChecks.lean',CHECKS_SHA)
    parent = json.loads(pinned(PARENT,PARENT_SHA))
    current = json.loads(pinned(CURRENT,CURRENT_SHA))
    graph = expected_graph(parent,current)
    graph_bytes = encoded(graph)
    if args.write:
        (HERE/'polynomial.json').write_bytes(graph_bytes)
    else:
        require((HERE/'polynomial.json').read_bytes() == graph_bytes,'Whole deterministic graph bytes')
    validation = check_graph(graph,parent,current)
    identity = check_identity(graph,parent)
    degrees = check_degree(graph)
    ports = check_ports(graph)
    negatives = []
    for name in ('missing_c_squared','wrong_residual','wrong_output','rational_leaf','extra_variable','wrong_port'):
        bad = deepcopy(graph)
        gates = {r[0]:r for r in bad['source']}
        if name == 'missing_c_squared': gates['strong_term'][3] = 1
        elif name == 'wrong_residual': gates['residual_first'][1] = '+'
        elif name == 'wrong_output': gates['polynomial'][3] = 'Delta'
        elif name == 'rational_leaf': gates['four_carrier'][2] = 4.0
        elif name == 'extra_variable': bad['witnesses'].append('unused')
        else: bad['coefficient_binding']['ports']['MF']['bits'] -= 1
        try:
            check_graph(bad,parent,current)
        except ValueError as error:
            negatives.append({'mutation':name,'rejected_by':str(error)})
        else:
            raise ValueError('Corrupted graph accepted: '+name)
    receipt = {'schema':'thirteen_corrected_strong2011_73_126_v1',
               'audit_sha256':sha(Path(__file__).read_bytes()),'graph_sha256':sha(graph_bytes),
               'parent_graph_sha256':PARENT_SHA,'current65_graph_sha256':CURRENT_SHA,
               'lean_source_sha256':LEAN_SHA,'lean_checks_sha256':CHECKS_SHA,
               'graph':validation,'whole_cut_identity':identity,'exact_degree':degrees,
               'current_ports':ports,'negative_controls':negatives,
               'scope':'Exact graph, all leading cancellations, complete current ports. Positive zero-set equivalence is separately Lean-proved; this arithmetic audit does not execute Lean or certify an internal ZFC derivation.'}
    data = encoded(receipt)
    if args.write:
        (HERE/'CERTIFICATE.json').write_bytes(data)
    else:
        require((HERE/'CERTIFICATE.json').read_bytes() == data,'Deterministic certificate bytes')
    print(json.dumps({'status':'PASS','variables':13,'operations':73,'degree':126,
                      'raw_port_bytes':47313,'graph_sha256':sha(graph_bytes),
                      'certificate_sha256':sha(data)},sort_keys=True))


if __name__ == '__main__':
    main()
