#!/usr/bin/env python3
"""Read-only by default: mixed-carrier72/124 and74/122 DAGs/current2011 ports.

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
PARENT = ROOT / 'research/thirteen-corrected-strong126/polynomial.json'
NORMALIZED = ROOT / 'research/thirteen-variable-normalized-independent/polynomial.json'
NORMALIZED_SHA = '50c7d99e5a1abb19f83c9c3b243995d965ecb3d1d39d509d13fd3b18dcec95d4'
PARENT_SHA = 'e6deeec7f6a298f47e4247c5868e39d7d9caa6431b738ef6b99e822e7183a358'
PARENT_AUDIT_SHA = 'd185e03bff041eb2d581c9f0f49d8d157b0ea275be3d4d45c9c0cb9498892f6d'
PARENT_CERT_SHA = '7d7b6230409776e0fc79a627cc86665f8fd45aca8d94974a6eb4204172e585a5'
CURRENT = ROOT / 'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
CURRENT_SHA = 'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
NATIVE = ROOT / 'research/padding-staircase-independent'
PROOF_SHA = '69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8'
CERT_SHA = 'fae49c56a9c57d394335c8a47da395f000a0c25cb8267d1330104eddbbc7850f'
ARRAY_SHA = '43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93'
LEAN_SHA = 'd64e31b377007ddd05964e29a1976c857d036d6eb919524df58c3bd8c237bd02'
CHECKS_SHA = '3a4301d7b4c72dbf52dc365521397219b929159a23657eaa63d6f9470ba51bdf'
ZERO_SET_PROOF_SHA = '0b4652adbdb5938ba52bf0865799acdc19dcbc13e23948ce16dc33c83cfd8386'
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


def expected_graph(parent, current, corrected=True):
    out = deepcopy(parent)
    count, deg = (74,122) if corrected else (72,124)
    out.update(name=f'thirteen_positive2011_mixed_carrier{count}_degree{deg}',
               operations=count, operation_counts={'*':41,'+':17 if corrected else 16,'-':16 if corrected else 15}, exact_degree=deg,
               proof='README.md', arithmetic_proof='../../Lean/DiophantineConsistency/ThirteenLVCarrier.lean',
               parent_polynomial='../thirteen-corrected-strong126/polynomial.json' if corrected else '../thirteen-variable-normalized-independent/polynomial.json',
               parent_polynomial_sha256=PARENT_SHA if corrected else NORMALIZED_SHA,
               proof_boundary='Positive integer zero sets correspond by inverse polynomial changes of coordinate m. External Lean current2011 consistency endpoint is separate from finite degree checking; no HA/internal ZFC proof or minimum claim.')
    out['arithmetic_proof_sha256'] = LEAN_SHA
    out['zero_set_proof'] = 'PROOF.md'
    out['zero_set_proof_sha256'] = ZERO_SET_PROOF_SHA
    out['coefficient_binding'] = deepcopy(current['coefficient_binding'])
    out['coefficient_binding']['path'] = 'coefficients/'
    out['display_scalar_names']['cTminusR'] = 'L'
    result = []
    for row in parent['source']:
        if row[0] == 'LB':
            require(row == ['LB','*','V2','B'], 'Exact parent carrier row')
            result.extend([['LV','*','cTminusR','V'], ['LB','*','LV','B']])
        else:
            result.append(list(row))
    out['source'] = result
    return out


def check_graph(graph, parent, current, corrected=True):
    count = 74 if corrected else 72
    require(graph == expected_graph(parent,current,corrected), 'Complete expected graph and metadata')
    require(graph['witnesses'] == VARIABLES and graph['fixed_numerals'] == PORTS,
            'Exact coordinate and four-port order')
    known, gates = set(SYMBOLS), {}
    for name,op,l,r in graph['source']:
        require(type(name) is str and name not in known and op in ('+','-','*'), 'Legal unique gate')
        require(all(type(x) is int or type(x) is str and x in known for x in (l,r)),
                'Integer leaves and topological order')
        known.add(name)
        gates[name] = (op,l,r)
    require(len(gates) == count and Counter(r[1] for r in graph['source']) == {'*':41,'+':17 if corrected else 16,'-':16 if corrected else 15},
            'All paid binary gates')
    live = set()
    def visit(x):
        if type(x) is int or x in live:
            return
        live.add(x)
        if x in gates:
            visit(gates[x][1]); visit(gates[x][2])
    visit('polynomial')
    require(live == known, 'All gates,13 coordinates and4 ports remain live')
    return {'operations':dict(sorted(Counter(r[1] for r in graph['source']).items())),
            'live_gates':count,'live_variables':13,'live_ports':4,
            'added_rows':['LV'],'changed_rows':['LB']}


def check_identity(graph, parent):
    # Nine independent common cut values, with no norm or positivity premise.
    P,Q,theta,V,L,b,G,m,Z = [symbol(n) for n in VARIABLES[:9]]
    cuts = {'N0':P,'N1':Q,'Theta':theta,'V':V,'cTminusR':L,
            'qm':b,'B':G,'m':m,'normalized_Ns':Z}
    for actual in (parent,graph):
        deps = {n:{n} for n in SYMBOLS}
        for name,_,left,right in actual['source']:
            deps[name] = (set() if type(left) is int else deps[left]) | (set() if type(right) is int else deps[right])
        require(all('m' not in deps[n] for n in cuts if n != 'm'),
                'Every common cut and correction ingredient is independent of m')
    old, new = evaluator(parent,cuts), evaluator(graph,cuts)
    V2, LV = power(V,2), mul(L,V)
    correction = mul(G,add(V2,LV,-1))
    old_y = add(const(1),mul(const(4),add(mul(b,add(m,mul(V2,G),-1)),G,-1)))
    new_y = add(const(1),mul(const(4),add(mul(b,add(m,mul(LV,G),-1)),G,-1)))
    require(old('y') == old_y and new('y') == new_y, 'Both entire literal carrier formulas')
    require(new('y') == add(old('y'),product([(b,1),(correction,1)],4)),
            'Exact new-minus-old ordinate identity')
    formula = add(product([(P,1),(Q,1),
        (add(mul(theta,add(V2,power(new_y,2),-1)),power(new_y,2)),1),(Z,1)]),const(1),-1)
    require(new('polynomial') == formula, 'Whole mixed-carrier formula independent of gate schedule')
    to_old_cuts = dict(cuts, m=add(m,correction))
    to_new_cuts = dict(cuts, m=add(m,correction,-1))
    require(evaluator(parent,to_old_cuts)('polynomial') == new('polynomial'),
            'Whole old polynomial after m_old=m_new+correction')
    require(evaluator(graph,to_new_cuts)('polynomial') == old('polynomial'),
            'Whole new polynomial after m_new=m_old-correction')
    require(add(add(m,correction),correction,-1) == m
            and add(add(m,correction,-1),correction) == m, 'Inverse coordinate maps')
    difference = product([(P,1),(Q,1),(Z,1),(add(const(1),theta,-1),1),
                          (add(power(new_y,2),power(old_y,2),-1),1)])
    require(add(new('polynomial'),old('polynomial'),-1) == difference and bool(difference),
            'Different same-coordinate polynomials, exact full difference')
    bad = deepcopy(graph)
    next(r for r in bad['source'] if r[0] == 'LV')[2] = 'V'
    require(evaluator(bad,cuts)('polynomial') != new('polynomial'), 'V-squared substitution corruption')
    wrong_sign = evaluator(parent,to_new_cuts)('polynomial')
    require(wrong_sign != new('polynomial'), 'Wrong-sign witness map rejected algebraically')
    return {'cut_symbols':dict(zip(['P','Q','Theta','V','L','b','G','m','Z'],VARIABLES[:9])),
            'correction':'G*(V^2-L*V)', 'to_old':'m+correction','to_new':'m-correction',
            'whole_polynomial_identity_both_maps':True,'maps_inverse':True,'cuts_independent_of_m':True,
            'complete_new_cut_polynomial':rows(formula),'complete_same_coordinate_difference':rows(difference),
            'V_squared_negative':True,'wrong_map_sign_negative':True,
            'positivity_boundary':'Finite ring identities only; positivity on each zero set is proved by ThirteenLVCarrier.lean.'}


def check_degree(graph, corrected=True):
    full = evaluator(graph)
    # Full expansion, not leading-term guessing, resolves both cancellations.
    main = full('N1')
    main_root = add(full('X'),mul(symbol('gamma'),full('H')))
    main_alt = add(add(power(main_root,2),product([(full('a'),1),(full('c'),1),(main_root,1)],2)),
                   mul(full('H'),power(full('c'),2)),-1)
    require(main == main_alt and degree(main) == 18 and len(main) == 323,
            'Entire323-term main norm cancellation')
    coefficient = {}
    if corrected:
        coefficient = full('corrected_Dc2')
        first = mul(add(mul(add(mul(const(2),full('X')),const(1)),power(full('Y'),2)),full('H')),
                    power(full('c'),2))
        second = product([(full('E'),2),(symbol('eta'),1),
                          (add(product([(full('k'),1),(full('Y'),1)],2),symbol('eta')),1)])
        third = product([(full('E'),1),(full('k'),2),(full('Y'),1)])
        alternative = add(add(add(add(first,second),third,-1),power(full('tau'),2)),const(1),-1)
        require(coefficient == alternative and degree(coefficient) == 20 and len(coefficient) == 353,
                'Entire353-term corrected coefficient cancellation')
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
    require(cancellations == (['N1','corrected_Dc2'] if corrected else ['N1']),'All leading cancellations accounted for')
    q0 = mul(symbol('beta'),symbol('J'))
    k0 = add(symbol('eta'),symbol('zeta'))
    C0 = add(add(q0,symbol('F'),-1),symbol('alpha'),-1)
    w,s,f,t,i,gamma = [symbol(n) for n in ('w','s','f','T','i','gamma')]
    if corrected:
        require(leaders['corrected_Dc2'] == product([(w,1),(s,4),(k0,2),(q0,13)],2),
                'Complete new coefficient leader')
    factors = {'N0':product([(w,2),(s,4),(k0,2),(q0,14)],-1),
               'N1':product([(gamma,1),(w,2),(s,3),(k0,1),(q0,11)],8),
               'Na':product([(q0,22),(k0,4),(s,6),(w,4),(f,6),(t,4),(C0,2)],-16),
               'normalized_Ns':product([(i,2),(w,1),(s,6),(k0,4),(q0,21)],-2) if corrected else
                   product([(i,2),(w,2),(s,6),(k0,4),(q0,22)],-1)}
    require(all(leaders[n] == v for n,v in factors.items()), 'Every complete factor leader')
    require([degree(v) for v in factors.values()] == ([22,18,48,34] if corrected else [22,18,48,36]), 'Exact four factor degrees')
    q_power, w_power, coefficient_abs, final_degree = (68,9,256,122) if corrected else (69,10,128,124)
    expected = product([(q0,q_power),(gamma,1),(i,2),(k0,11),(w,w_power),(s,19),(f,6),(t,4),(C0,2)],-coefficient_abs)
    require(leaders['polynomial'] == expected and degree(expected) == final_degree and len(expected) == 72,
            'Entire72-term exact final leader')
    chosen = {'J':q_power+2,'beta':q_power+2,'gamma':1,'i':2,'eta':11,'w':w_power,'s':19,'f':6,'T':4}
    require(expected.get(tuple(chosen.get(n,0) for n in SYMBOLS)) == -coefficient_abs,
            'Selected nonzero specialized beta coefficient')
    return {'exact_degree':final_degree,'symbols':SYMBOLS,
            'selected_coefficient':f'-{coefficient_abs}*beta^{q_power+2}',
            'complete_main_norm_terms':len(main),'main_norm_sha256':sha(encoded(rows(main))),
            'complete_corrected_coefficient_terms':len(coefficient),
            'corrected_coefficient_sha256':sha(encoded(rows(coefficient))),
            'complete_corrected_coefficient_leader':rows(leaders['corrected_Dc2']) if corrected else None,
            'complete_factor_leaders':{n:rows(v) for n,v in factors.items()},
            'complete_leader':rows(expected),'cancellations':cancellations,
            'all_gate_leaders':{n:{'degree':degree(leaders[n]),'terms':len(leaders[n]),
                                  'sha256':sha(encoded(rows(leaders[n])))} for n,_,_,_ in graph['source']}}


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


def check_ports(graph, corrected=True):
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
            'selected_actual_leader_coefficient_magnitude':record(256*beta**70 if corrected else 128*beta**71),
            'selected_actual_leader_coefficient_sign':-1,'MF_shifted_exactly_once':True,
            'actual_polynomial_dependence':dependence_witnesses(graph,values)}


def check_mixed_strong_identity(graph74, graph72):
    stripped = []
    for row in graph74['source']:
        if row[0] not in ('residual_first','corrected_Dc2'):
            stripped.append(['intermediate','*','hi2','Dc2'] if row[0] == 'intermediate' else row)
    require(stripped == graph72['source'], 'Whole72/74 schedules differ only by the strong correction')
    delta,f,b,i,c,P,Q,U = [symbol(n) for n in VARIABLES[:8]]
    cuts = {'Delta':delta,'f2':power(f,2),'hi':mul(b,i),'c2':power(c,2),
            'Dc2':mul(delta,power(c,2)),'N0':P,'N1':Q,'Na':U}
    old, new = evaluator(graph72,cuts), evaluator(graph74,cuts)
    A = product([(b,2),(i,2),(c,2)])
    difference = product([(P,1),(Q,1),(U,1),(A,1),(add(P,const(1),-1),1)])
    require(new('polynomial') == add(old('polynomial'),difference,-1),
            'Whole mixed74=mixed72-P*Q*U*(b*i*c)^2*(P-1)')
    return {'identity':'mixed74=mixed72-P*Q*U*(b*i*c)^2*(P-1)',
            'complete_correction':rows(difference),'cut_symbols':dict(zip(['delta','f','b','i','c','P','Q','U'],VARIABLES[:8]))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='write both graphs, whole port files and deterministic certificate')
    args = parser.parse_args()
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenLVCarrier.lean',LEAN_SHA)
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenLVCarrierChecks.lean',CHECKS_SHA)
    pinned(HERE/'PROOF.md',ZERO_SET_PROOF_SHA)
    pinned(PARENT.parent/'audit.py',PARENT_AUDIT_SHA)
    pinned(PARENT.parent/'CERTIFICATE.json',PARENT_CERT_SHA)
    parent = json.loads(pinned(PARENT,PARENT_SHA))
    normalized = json.loads(pinned(NORMALIZED,NORMALIZED_SHA))
    current = json.loads(pinned(CURRENT,CURRENT_SHA))
    graph74 = expected_graph(parent,current)
    graph72 = expected_graph(normalized,current,False)
    if args.write:
        (HERE/'coefficients').mkdir(exist_ok=True)
        for entry in graph74['coefficient_binding']['ports'].values():
            raw = pinned(CURRENT.parent/'coefficients'/entry['file'],entry['gzip_sha256'])
            (HERE/'coefficients'/entry['file']).write_bytes(raw)
    profiles = {}
    for corrected, graph, prior, filename in [(True,graph74,parent,'polynomial.json'),
                                              (False,graph72,normalized,'polynomial72.json')]:
        graph_bytes = encoded(graph)
        if args.write:
            (HERE/filename).write_bytes(graph_bytes)
        else:
            require((HERE/filename).read_bytes() == graph_bytes,'Whole deterministic graph bytes '+filename)
        validation = check_graph(graph,prior,current,corrected)
        identity = check_identity(graph,prior)
        degrees = check_degree(graph,corrected)
        ports = check_ports(graph,corrected)
        negatives = []
        names = ['missing_c_squared','wrong_output','rational_leaf','extra_variable','wrong_port','old_squared_carrier','missing_LV_row']
        if corrected:
            names.append('wrong_residual')
        for name in names:
            bad = deepcopy(graph)
            gates = {r[0]:r for r in bad['source']}
            if name == 'missing_c_squared': gates['strong_term'][3] = 1
            elif name == 'wrong_residual': gates['residual_first'][1] = '+'
            elif name == 'wrong_output': gates['polynomial'][3] = 'Delta'
            elif name == 'rational_leaf': gates['four_carrier'][2] = 4.0
            elif name == 'extra_variable': bad['witnesses'].append('unused')
            elif name == 'wrong_port': bad['coefficient_binding']['ports']['MF']['bits'] -= 1
            elif name == 'old_squared_carrier': gates['LB'][2] = 'V2'
            else: bad['source'] = [r for r in bad['source'] if r[0] != 'LV']
            try:
                check_graph(bad,prior,current,corrected)
            except ValueError as error:
                negatives.append({'mutation':name,'rejected_by':str(error)})
            else:
                raise ValueError('Corrupted graph accepted: '+name)
        profiles[str(graph['operations'])] = {'graph_sha256':sha(graph_bytes),'graph':validation,
            'whole_cut_identity':identity,'exact_degree':degrees,'current_ports':ports,'negative_controls':negatives}
    receipt = {'schema':'thirteen_mixed_carrier2011_72_124_and74_122_v1',
               'audit_sha256':sha(Path(__file__).read_bytes()),
               'parent_graph_sha256':PARENT_SHA,'parent_audit_sha256':PARENT_AUDIT_SHA,
               'parent_certificate_sha256':PARENT_CERT_SHA,'normalized71_graph_sha256':NORMALIZED_SHA,
               'current65_graph_sha256':CURRENT_SHA,'lean_source_sha256':LEAN_SHA,
               'lean_checks_sha256':CHECKS_SHA,'zero_set_proof_sha256':ZERO_SET_PROOF_SHA,
               'profiles':profiles,'mixed_strong_identity':check_mixed_strong_identity(graph74,graph72),
               'scope':'Exact graphs, full common-cut coordinate identities, all leading cancellations, complete current ports. Positive zero-set maps are separately Lean-proved; this finite audit does not execute Lean or certify HA/internal ZFC derivability.'}
    data = encoded(receipt)
    if args.write:
        (HERE/'CERTIFICATE.json').write_bytes(data)
    else:
        require((HERE/'CERTIFICATE.json').read_bytes() == data,'Deterministic certificate bytes')
    print(json.dumps({'status':'PASS','variables':13,'profiles':[[72,124],[74,122]],
                      'raw_port_bytes':47313,'graph_sha256':{n:p['graph_sha256'] for n,p in profiles.items()},
                      'certificate_sha256':sha(data)},sort_keys=True))


if __name__ == '__main__':
    main()
