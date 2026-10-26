#!/usr/bin/env python3
"""Complete CURRENT2011 fourteen-variable nonzero-sphere71/80 and72/68 audit.

Only newly authored standard-library code executes. Existing code is inert data.
Default and -O compare deterministic artifacts; --write materializes this packet.
"""
import argparse
from collections import Counter
from copy import deepcopy
import gzip
import hashlib
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT/'candidates/one-page-padding-staircase-carrier65-2011'
PARENT_SHA = 'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
PARENT_LEAN_SHA = 'be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154'
SCALED_LEAN_SHA = '2e222efd3b40626e6734fe30e5b7239fb7a7abd5fd9c14bee8e4a238c237c620'
LEAN_SHA = 'f2fb2bfc613e152e9b62d690d1564b41735f34dd2f7ec71c1a5980212b4ed51a'
CHECKS_SHA = 'a4eb07814e8c771e3f6f6f34d6720952a839adc7f7ada7629ccb77060928c526'
GENERIC_SHA = 'c68431d9b220e432550bdba7e8dcef6dd3a7e0323427ae5acdcba006ea69f53a'
GENERIC_CHECKS_SHA = 'ec924b1e5aaf3855811828a0d3f4b3c5c7aecb749564a58d7c4bc40ac51d67d0'
ZERO_SET_PROOF_SHA = 'efade416bb7157651be664255745881982d60da1c613051454725694538d2437'
NATIVE = ROOT/'research/padding-staircase-independent'
PROOF_SHA = '69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8'
CERT_SHA = 'fae49c56a9c57d394335c8a47da395f000a0c25cb8267d1330104eddbbc7850f'
ARRAY_SHA = '43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93'
VARIABLES = ['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma']
PORTS = ['beta','K0','MC','MF']
SYMBOLS = VARIABLES+PORTS
ZERO = (0,)*len(SYMBOLS)

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
    return max((sum(m[:len(VARIABLES)]) for m in a), default=-1)


def leading(a):
    d = degree(a)
    return {m:c for m,c in a.items() if sum(m[:len(VARIABLES)]) == d}


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
    the other fourteen-coordinate inputs are positive and every fixed port
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


COMMON = [
    ['i2','*','i','i'], ['i2Dc2','*','i2','Dc2'],
    ['strong_term','*','i2Dc2','c2'], ['Z','-','f2','strong_term'],
    ['V2','*','V','V'], ['y2','*','y','y'], ['square_gap','-','V2','y2'],
    ['f2minus1','-','f2',1], ['Theta','*','Delta','f2minus1'],
    ['auxiliary','*','Theta','square_gap'], ['U','+','auxiliary','y2']]
TAILS = {
    71:[['PQ','*','N0','N1'], ['UW','*','U','Nt'], ['rUW','-','UW',1],
        ['PQ2','*','PQ','PQ'], ['rUW2','*','rUW','rUW'], ['Z2','*','Z','Z'],
        ['sum1','+','PQ2','rUW2'], ['sum2','+','sum1','Z2'],
        ['polynomial','-','sum2',2]],
    72:[['QW','*','N1','Nt'], ['rQW','-','QW',1],
        ['P2','*','N0','N0'], ['U2','*','U','U'], ['Z2','*','Z','Z'],
        ['rQW2','*','rQW','rQW'], ['sum1','+','P2','U2'],
        ['sum2','+','sum1','Z2'], ['sum3','+','sum2','rQW2'],
        ['polynomial','-','sum3',3]]}
COUNTS = {71:{'*':39,'+':18,'-':14},72:{'*':39,'+':19,'-':14}}
DEGREES = {71:80,72:68}


def expected_graph(parent, profile):
    require(profile in TAILS, 'Known complete profile')
    require(len(parent['source']) == 65 and parent['source'][50] == ['V','-','f2inner','c'],
            'Complete actual65 parent prefix boundary')
    out = deepcopy(parent)
    out.update(name=f'fourteen_current2011_nonzero_sphere{profile}_degree{DEGREES[profile]}',
        operations=profile,operation_counts=COUNTS[profile],exact_degree=DEGREES[profile],
        arithmetic_proof='../../Lean/DiophantineConsistency/CarrierNonzeroSpheres.lean',
        arithmetic_proof_sha256=LEAN_SHA,proof='PROOF.md',zero_set_proof_sha256=ZERO_SET_PROOF_SHA,
        parent_polynomial='../../candidates/one-page-padding-staircase-carrier65-2011/polynomial.json',
        parent_polynomial_sha256=PARENT_SHA,
        proof_boundary='Same entire fourteen-positive-coordinate zero set as actual2011 Carrier65, by identity maps; external ConZFC endpoint, no internal HA/ZFC proof or global minimum.')
    out['source'] = deepcopy(parent['source'][:51]+COMMON+TAILS[profile])
    out['display_scalar_names'] = {'qm':'b','N0':'P','N1':'Q','U':'U','Nt':'W',
                                  'Z':'Z','main_root':'D','MC':'mu','MF':'omega'}
    return out


def check_graph(graph, parent, profile):
    require(graph == expected_graph(parent,profile), 'Complete expected graph and metadata')
    require(graph['witnesses'] == VARIABLES and graph['fixed_numerals'] == PORTS,
            'All14 coordinates and four ports in exact order')
    known,gates = set(SYMBOLS),{}
    for name,op,l,r in graph['source']:
        require(type(name) is str and name not in known and op in ('+','-','*'),'Unique legal gate')
        require(all(type(x) is int or type(x) is str and x in known for x in (l,r)),
                'Integer leaves and topological dependencies')
        known.add(name);gates[name] = (op,l,r)
    require(len(gates) == profile and Counter(r[1] for r in graph['source']) == COUNTS[profile],
            'All paid binary operations')
    live = set()
    def visit(x):
        if type(x) is int or x in live:
            return
        live.add(x)
        if x in gates:
            visit(gates[x][1]);visit(gates[x][2])
    visit('polynomial')
    require(live == known,'Every producer, coordinate and fixed port is live')
    require(graph['source'][:51] == parent['source'][:51], 'All51 unchanged parent rows')
    require(Counter(r[1] for r in graph['source'][:62]) == {'*':34,'+':16,'-':12},
            'Exact paid common62-row prefix')
    require(all(n in known for n in graph['display_scalar_names']), 'Live aliases')
    return {'operations':COUNTS[profile],'live_gates':profile,'live_variables':14,'live_ports':4,
            'unchanged_parent_prefix':51,'common_prefix_count':62,
            'retired_parent_tail':parent['source'][51:],'replacement_common_rows':COMMON,
            'new_tail':TAILS[profile]}


def formulas():
    P,Q,W,D,F,S,V,Y = [symbol(n) for n in VARIABLES[:8]]
    U = add(mul(mul(D,add(F,const(1),-1)),add(V,Y,-1)),Y)
    Uold = add(mul(mul(D,S),add(V,Y,-1)),Y)
    Z = add(F,S,-1)
    PQ,UW,QW = mul(P,Q),mul(U,W),mul(Q,W)
    a = add(add(add(power(PQ,2),power(add(UW,const(1),-1),2)),power(Z,2)),const(2),-1)
    b = add(add(add(add(power(P,2),power(U,2)),power(Z,2)),
                power(add(QW,const(1),-1),2)),const(3),-1)
    old = mul(D,add(product([(P,1),(Q,1),(Uold,1),(W,1),(Z,1)]),const(1),-1))
    return (P,Q,W,D,F,S,V,Y),U,Uold,Z,{71:a,72:b},old


def check_formulas(graphs,parent):
    symbols,U,Uold,Z,expected,old_expected = formulas()
    P,Q,W,D,F,S,V,Y = symbols
    cuts = dict(zip(['N0','N1','Nt','Delta','f2','strong_term','V2','y2'],symbols))
    old_cuts = {k:v for k,v in cuts.items() if k != 'strong_term'}
    old_cuts['normalized_S2'] = mul(D,S)
    old = evaluator(parent,old_cuts)('polynomial')
    require(old == old_expected, 'Complete actual65 graph binds scaled old product')
    require(add(U,Uold,-1) == mul(mul(D,add(Z,const(1),-1)),add(V,Y,-1)),
            'Exact auxiliary difference controlled by strong residual')
    normalized = add(product([(P,1),(Q,1),(U,1),(W,1),(Z,1)]),const(1),-1)
    require(add(mul(D,normalized),old,-1) ==
            product([(P,1),(Q,1),(W,1),(D,2),(Z,1),(add(Z,const(1),-1),1),(add(V,Y,-1),1)]),
            'Whole scaled-product difference identity')
    controls = {}
    for profile,graph in graphs.items():
        actual = evaluator(graph,cuts)('polynomial')
        require(actual == expected[profile], 'Every row binds independent full sphere formula')
        require(actual != old and actual != normalized, 'No all-ring identity with product parents')
        rejected = []
        for name in ('constant','strong_residual','wrong_theta','missing_square','wrong_transport_group'):
            bad = deepcopy(graph);g = {r[0]:r for r in bad['source']}
            if name == 'constant':g['polynomial'][3] += 1
            elif name == 'strong_residual':g['Z'][2] = 'f2minus1'
            elif name == 'wrong_theta':g['Theta'][3] = 'f2'
            elif name == 'missing_square':g['Z2'][3] = 1
            elif profile == 71:g['UW'][3] = 'N1'
            else:g['QW'][3] = 'N0'
            require(evaluator(bad,cuts)('polynomial') != expected[profile], 'Algebra rejects '+name)
            rejected.append(name)
        controls[profile] = rejected
    require(expected[71] != expected[72], 'Two proposed polynomials are distinct')
    cases71 = cases72 = 0
    for a,b,c in itertools.product(range(-3,4),repeat=3):
        if a and c:
            require((a*a+(b-1)**2+c*c == 2) == (a*a == c*c == 1 and b == 1),
                    'Bounded two-nonzero-square diagnostic')
            cases71 += 1
    for a,b,c,d in itertools.product(range(-3,4),repeat=4):
        if a and b and c:
            require((a*a+b*b+c*c+(d-1)**2 == 3) == (a*a == b*b == c*c == 1 and d == 1),
                    'Bounded three-nonzero-square diagnostic')
            cases72 += 1
    require(0**2+(0-1)**2+1**2 == 2 and 0**2+1**2+1**2+(0-1)**2 == 3,
            'Omitting nonzero premises permits unwanted zero groups')
    return {'cut_symbols':dict(zip(cuts,VARIABLES[:8])),
            'complete_old_cut_polynomial':rows(old_expected),
            'complete_new_cut_polynomials':{p:rows(e) for p,e in expected.items()},
            'whole_auxiliary_difference':rows(add(U,Uold,-1)),
            'algebraic_mutations':controls,'bounded_diagnostic_cases':{71:cases71,72:cases72},
            'all_ring_identity_to_parent':False,
            'scope':'Complete graph/formula binding and strong-controlled identities. Finite diagnostics do not replace the unbounded integer descent, nonzero premises, or positive-zero proofs.'}


def check_degree(graph,profile):
    full = evaluator(graph)
    main = full('N1')
    zmain = add(full('X'),mul(symbol('gamma'),full('H')))
    alternate = add(add(power(zmain,2),product([(full('a'),1),(full('c'),1),(zmain,1)],2)),
                    mul(full('H'),power(full('c'),2)),-1)
    require(main == alternate and degree(main) == 18 and len(main) == 323,
            'Entire323-term main norm and cancellation')
    leaders = {s:symbol(s) for s in SYMBOLS};cancellations=[]
    for name,op,l,r in graph['source']:
        a = const(l) if type(l) is int else leaders[l]
        b = const(r) if type(r) is int else leaders[r]
        if op == '*':result = mul(a,b)
        elif degree(a)>degree(b):result=a
        elif degree(b)>degree(a):result=b if op=='+' else mul(const(-1),b)
        else:result=add(a,b,1 if op=='+' else -1)
        if not result:
            cancellations.append(name);result=leading(full(name))
        require(bool(result),'Nonzero complete gate leader '+name)
        leaders[name]=result
    require(cancellations == ['N1'],'Every leading cancellation accounted for')
    q0=mul(symbol('beta'),symbol('J'));k0=add(symbol('eta'),symbol('zeta'))
    C0=add(add(q0,symbol('F'),-1),symbol('alpha'),-1)
    w,s,f,t,i,gamma,z=[symbol(n) for n in ('w','s','f','T','i','gamma','z')]
    factors={'N0':product([(w,2),(s,4),(k0,2),(q0,14)],-1),
             'N1':product([(gamma,1),(w,2),(s,3),(k0,1),(q0,11)],8),
             'U':product([(w,2),(s,4),(k0,2),(q0,14),(f,6),(t,2)]),
             'Nt':add(mul(w,C0),mul(z,q0),-1),
             'Z':product([(i,2),(w,2),(s,6),(k0,4),(q0,20)],-1)}
    require(all(leaders[n] == v for n,v in factors.items()),'All five complete factor leaders')
    require([degree(p) for p in factors.values()] == [22,18,30,2,34],'Exact factor degrees')
    if profile == 71:
        expected=product([(gamma,2),(w,8),(s,14),(k0,6),(q0,50)],64)
        chosen={'J':50,'beta':50,'eta':6,'gamma':2,'w':8,'s':14}
        coefficient,exponent=64,50
        require([degree(leaders[n]) for n in ('PQ2','rUW2','Z2')] == [80,64,68],
                'Three complete square degrees')
    else:
        expected=product([(i,4),(w,4),(s,12),(k0,8),(q0,40)])
        chosen={'J':40,'beta':40,'eta':8,'i':4,'w':4,'s':12}
        coefficient,exponent=1,40
        require([degree(leaders[n]) for n in ('P2','U2','Z2','rQW2')] == [44,60,68,40],
                'Four complete square degrees')
    require(leaders['polynomial'] == expected and degree(expected) == DEGREES[profile],
            'Exact entire output leader')
    require(expected.get(tuple(chosen.get(n,0) for n in SYMBOLS)) == coefficient,
            'Selected nonzero coefficient after actual beta specialization')
    return {'exact_degree':DEGREES[profile],'symbols':SYMBOLS,'complete_main_terms':len(main),
            'main_norm_sha256':sha(encoded(rows(main))),'cancellations':cancellations,
            'complete_factor_leaders':{n:rows(v) for n,v in factors.items()},
            'complete_leader':rows(expected),'selected_coefficient_factor':coefficient,
            'selected_beta_exponent':exponent,
            'selected_unknown_monomial':{n:e for n,e in chosen.items() if n in VARIABLES},
            'all_gate_leaders':{n:{'degree':degree(leaders[n]),'terms':len(leaders[n]),
                'sha256':sha(encoded(rows(leaders[n]))),'complete_leader':rows(leaders[n])}
                for n,_,_,_ in graph['source']}}


def check_ports(graph):
    pinned(NATIVE/'PROOF.md',PROOF_SHA)
    cert=json.loads(pinned(NATIVE/'certificate.json',CERT_SHA))
    c=json.loads(pinned(NATIVE/'coefficients.json',ARRAY_SHA))
    require(len(c)==3297 and all(type(v) is int and v>=0 for v in c),'All3297 actual coefficients')
    require(all(e<=1005 for e,v in enumerate(c) if v),'Natural reflected exponents')
    rp=lambda e:1<<(47*e)
    G=lambda n:sum(rp(e) for e in range(n))
    beta=rp(2011)-1
    K=rp(18)+rp(1004)+rp(2020)+sum(v*rp(1005-e) for e,v in enumerate(c) if v)
    MC=beta-G(951)-rp(960)*G(26)-rp(1004)
    native=8*G(917)-4+((1<<45)-4)*rp(1005)+rp(960)*G(9)+rp(987)*G(8)+rp(1004)
    values={'beta':beta,'K':K,'MC':MC,'MF_source':beta+native}
    records={n:record(v) for n,v in values.items()}
    require(records==cert['constant_ports'] and 0<MC<beta<beta+native<2*beta,
            'Exact current2011 whole integers and scalar boxes')
    binding=graph['coefficient_binding']
    require((HERE/binding['ordinary_proof']).resolve()==NATIVE/'PROOF.md' and
            (HERE/binding['certificate']).resolve()==NATIVE/'certificate.json','Exact native paths')
    for alias,name in {'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}.items():
        entry=binding['ports'][alias]
        raw=gzip.decompress(pinned(HERE/binding['path']/entry['file'],entry['gzip_sha256']))
        require(int.from_bytes(raw,'big')==values[name] and sha(raw)==entry['raw_sha256'] and
                len(raw)==entry['raw_bytes'] and values[name].bit_length()==entry['bits'],
                'Every whole materialized port '+alias)
    require(sum(v['bytes'] for v in records.values())==binding['raw_bytes']==47313,'Total raw bytes')
    require(MC+rp(1004)!=MC and beta+native+beta!=values['MF_source'],
            'Marker omission and duplicate source shift change whole ports')
    return values,{'ports':records,'raw_bytes':47313,'source_array_sha256':ARRAY_SHA,
                   'MF_shifted_exactly_once':True}


def negative_controls(graph,parent,profile):
    rejected=[]
    for name in ('wrong_constant','wrong_strong','missing_i_square','missing_c_square',
                 'wrong_theta','wrong_group','missing_square','rational_leaf','extra_variable',
                 'dead_gate','wrong_port','old_positive_y_changed'):
        bad=deepcopy(graph);g={r[0]:r for r in bad['source']}
        if name=='wrong_constant':g['polynomial'][3]+=1
        elif name=='wrong_strong':g['Z'][2]='f2minus1'
        elif name=='missing_i_square':g['i2'][3]=1
        elif name=='missing_c_square':g['strong_term'][3]=1
        elif name=='wrong_theta':g['Theta'][3]='f2'
        elif name=='wrong_group':g['UW' if profile==71 else 'QW'][3]='N0'
        elif name=='missing_square':g['Z2'][3]=1
        elif name=='rational_leaf':g['four_a'][2]=4.0
        elif name=='extra_variable':bad['witnesses'].append('unused')
        elif name=='dead_gate':bad['source'].append(['unused_gate','+',1,1])
        elif name=='wrong_port':bad['coefficient_binding']['ports']['MF']['bits']-=1
        else:g['y2'][2]='V'
        try:check_graph(bad,parent,profile)
        except ValueError as error:rejected.append({'mutation':name,'rejected_by':str(error)})
        else:raise ValueError('Corruption accepted '+name)
    return rejected


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='write only this new packet')
    args=parser.parse_args()
    for name,digest in [('Carrier65',PARENT_LEAN_SHA),('CarrierScaledAuxiliary118',SCALED_LEAN_SHA),
                        ('NearSquareNormZero',GENERIC_SHA),('NearSquareNormZeroChecks',GENERIC_CHECKS_SHA),
                        ('CarrierNonzeroSpheres',LEAN_SHA),('CarrierNonzeroSpheresChecks',CHECKS_SHA)]:
        pinned(ROOT/'Lean/DiophantineConsistency'/f'{name}.lean',digest)
    pinned(HERE/'PROOF.md',ZERO_SET_PROOF_SHA)
    parent=json.loads(pinned(PARENT/'polynomial.json',PARENT_SHA))
    graphs={p:expected_graph(parent,p) for p in TAILS}
    if args.write:
        (HERE/'coefficients').mkdir(exist_ok=True)
        for entry in parent['coefficient_binding']['ports'].values():
            payload=pinned(PARENT/'coefficients'/entry['file'],entry['gzip_sha256'])
            (HERE/'coefficients'/entry['file']).write_bytes(payload)
    for p,g in graphs.items():
        data=encoded(g);path=HERE/f'polynomial{p}.json'
        if args.write:path.write_bytes(data)
        else:require(path.read_bytes()==data,'Complete deterministic graph bytes')
    values,ports=check_ports(graphs[71])
    require(graphs[71]['coefficient_binding']==graphs[72]['coefficient_binding'],'Both exact bindings agree')
    profiles={}
    for p,g in graphs.items():
        deg=check_degree(g,p)
        deg['actual_selected_coefficient']=record(deg['selected_coefficient_factor']*
                                                 values['beta']**deg['selected_beta_exponent'])
        profiles[p]={'graph_sha256':sha(encoded(g)),'graph':check_graph(g,parent,p),
                     'degree':deg,'negative_controls':negative_controls(g,parent,p),
                     'actual_dependence':dependence_witnesses(g,values)}
    out={'schema':'fourteen_current2011_nonzero_spheres71_80_72_68_v1',
         'audit_sha256':sha(Path(__file__).read_bytes()),'parent_graph_sha256':PARENT_SHA,
         'parent_lean_sha256':PARENT_LEAN_SHA,'scaled_lean_sha256':SCALED_LEAN_SHA,
         'generic_lean_sha256':GENERIC_SHA,'generic_checks_sha256':GENERIC_CHECKS_SHA,
         'lean_sha256':LEAN_SHA,'checks_sha256':CHECKS_SHA,'ordinary_proof_sha256':ZERO_SET_PROOF_SHA,
         'profiles':profiles,'full_formula_bindings':check_formulas(graphs,parent),'current_ports':ports,
         'scope':'Complete literal schedules, all gate leaders and current2011 whole ports. Unbounded nonzero facts and entire positive-zero maps are separately Lean-proved. No internal HA/ZFC proof or global minimum.'}
    data=encoded(out)
    if args.write:(HERE/'CERTIFICATE.json').write_bytes(data)
    else:require((HERE/'CERTIFICATE.json').read_bytes()==data,'Deterministic complete receipt bytes')
    print(json.dumps({'status':'PASS','variables':14,'profiles':DEGREES,'raw_port_bytes':47313,
                      'certificate_sha256':sha(data)},sort_keys=True))


if __name__=='__main__':
    main()

