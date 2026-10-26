#!/usr/bin/env python3
"""Literal first-norm correction84/92 graph and current2011 whole-port audit.

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
PARENT = ROOT / 'research/thirteen-unit-sphere96'
PARENT_SHA = '48573f58aac3d60f706eb7f52e92f5c061bd74d41ad7e9e9ee3e2ea43dcd9ca1'
PARENT_AUDIT_SHA = 'a459434a804f13d0aabd4dbd2fe53bd19846163e4e396076b72c1a01c6e669d0'
PARENT_CERT_SHA = 'fd8c02774985bb3b8fef11294a3d9dc8198312b6fc38228a5f651c4d05fd4acc'
PARENT_PROOF_SHA = 'b2d4edb3ef89dcd3e4798400d8afe422b7c66552191d31f73c4f3e549bd56a42'
PARENT_LEAN_SHA = '6589cdb6a7f4c97bd58eab10e6d3a05ff34189834f0660f8ca5eba3a3d954ab8'
LEAN_SHA = '1cd3641065d40e32cbb7ed91f204ac667439aeddc45ffc9581e39c594f9e3386'
CHECKS_SHA = '3b059baa5d5fda30554dd767b997ac9ef83f6799eb000fd19a895454e0f10460'
ZERO_SET_PROOF_SHA = 'f12015ebee3c930caa8ddc04c864de7bfc5d6c6068777fb0fd8e145e0f7c5e32'
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


EXTRA = [
 ['bT','*','qm','T'], ['bTG','*','bT','B'], ['bTGV','*','bTG','V'],
 ['bTGV2','*','bTGV','bTGV'], ['corr0','*','bTGV2','f2'],
 ['corrCoefficient','*',16,'corr0'], ['Pminus1','-','N0',1],
 ['correction','*','corrCoefficient','Pminus1'], ['correctedU','-','Na','correction']]


def expected_graph(parent):
    require(len(parent['source']) == 75 and parent['source'][67] == ['Z','-','f2','strong_term'],
            'Exact parent prefix boundary')
    require(parent['source'][70] == ['sqU','*','Na','Na'], 'Exact replaced sphere row')
    out = deepcopy(parent)
    out.update(name='thirteen_positive2011_first_norm_correction84_degree92',
        operations=84, operation_counts={'*':49,'+':18,'-':17}, exact_degree=92,
        arithmetic_proof='../../Lean/DiophantineConsistency/ThirteenFirstNormCorrection92.lean',
        arithmetic_proof_sha256=LEAN_SHA,
        parent_polynomial='../thirteen-unit-sphere96/polynomial.json',
        parent_polynomial_sha256=PARENT_SHA, zero_set_proof='PROOF.md',
        zero_set_proof_sha256=ZERO_SET_PROOF_SHA,
        proof_boundary='Different polynomial; identical entire positive integer zero set by identity witness maps. Exact actual external Lean endpoint inherited; no internal HA/PA/ZFC proof or minimum claim.')
    out['source'] = deepcopy(parent['source'][:68])+deepcopy(EXTRA)+deepcopy(parent['source'][68:])
    for row in out['source']:
        if row[0] == 'sqU': row[2] = row[3] = 'correctedU'
    out['display_scalar_names'].update(correctedU='Uc',corrCoefficient='A')
    return out


def check_graph(graph,parent):
    require(graph == expected_graph(parent), 'Entire expected graph and metadata')
    require(graph['witnesses'] == VARIABLES and graph['fixed_numerals'] == PORTS,'Exact13+4 order')
    known,gates=set(SYMBOLS),{}
    for name,op,l,r in graph['source']:
        require(type(name) is str and name not in known and op in ('+','-','*'),'Legal unique gate')
        require(all(type(x) is int or type(x) is str and x in known for x in (l,r)),
                'Integer leaves and topological order')
        known.add(name);gates[name]=(op,l,r)
    counts=dict(Counter(r[1] for r in graph['source']))
    require(len(gates)==84 and counts=={'*':49,'+':18,'-':17},'All84 paid binary operations')
    live=set()
    def visit(x):
        if type(x) is int or x in live:return
        live.add(x)
        if x in gates:visit(gates[x][1]);visit(gates[x][2])
    visit('polynomial');require(live==known,'All84 gates and13 variables and4 ports live')
    newnames={r[0] for r in EXTRA}|{'sqU'}
    require([r for r in graph['source'] if r[0] not in newnames]==
            [r for r in parent['source'] if r[0]!='sqU'],'All74 unchanged rows and order')
    require(all(n in gates for n in graph['display_scalar_names']),'Displayed aliases live')
    return {'operations':counts,'live_gates':84,'live_variables':13,'live_ports':4,
            'unchanged_parent_rows':74,'inserted_rows':EXTRA,
            'replaced_row':['sqU','*','correctedU','correctedU']}


def check_identity(graph,parent):
    names=['N0','N1','Na','Z','qm','T','B','V','f2']
    P,Q,U,Z,b,T,G,V,F2=[symbol(n) for n in VARIABLES[:9]]
    cuts=dict(zip(names,[P,Q,U,Z,b,T,G,V,F2]))
    coefficient=product([(b,2),(T,2),(G,2),(V,2),(F2,1)],16)
    correction=mul(coefficient,add(P,const(1),-1))
    uc=add(U,correction,-1)
    expected=add(add(add(power(mul(P,Q),2),power(uc,2)),power(Z,2)),const(3),-1)
    oldexpected=add(add(add(power(mul(P,Q),2),power(U,2)),power(Z,2)),const(3),-1)
    new=evaluator(graph,cuts)('polynomial');old=evaluator(parent,cuts)('polynomial')
    require(new==expected and old==oldexpected,'Whole graph binds exact new/old formula')
    difference=add(power(correction,2),mul(const(2),mul(U,correction)),-1)
    require(new!=old and add(new,old,-1)==difference,'Exact nonzero polynomial difference')
    controls=[]
    for name in ('coefficient15','coefficient17','wrong_P','wrong_vanishing_constant',
                 'added_correction','missing_f2','missing_correction_square','sphere_two'):
        bad=deepcopy(graph);gates={r[0]:r for r in bad['source']}
        if name=='coefficient15':gates['corrCoefficient'][2]=15
        elif name=='coefficient17':gates['corrCoefficient'][2]=17
        elif name=='wrong_P':gates['Pminus1'][2]='N1'
        elif name=='wrong_vanishing_constant':gates['Pminus1'][3]=2
        elif name=='added_correction':gates['correctedU'][1]='+'
        elif name=='missing_f2':gates['corr0'][3]=1
        elif name=='missing_correction_square':gates['bTGV2'][3]=1
        else:gates['polynomial'][3]=2
        require(evaluator(bad,cuts)('polynomial')!=expected,'Algebra rejects '+name)
        controls.append(name)
    return {'cut_symbols':dict(zip(names,VARIABLES[:9])),
            'complete_new_cut_polynomial':rows(new),'complete_parent_cut_polynomial':rows(old),
            'complete_difference':rows(difference),'polynomial_equal_to_parent':False,
            'algebraic_negative_controls':controls,
            'scope':'Entire exact formula identity and difference. Positive-zero theorem uses integer unit sphere plus P,Q negative-unit exclusions; not tested by finite sampling.'}


def check_degree(graph,parent_cert):
    # Exact two-highest-drop layers suffice for the new cancellation.
    # Multiplication drops only terms whose proven maximum degree is below
    # the output upper bound minus two; addition truncates at the same cut.
    # Q is expanded completely to handle its separate degree cancellation.
    full=evaluator(graph);main=full('N1')
    main_root=add(full('X'),mul(symbol('gamma'),full('H')))
    main_alt=add(add(power(main_root,2),product([(full('a'),1),(full('c'),1),(main_root,1)],2)),
                 mul(full('H'),power(full('c'),2)),-1)
    require(main==main_alt and degree(main)==18 and len(main)==323,'Complete main norm')
    layers={s:(1 if s in VARIABLES else 0,symbol(s)) for s in SYMBOLS}
    leaders={};cancellations=[]
    for name,op,l,r in graph['source']:
        da,a=(0,const(l)) if type(l) is int else layers[l]
        db,b=(0,const(r)) if type(r) is int else layers[r]
        bound=da+db if op=='*' else max(da,db)
        result=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
        result={m:c for m,c in result.items() if sum(m[:13])>=bound-2}
        if name=='N1':
            cancellations.append(name);bound=18
            result={m:c for m,c in main.items() if sum(m[:13])>=16}
        if name=='correctedU':
            require(bound==48 and degree(result)==46,'Exact degree48 and47 cancellation')
            cancellations.append(name);bound=46;result=leading(result)
        if name=='sqU':
            # Only Uc's exact leader is retained after sharpening its bound.
            # No later gate can affect degree92 with a lower-degree branch.
            result={m:c for m,c in result.items() if sum(m[:13])==92}
        require(result and degree(result)==bound,'Every other bound is sharp: '+name)
        layers[name]=(bound,result);leaders[name]=leading(result)
    q0=mul(symbol('beta'),symbol('J'));k0=add(symbol('eta'),symbol('zeta'))
    C0=add(add(q0,symbol('F'),-1),symbol('alpha'),-1)
    f,T,s,w=[symbol(n) for n in ('f','T','s','w')]
    bracket=add(add(product([(q0,1),(k0,1),(T,1),(s,1),(w,1)]),
                    product([(k0,1),(f,2),(T,1),(s,1)],2),-1),
                product([(q0,1),(f,2),(w,1),(add(q0,symbol('F'),-1),1)],2))
    expectedU=mul(product([(q0,21),(k0,3),(f,4),(T,3),(s,5),(w,3),(C0,2)],16),bracket)
    require(leaders['correctedU']==expectedU and degree(expectedU)==46 and len(expectedU)==96,
            'Exact factored96-term corrected auxiliary leader')
    expected=power(expectedU,2)
    require(leaders['polynomial']==expected and degree(expected)==92 and len(expected)==900,
            'Whole900-term output leader')
    chosen={'J':42,'beta':42,'alpha':4,'f':12,'T':8,'s':12,'w':6,'zeta':8}
    key=tuple(chosen.get(n,0) for n in SYMBOLS)
    require(expected.get(key)==1024,'Actual selected nonzero coefficient1024beta42')
    # No other beta/port exponent can contribute to the same unknown monomial.
    require([(m,c) for m,c in expected.items() if m[:13]==key[:13]]==[(key,1024)],
            'No specialization cancellation in selected coefficient')
    all_leaders={n:{'degree':degree(leaders[n]),'terms':len(leaders[n]),
                   'sha256':sha(encoded(rows(leaders[n]))),'complete_leader':rows(leaders[n])}
                 for n,_,_,_ in graph['source']}
    excluded={r[0] for r in EXTRA}|{'sqU','sumPQ_U','sumSquares','polynomial'}
    matched=0
    for n,entry in all_leaders.items():
        if n not in excluded:
            require(entry==parent_cert['exact_degree']['all_gate_leaders'][n],
                    'Entire unchanged parent leader '+n);matched+=1
    require(matched==71,'All71 unaffected parent leaders')
    return {'exact_degree':92,'symbols':SYMBOLS,'all_gate_leaders':all_leaders,
            'complete_leader':rows(expected),'complete_corrected_auxiliary_leader':rows(expectedU),
            'cancellations':cancellations,'complete_main_norm_terms':len(main),
            'main_norm_sha256':sha(encoded(rows(main))),'matching_parent_gate_leaders':matched,
            'selected_unknown_monomial':{n:e for n,e in chosen.items() if n in VARIABLES},
            'selected_coefficient':'1024*beta^42',
            'method':'Exact degree upper bounds and highest three homogeneous layers before Uc; full main norm; exact Uc/output leaders after its bound drops by two.'}


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
            'selected_actual_leader_coefficient_magnitude':record(1024*beta**42),
            'selected_actual_leader_coefficient_sign':1,'MF_shifted_exactly_once':True,
            'actual_polynomial_dependence':dependence_witnesses(graph,values)}


def negative_controls(graph,parent):
    failures=[]
    for name in ('coefficient15','Pminus2','wrong_sphere','wrong_port','rational_leaf',
                 'extra_variable','dead_gate','missing_correction','wrong_first_norm'):
        bad=deepcopy(graph);gates={r[0]:r for r in bad['source']}
        if name=='coefficient15':gates['corrCoefficient'][2]=15
        elif name=='Pminus2':gates['Pminus1'][3]=2
        elif name=='wrong_sphere':gates['polynomial'][3]=2
        elif name=='wrong_port':bad['coefficient_binding']['ports']['MF']['bits']-=1
        elif name=='rational_leaf':gates['corrCoefficient'][2]=16.0
        elif name=='extra_variable':bad['witnesses'].append('unused')
        elif name=='dead_gate':bad['source'].append(['dead','+','f',1])
        elif name=='missing_correction':gates['sqU'][2]=gates['sqU'][3]='Na'
        else:gates['Pminus1'][2]='N1'
        try:check_graph(bad,parent)
        except ValueError as error:failures.append({'mutation':name,'rejected_by':str(error)})
        else:raise ValueError('Corruption accepted: '+name)
    return failures


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='materialize only this new packet')
    args=parser.parse_args()
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenUnitSphere96.lean',PARENT_LEAN_SHA)
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenFirstNormCorrection92.lean',LEAN_SHA)
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenFirstNormCorrection92Checks.lean',CHECKS_SHA)
    pinned(PARENT/'audit.py',PARENT_AUDIT_SHA)
    parent_cert=json.loads(pinned(PARENT/'CERTIFICATE.json',PARENT_CERT_SHA))
    pinned(PARENT/'PROOF.md',PARENT_PROOF_SHA);pinned(HERE/'PROOF.md',ZERO_SET_PROOF_SHA)
    parent=json.loads(pinned(PARENT/'polynomial.json',PARENT_SHA))
    graph=expected_graph(parent);graph_bytes=encoded(graph)
    if args.write:
        (HERE/'coefficients').mkdir(exist_ok=True)
        for entry in graph['coefficient_binding']['ports'].values():
            raw=pinned(PARENT/'coefficients'/entry['file'],entry['gzip_sha256'])
            (HERE/'coefficients'/entry['file']).write_bytes(raw)
        (HERE/'polynomial.json').write_bytes(graph_bytes)
    else:require((HERE/'polynomial.json').read_bytes()==graph_bytes,'Exact graph bytes')
    receipt={'schema':'thirteen_first_norm_correction84_92_v1',
        'audit_sha256':sha(Path(__file__).read_bytes()),'parent_graph_sha256':PARENT_SHA,
        'parent_audit_sha256':PARENT_AUDIT_SHA,'parent_certificate_sha256':PARENT_CERT_SHA,
        'parent_proof_sha256':PARENT_PROOF_SHA,'parent_lean_sha256':PARENT_LEAN_SHA,
        'lean_source_sha256':LEAN_SHA,'lean_checks_sha256':CHECKS_SHA,
        'zero_set_proof_sha256':ZERO_SET_PROOF_SHA,'graph_sha256':sha(graph_bytes),
        'graph':check_graph(graph,parent),'whole_graph_formula':check_identity(graph,parent),
        'exact_degree':check_degree(graph,parent_cert),'current_ports':check_ports(graph),
        'negative_controls':negative_controls(graph,parent),
        'scope':'All84 rows/formula, complete all-gate leaders, current whole ports. Entire positive zero sets and external current ConZFC equivalence are Lean-proved separately. No internal HA/PA/ZFC proof or global minimum.'}
    excluded={'actual_polynomial_dependence','selected_actual_leader_coefficient_magnitude'}
    require({k:v for k,v in receipt['current_ports'].items() if k not in excluded}==
            {k:v for k,v in parent_cert['current_ports'].items() if k not in excluded},
            'All actual whole-port metadata unchanged')
    new=receipt['current_ports']['actual_polynomial_dependence']
    old=parent_cert['current_ports']['actual_polynomial_dependence']
    a,b=new['witnesses']['J'],old['witnesses']['J']
    require(new['modulus']==old['modulus'] and a['all_unknowns_before']==b['all_unknowns_before']==1
            and a['before']!=b['before'],'Actual positive assignment distinguishes polynomials')
    receipt['actual_parent_nonidentity_witness']={'all_unknowns':1,
        'ports':'complete actual current2011 integers','modulus':new['modulus'],
        'new_value':a['before'],'parent_value':b['before']}
    data=encoded(receipt)
    if args.write:(HERE/'CERTIFICATE.json').write_bytes(data)
    else:require((HERE/'CERTIFICATE.json').read_bytes()==data,'Exact deterministic certificate')
    print(json.dumps({'status':'PASS','variables':13,'operations':84,'exact_degree':92,
        'raw_port_bytes':47313,'graph_sha256':sha(graph_bytes),'certificate_sha256':sha(data)},sort_keys=True))


if __name__=='__main__':main()
