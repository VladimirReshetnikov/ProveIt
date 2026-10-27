#!/usr/bin/env python3
"""Two literal first-norm corrections92/90 and97/88 and current2011 whole-port audit.

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
LEAN_SHA = 'ea83a05732e96ebbadbab135f98018f5bcda115c887c1896b0f4be30a267bd22'
CHECKS_SHA = '578a95d1d5f3c497895bbeab3a54d719a9f7898e2478b7e750fa32c479b40409'
ZERO_SET_PROOF_SHA = 'ad5979f32d64c2ca41088e0572718b4602663c0870ea6e5f6539b88f030e91fe'
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


EXTRA90 = [
 ['bG','*','qm','B'],['bGT','*','bG','T'],['WG','*','bGT','V'],
 ['WGh','*','WG','f2minus1'],['VC','*','V','C'],['bGf2','*','bG','f2'],
 ['bGf2R','*','bGf2','R'],['gap2','-','VC','bGf2R'],['f2T','*','f2','T'],
 ['term2','*','f2T','gap2'],['twoterm2','*',2,'term2'],['bracket','+','WGh','twoterm2'],
 ['coeff0','*','WG','bracket'],['coeff','*',16,'coeff0'],['Pminus1','-','N0',1],
 ['correction','*','coeff','Pminus1'],['correctedU','-','Na','correction']]
EXTRA88 = [
 ['bG','*','qm','B'],['bG2','*','bG','bG'],['Vh','*','V','f2minus1'],
 ['firstterm','*','bG2','Vh'],['VC','*','V','C'],['XC','*','X','C'],
 ['twoBG','*',2,'bG'],['gap3','-','twoBG','XC'],['VCgap','*','VC','gap3'],
 ['f2R','*','f2','R'],['bG2f2R','*','bG2','f2R'],['inner3','-','VCgap','bG2f2R'],
 ['f2inner3','*','f2','inner3'],['twoinner3','*',2,'f2inner3'],
 ['bracket','+','firstterm','twoinner3'],['T2','*','T','T'],['T2V','*','T2','V'],
 ['coeff0','*','T2V','bracket'],['coeff','*',16,'coeff0'],['Pminus1','-','N0',1],
 ['correction','*','coeff','Pminus1'],['correctedU','-','Na','correction']]
VARIANTS = {90: {'extra':EXTRA90,'operations':92,'counts':{'*':55,'+':19,'-':18},
                  'aux_terms':75,'leader_terms':639,'beta_exp':40},
            88: {'extra':EXTRA88,'operations':97,'counts':{'*':59,'+':19,'-':19},
                  'aux_terms':302,'leader_terms':7112,'beta_exp':38}}


def expected_graph(parent,d):
    v=VARIANTS[d]
    require(len(parent['source'])==75 and parent['source'][67]==['Z','-','f2','strong_term'],
            'Exact parent prefix boundary')
    require(parent['source'][70]==['sqU','*','Na','Na'],'Exact replaced sphere row')
    out=deepcopy(parent)
    out.update(name=f'thirteen_positive2011_correction{v["operations"]}_degree{d}',
        operations=v['operations'],operation_counts=v['counts'],exact_degree=d,
        arithmetic_proof='../../Lean/DiophantineConsistency/ThirteenSecondFirstNormCorrections.lean',
        arithmetic_proof_sha256=LEAN_SHA,lean_variant_boolean=d==88,
        parent_polynomial='../thirteen-unit-sphere96/polynomial.json',
        parent_polynomial_sha256=PARENT_SHA,zero_set_proof='PROOF.md',
        zero_set_proof_sha256=ZERO_SET_PROOF_SHA,
        proof_boundary='Different polynomial; entire positive zero set unchanged with identity witnesses. Actual external Lean ConZFC endpoint; no internal HA/PA/ZFC or minimum claim.')
    out['source']=deepcopy(parent['source'][:68])+deepcopy(v['extra'])+deepcopy(parent['source'][68:])
    for row in out['source']:
        if row[0]=='sqU':row[2]=row[3]='correctedU'
    out['display_scalar_names'].update(correctedU='Uc',coeff='A')
    return out


def check_graph(graph,parent,d):
    v=VARIANTS[d]
    require(graph==expected_graph(parent,d),'Entire expected graph and metadata')
    require(graph['witnesses']==VARIABLES and graph['fixed_numerals']==PORTS,'Exact13+4 order')
    known,gates=set(SYMBOLS),{}
    for name,op,l,r in graph['source']:
        require(type(name)is str and name not in known and op in ('+','-','*'),'Legal unique gate')
        require(all(type(x)is int or type(x)is str and x in known for x in (l,r)),
                'Integer leaves and topological order')
        known.add(name);gates[name]=(op,l,r)
    counts=dict(Counter(r[1] for r in graph['source']))
    require(len(gates)==v['operations'] and counts==v['counts'],'All paid binary operations')
    live=set()
    def visit(x):
        if type(x)is int or x in live:return
        live.add(x)
        if x in gates:visit(gates[x][1]);visit(gates[x][2])
    visit('polynomial');require(live==known,'All gates and13 variables and4 ports live')
    names={r[0] for r in v['extra']}|{'sqU'}
    require([r for r in graph['source'] if r[0] not in names]==
            [r for r in parent['source'] if r[0]!='sqU'],'All74 unchanged rows and order')
    require(all(n in gates for n in graph['display_scalar_names']),'Displayed aliases live')
    return {'operations':counts,'live_gates':v['operations'],'live_variables':13,'live_ports':4,
            'unchanged_parent_rows':74,'inserted_rows':v['extra'],
            'replaced_row':['sqU','*','correctedU','correctedU']}


def check_identity(graph,parent,d):
    names=['N0','N1','Na','Z','qm','T','B','V','f2','C','R','X']
    P,Q,U,Z,b,T,G,V,F2,C,R,X=[symbol(n) for n in VARIABLES[:12]]
    cuts=dict(zip(names,[P,Q,U,Z,b,T,G,V,F2,C,R,X]))
    h=add(F2,const(1),-1); W=product([(b,1),(T,1),(G,1),(V,1)])
    gap=add(mul(V,C),product([(b,1),(G,1),(F2,1),(R,1)]),-1)
    A90=product([(W,1),(add(mul(W,h),product([(F2,1),(T,1),(gap,1)],2)),1)],16)
    D=add(mul(X,C),mul(b,G),-1)
    A88=add(A90,product([(F2,1),(T,2),(V,2),(C,1),(D,1)],32),-1)
    coefficient=A90 if d==90 else A88
    get=evaluator(graph,cuts)
    require(get('coeff')==coefficient,'Complete direct-versus-factored coefficient identity')
    correction=mul(coefficient,add(P,const(1),-1));uc=add(U,correction,-1)
    expected=add(add(add(power(mul(P,Q),2),power(uc,2)),power(Z,2)),const(3),-1)
    oldexpected=add(add(add(power(mul(P,Q),2),power(U,2)),power(Z,2)),const(3),-1)
    new=get('polynomial');old=evaluator(parent,cuts)('polynomial')
    require(new==expected and old==oldexpected,'Whole graph binds exact new/old formula')
    difference=add(power(correction,2),product([(U,1),(correction,1)],2),-1)
    require(new!=old and add(new,old,-1)==difference,'Exact nonzero polynomial difference')
    controls=[]
    for name in ('coefficient15','coefficient17','wrong_P','wrong_vanishing_constant',
                 'added_correction','missing_term2','wrong_R','sphere_two'):
        bad=deepcopy(graph);gates={r[0]:r for r in bad['source']}
        if name=='coefficient15':gates['coeff'][2]=15
        elif name=='coefficient17':gates['coeff'][2]=17
        elif name=='wrong_P':gates['Pminus1'][2]='N1'
        elif name=='wrong_vanishing_constant':gates['Pminus1'][3]=2
        elif name=='added_correction':gates['correctedU'][1]='+'
        elif name=='missing_term2':gates['bracket'][3]=0
        elif name=='wrong_R':gates['bGf2R' if d==90 else 'f2R'][3]='C'
        else:gates['polynomial'][3]=2
        require(evaluator(bad,cuts)('polynomial')!=expected,'Algebra rejects '+name)
        controls.append(name)
    return {'cut_symbols':dict(zip(names,VARIABLES[:12])),
            'complete_coefficient':rows(coefficient),'complete_new_cut_polynomial':rows(new),
            'complete_parent_cut_polynomial':rows(old),'complete_difference':rows(difference),
            'polynomial_equal_to_parent':False,'algebraic_negative_controls':controls,
            'scope':'Entire exact coefficient/formula identity and difference. Positive-zero theorem is separately Lean-proved, not sampled.'}


def check_degree(graph,parent_cert,d):
    v=VARIANTS[d];full=evaluator(graph);main=full('N1')
    main_root=add(full('X'),mul(symbol('gamma'),full('H')))
    main_alt=add(add(power(main_root,2),product([(full('a'),1),(full('c'),1),(main_root,1)],2)),
                 mul(full('H'),power(full('c'),2)),-1)
    require(main==main_alt and degree(main)==18 and len(main)==323,'Complete main norm')
    layers={s:(1 if s in VARIABLES else 0,symbol(s)) for s in SYMBOLS}
    leaders={};cancellations=[];width=6
    for name,op,l,r in graph['source']:
        da,a=(0,const(l)) if type(l)is int else layers[l]
        db,b=(0,const(r)) if type(r)is int else layers[r]
        bound=da+db if op=='*' else max(da,db)
        result=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
        result={m:c for m,c in result.items() if sum(m[:13])>=bound-width}
        if name=='N1':
            cancellations.append({'gate':name,'bound_before':bound,'bound_after':18});bound=18
            result={m:c for m,c in main.items() if sum(m[:13])>=18-width}
        if name=='correctedU':
            require(bound==48 and degree(result)==d//2,'All required leading layers cancel')
            cancellations.append({'gate':name,'bound_before':bound,'bound_after':d//2})
            bound=d//2;result=leading(result)
        if name in ('sqU','sumPQ_U','sumSquares','polynomial'):
            result={m:c for m,c in result.items() if sum(m[:13])==bound}
        require(result and degree(result)==bound,'Every other bound is sharp: '+name)
        layers[name]=(bound,result);leaders[name]=leading(result)
    auxiliary=leaders['correctedU']
    require(len(auxiliary)==v['aux_terms'],'Complete corrected auxiliary term count')
    if d==90:
        B=mul(symbol('beta'),symbol('J'));k=add(symbol('eta'),symbol('zeta'))
        C0=add(add(B,symbol('F'),-1),symbol('alpha'),-1)
        D0=add(mul(add(symbol('w'),mul(B,symbol('K0')),-1),C0),mul(B,symbol('F')))
        expected90=product([(B,20),(k,4),(symbol('f'),6),(symbol('T'),4),
                            (symbol('s'),6),(symbol('w'),2),(C0,1),(D0,1)],32)
        require(auxiliary==expected90,'Independent compact75-term auxiliary leader')
    expected=power(auxiliary,2)
    require(leaders['polynomial']==expected and degree(expected)==d and len(expected)==v['leader_terms'],
            'Whole exact output leader')
    chosen=({'J':40,'beta':40,'alpha':4,'f':12,'T':8,'s':12,'w':6,'zeta':8} if d==90 else
            {'J':38,'beta':38,'alpha':4,'f':12,'T':8,'s':10,'w':8,'eta':2,'zeta':6})
    key=tuple(chosen.get(n,0) for n in SYMBOLS)
    require(expected.get(key)==1024,'Selected nonzero actual coefficient')
    require([(m,c) for m,c in expected.items() if m[:13]==key[:13]]==[(key,1024)],
            'No specialization cancellation at selected unknown monomial')
    all_leaders={n:{'degree':degree(leaders[n]),'terms':len(leaders[n]),
                   'sha256':sha(encoded(rows(leaders[n]))),'complete_leader':rows(leaders[n])}
                 for n,_,_,_ in graph['source']}
    excluded={r[0] for r in v['extra']}|{'sqU','sumPQ_U','sumSquares','polynomial'}
    matched=0
    for n,entry in all_leaders.items():
        if n not in excluded:
            require(entry==parent_cert['exact_degree']['all_gate_leaders'][n],
                    'Entire unchanged parent leader '+n);matched+=1
    require(matched==71,'All71 unaffected parent leaders')
    return {'exact_degree':d,'symbols':SYMBOLS,'all_gate_leaders':all_leaders,
            'complete_leader':rows(expected),'complete_corrected_auxiliary_leader':rows(auxiliary),
            'cancellations':cancellations,'complete_main_norm_terms':len(main),
            'main_norm_sha256':sha(encoded(rows(main))),'matching_parent_gate_leaders':matched,
            'selected_unknown_monomial':{n:e for n,e in chosen.items() if n in VARIABLES},
            'selected_coefficient':f'1024*beta^{v["beta_exp"]}',
            'method':'Seven highest homogeneous layers at sharp bounds before correctedU; full main norm; exact auxiliary and output leaders after correction. No full-polynomial expansion claim.'}


def check_ports(graph,d):
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
            'selected_actual_leader_coefficient_magnitude':record(1024*beta**VARIANTS[d]['beta_exp']),
            'selected_actual_leader_coefficient_sign':1,'MF_shifted_exactly_once':True,
            'actual_polynomial_dependence':dependence_witnesses(graph,values)}


def negative_controls(graph,parent,d):
    failures=[]
    for name in ('coefficient15','Pminus2','wrong_sphere','wrong_port','rational_leaf',
                 'extra_variable','dead_gate','missing_correction','wrong_first_norm'):
        bad=deepcopy(graph);gates={r[0]:r for r in bad['source']}
        if name=='coefficient15':gates['coeff'][2]=15
        elif name=='Pminus2':gates['Pminus1'][3]=2
        elif name=='wrong_sphere':gates['polynomial'][3]=2
        elif name=='wrong_port':bad['coefficient_binding']['ports']['MF']['bits']-=1
        elif name=='rational_leaf':gates['coeff'][2]=16.0
        elif name=='extra_variable':bad['witnesses'].append('unused')
        elif name=='dead_gate':bad['source'].append(['dead','+','f',1])
        elif name=='missing_correction':gates['sqU'][2]=gates['sqU'][3]='Na'
        else:gates['Pminus1'][2]='N1'
        try:check_graph(bad,parent,d)
        except ValueError as error:failures.append({'mutation':name,'rejected_by':str(error)})
        else:raise ValueError('Corruption accepted: '+name)
    return failures


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='materialize only this new packet')
    args=parser.parse_args()
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenUnitSphere96.lean',PARENT_LEAN_SHA)
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenFirstNormCorrection92.lean',
           '1cd3641065d40e32cbb7ed91f204ac667439aeddc45ffc9581e39c594f9e3386')
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenSecondFirstNormCorrections.lean',LEAN_SHA)
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenSecondFirstNormCorrectionsChecks.lean',CHECKS_SHA)
    pinned(PARENT/'audit.py',PARENT_AUDIT_SHA)
    parent_cert=json.loads(pinned(PARENT/'CERTIFICATE.json',PARENT_CERT_SHA))
    pinned(PARENT/'PROOF.md',PARENT_PROOF_SHA);pinned(HERE/'PROOF.md',ZERO_SET_PROOF_SHA)
    parent=json.loads(pinned(PARENT/'polynomial.json',PARENT_SHA))
    receipt={'schema':'thirteen_second_first_norm_corrections_90_88_v1',
        'audit_sha256':sha(Path(__file__).read_bytes()),'parent_graph_sha256':PARENT_SHA,
        'parent_audit_sha256':PARENT_AUDIT_SHA,'parent_certificate_sha256':PARENT_CERT_SHA,
        'parent_proof_sha256':PARENT_PROOF_SHA,'parent_lean_sha256':PARENT_LEAN_SHA,
        'lean_source_sha256':LEAN_SHA,'lean_checks_sha256':CHECKS_SHA,
        'zero_set_proof_sha256':ZERO_SET_PROOF_SHA,'variants':{},
        'scope':'All92/97 rows, exact whole formulas and all-gate leaders; actual whole current2011 ports. Entire positive zero maps and external ConZFC endpoints are Lean-proved separately; no internal HA/PA/ZFC or optimum claim.'}
    for d in (90,88):
        graph=expected_graph(parent,d);graph_bytes=encoded(graph)
        filename=f'polynomial{d}.json'
        if args.write:
            (HERE/'coefficients').mkdir(exist_ok=True)
            for entry in graph['coefficient_binding']['ports'].values():
                raw=pinned(PARENT/'coefficients'/entry['file'],entry['gzip_sha256'])
                (HERE/'coefficients'/entry['file']).write_bytes(raw)
            (HERE/filename).write_bytes(graph_bytes)
        else:require((HERE/filename).read_bytes()==graph_bytes,'Exact graph bytes '+filename)
        item={'graph_sha256':sha(graph_bytes),'graph':check_graph(graph,parent,d),
              'whole_graph_formula':check_identity(graph,parent,d),'exact_degree':check_degree(graph,parent_cert,d),
              'current_ports':check_ports(graph,d),'negative_controls':negative_controls(graph,parent,d)}
        excluded={'actual_polynomial_dependence','selected_actual_leader_coefficient_magnitude'}
        require({k:v for k,v in item['current_ports'].items() if k not in excluded}==
                {k:v for k,v in parent_cert['current_ports'].items() if k not in excluded},
                'All actual whole-port metadata unchanged')
        new=item['current_ports']['actual_polynomial_dependence']
        old=parent_cert['current_ports']['actual_polynomial_dependence']
        a,b=new['witnesses']['J'],old['witnesses']['J']
        require(new['modulus']==old['modulus'] and a['all_unknowns_before']==b['all_unknowns_before']==1
                and a['before']!=b['before'],'Actual positive assignment distinguishes polynomials')
        item['actual_parent_nonidentity_witness']={'all_unknowns':1,
            'ports':'complete actual current2011 integers','modulus':new['modulus'],
            'new_value':a['before'],'parent_value':b['before']}
        receipt['variants'][str(d)]=item
    data=encoded(receipt)
    if args.write:(HERE/'CERTIFICATE.json').write_bytes(data)
    else:require((HERE/'CERTIFICATE.json').read_bytes()==data,'Exact deterministic certificate')
    print(json.dumps({'status':'PASS','variables':13,'frontier':[[92,90],[97,88]],
        'raw_port_bytes':47313,'certificate_sha256':sha(data)},sort_keys=True))


if __name__=='__main__':main()
