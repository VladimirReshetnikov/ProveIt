#!/usr/bin/env python3
"""Complete scoped13/178/86 literal graph audit. Standard library only.
No project/incoming program is imported or executed. --write touches only
this new packet; default and -O compare the complete deterministic artifacts.
"""
import argparse
from collections import Counter
from copy import deepcopy
import gzip,hashlib,json,resource,shutil
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'research/thirteen-second-first-norm-corrections'
PARENT_SHA='32d896933d3f3a524adfad130bacddd5cb137bfe9438e62dfcfec570a8c0e8e1'
PARENT_CERT_SHA='b05205f7a5e40dcddf78d77fd6a170a79c4e0df45c3ba23c9bc8b68c3f44d3e5'
PARENT_LEAN_SHA='ea83a05732e96ebbadbab135f98018f5bcda115c887c1896b0f4be30a267bd22'
LEAN_SHA='53be78f9046b591dcd1a33421d3dae3e14764537ac19fa0906665e3e0829f253'
CHECKS_SHA='9a4b58d6ff9eddb83ce2013d18da867211b70abffac03ba9de99bbc1f82c8c4f'
ZERO_SET_PROOF_SHA='609fcdece2ba042a1fa0c5cf73783a8b76cda4d2238e6e1fcf1a28464bd6adf7'
NATIVE=ROOT/'research/padding-staircase-independent'
PROOF_SHA='69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8'
CERT_SHA='fae49c56a9c57d394335c8a47da395f000a0c25cb8267d1330104eddbbc7850f'
ARRAY_SHA='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93'
VARIABLES=['J','F','alpha','f','i','T','s','w','n','eta','zeta','m','gamma']
PORTS=['beta','K0','MC','MF'];SYMBOLS=VARIABLES+PORTS;ZERO=(0,)*17
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
    ['r89', '*', 'K0', 'C'],
    ['r90', '-', 'r89', 'F'],
    ['r91', '*', 'k', 's'],
    ['r92', '*', 'r91', 'q2'],
    ['r93', '*', 'X', 'R'],
    ['r94', '*', 'T', 'kY'],
    ['r95', '-', 'r93', 'r94'],
    ['r96', '*', 'X', 'eta'],
    ['r97', '*', 'C', 'r95'],
    ['r98', '*', 'X', 'r94'],
    ['r99', '*', 2, 'r98'],
    ['r100', '*', 3, 'r93'],
    ['r101', '-', 'r100', 'r94'],
    ['r102', '*', 'f2', 'r101'],
    ['r103', '+', 'r99', 'r102'],
    ['r104', '*', 'r97', 'r103'],
    ['r105', '*', 'f2', 'T2'],
    ['r106', '*', 2, 'r105'],
    ['r107', '*', 'kY', 'r96'],
    ['r108', '*', 'r92', 'r92'],
    ['r109', '+', 'r107', 'r108'],
    ['r110', '*', 'XC', 'r109'],
    ['r111', '*', 'r106', 'r110'],
    ['r112', '*', 'f2', 'r90'],
    ['r113', '*', 4, 'r112'],
    ['r114', '*', 'r94', 'r94'],
    ['r115', '*', 'r113', 'r114'],
    ['r116', '-', 'r111', 'r115'],
    ['r117', '+', 'r104', 'r116'],
    ['r118', '*', 'f2', 'T'],
    ['r119', '*', 'r118', 'r118'],
    ['r120', '*', 'r119', 'C'],
    ['r121', '*', 16, 'r120'],
    ['r122', '*', 'q', 'r90'],
    ['r123', '-', 'B', 'r122'],
    ['r124', '*', 'C', 'kY'],
    ['r125', '*', 'r124', 'X'],
    ['r126', '*', 'r125', 'r93'],
    ['r127', '*', 'r94', 'r95'],
    ['r128', '*', -2, 'r127'],
    ['r129', '*', 4, 'r94'],
    ['r130', '-', 'r129', 'r100'],
    ['r131', '*', 'R', 'r130'],
    ['r132', '*', 'T', 'r94'],
    ['r133', '*', 'r132', 'r96'],
    ['r134', '*', 2, 'r133'],
    ['r135', '-', 'r131', 'r134'],
    ['r136', '*', 'f2', 'r135'],
    ['r137', '+', 'r128', 'r136'],
    ['r138', '*', 'r123', 'r137'],
    ['r139', '+', 'r126', 'r138'],
    ['r140', '*', 'r118', 'r94'],
    ['r141', '*', 2, 'r90'],
    ['r142', '-', 'r141', 'C'],
    ['r143', '*', 'r92', 'r142'],
    ['r144', '*', 'r140', 'r143'],
    ['r145', '+', 'r139', 'r144'],
    ['r146', '*', 2, 'r145'],
    ['r147', '+', 'r117', 'r146'],
    ['r148', '*', 'r121', 'r147'],
    ['r149', '*', 4, 'gamma'],
    ['r150', '-', 'k', 'r149'],
    ['r151', '*', 8, 'gamma'],
    ['r152', '*', 'r151', 'Pminus1'],
    ['r153', '-', 'N1', 1],
    ['r154', '*', 'kY', 'r153'],
    ['r155', '+', 'r152', 'r154'],
    ['r156', '*', 8, 'qm'],
    ['r157', '*', 'r156', 'f2'],
    ['r158', '*', 'qm', 'r90'],
    ['r159', '+', 'r158', 'C'],
    ['r160', '*', 'r90', 'r159'],
    ['r161', '*', 'r114', 'r160'],
    ['r162', '*', 'r119', 'r161'],
    ['r163', '*', 'r157', 'r162'],
    ['r164', '+', 'coeff', 'r148'],
    ['r165', '*', 'r164', 'Pminus1'],
    ['r166', '-', 'Na', 'r165'],
    ['r167', '*', 'r150', 'r166'],
    ['r168', '*', 'r163', 'r155'],
    ['r169', '-', 'r167', 'r168'],
    ['r170', '*', 'N0', 'N1'],
    ['r171', '-', 'r170', 1],
    ['r172', '-', 'Z', 1],
    ['r173', '-', 'r169', 'r150'],
    ['outPQ', '*', 'r171', 'r171'],
    ['outZ', '*', 'r172', 'r172'],
    ['outU', '*', 'r173', 'r173'],
    ['outSum', '+', 'outPQ', 'outZ'],
    ['polynomial', '+', 'outSum', 'outU'],
]


def expected_graph(parent):
    require(parent['source'][87]==['Pminus1','-','N0',1],'Exact88-row prefix')
    out=deepcopy(parent)
    out.update(name='thirteen_positive2011_scaled_syzygy178_degree86',operations=178,
      operation_counts={'*':117,'+':29,'-':32},exact_degree=86,
      arithmetic_proof='../../Lean/DiophantineConsistency/ThirteenScaledNormSyzygy86.lean',
      arithmetic_proof_sha256=LEAN_SHA,parent_polynomial='../thirteen-second-first-norm-corrections/polynomial88.json',
      parent_polynomial_sha256=PARENT_SHA,zero_set_proof='PROOF.md',zero_set_proof_sha256=ZERO_SET_PROOF_SHA,
      proof_boundary='Whole positive zero set unchanged with identity witnesses; scale positivity follows from Q=1 before cancellation. External actual ConZFC only, no HA/PA/ZFC internal or optimality claim.')
    out.pop('lean_variant_boolean',None)
    out['source']=deepcopy(parent['source'][:88])+deepcopy(EXTRA)
    out['display_scalar_names']={k:v for k,v in out['display_scalar_names'].items() if k!='correctedU'}
    out['display_scalar_names'].update(coeff='A88',r90='Gc',r148='Bcorr',r150='A',r155='S',r163='Hcorr',r169='Uc')
    return out


def check_graph(graph,parent):
    require(graph==expected_graph(parent),'Entire literal graph and metadata')
    require(graph['witnesses']==VARIABLES and graph['fixed_numerals']==PORTS,'Actual13+4 coordinates')
    known=set(SYMBOLS);gates={}
    for n,op,l,r in graph['source']:
        require(type(n)is str and n not in known and op in ('+','-','*'),'Unique paid gate')
        require(all(type(x)is int or type(x)is str and x in known for x in (l,r)),'Integer leaf/topology')
        known.add(n);gates[n]=(op,l,r)
    counts=dict(Counter(r[1] for r in graph['source']))
    require(len(gates)==178 and counts=={'*':117,'+':29,'-':32},'Exact paid count')
    live=set()
    def visit(x):
        if type(x)is int or x in live:return
        live.add(x)
        if x in gates:visit(gates[x][1]);visit(gates[x][2])
    visit('polynomial');require(live==known,'All178 gates,13 unknowns,4 ports live')
    require(all(n in gates for n in graph['display_scalar_names']),'All aliases live')
    return {'operations':counts,'live_gates':178,'live_unknowns':13,'live_ports':4,'unchanged_parent_prefix':88}


def check_formula(graph):
    # Independent exact compact coefficient formula over12 algebraic cuts.
    names=['qm','T','B','f2','C','R','X','kY','q','eta','r90','r92']
    b,T,G,F2,C,R,X,K,q,eta,Gc,g=[symbol(n)for n in VARIABLES[:12]]
    cuts1=dict(zip(names,[b,T,G,F2,C,R,X,K,q,eta,Gc,g]));get=evaluator(graph,cuts1)
    u=mul(X,R);v=mul(T,K);e=add(u,v,-1);h=add(G,mul(q,Gc),-1)
    L1=add(add(product([(C,1),(e,1),(add(product([(X,1),(v,1)],2),mul(F2,add(product([(u,1)],3),v,-1))),1)]),
                product([(F2,1),(T,2),(C,1),(X,1),(add(product([(K,1),(X,1),(eta,1)]),power(g,2)),1)],2)),
                product([(F2,1),(Gc,1),(v,2)],4),-1)
    inner=add(product([(v,1),(e,1)],-2),mul(F2,add(mul(R,add(product([(v,1)],4),product([(u,1)],3),-1)),product([(T,1),(v,1),(X,1),(eta,1)],2),-1)))
    L2=add(add(product([(C,1),(K,1),(X,1),(u,1)]),mul(h,inner)),product([(F2,1),(T,1),(v,1),(g,1),(add(product([(Gc,1)],2),C,-1),1)]))
    bc=product([(F2,2),(T,2),(C,1),(add(L1,product([(L2,1)],2)),1)],16)
    hc=product([(b,1),(F2,3),(T,2),(v,2),(Gc,1),(add(mul(b,Gc),C),1)],8)
    require(get('r148')==bc and get('r163')==hc,'Entire compact coefficient identities')
    # These separate small checks bind the two cut definitions exactly.
    get0=evaluator(graph,dict(zip(['K0','C','F','k','s','q2'],map(symbol,VARIABLES[:6]))))
    a,c,f,k,s,q2=map(symbol,VARIABLES[:6])
    require(get0('r90')==add(mul(a,c),f,-1) and get0('r92')==product([(k,1),(s,1),(q2,1)]),'Gc and g exact cuts')
    names2=['N0','N1','Na','Z','coeff','r148','r163','k','kY','gamma']
    P,Q,U,Z,A0,BC,HC,k,K,gamma=map(symbol,VARIABLES[:10])
    cuts=dict(zip(names2,[P,Q,U,Z,A0,BC,HC,k,K,gamma]));get2=evaluator(graph,cuts)
    A=add(k,product([(gamma,1)],4),-1);pm=add(P,const(1),-1)
    S=add(product([(gamma,1),(pm,1)],8),mul(K,add(Q,const(1),-1)))
    uc=add(mul(A,add(U,mul(add(A0,BC),pm),-1)),mul(HC,S),-1)
    expected=add(add(power(add(mul(P,Q),const(1),-1),2),power(add(Z,const(1),-1),2)),power(add(uc,A,-1),2))
    require(get2('r150')==A and get2('r155')==S and get2('r169')==uc and get2('polynomial')==expected,'Complete scaled residual formula')
    controls=[]
    for name,gate,index,replacement in [
      ('wrong_scale','r149',2,5),('wrong_syzygy','r151',2,7),('wrong_main_unit','r153',3,2),
      ('wrong_first_unit','Pminus1',3,2),('wrong_coefficient','r121',2,15),
      ('missing_second_bracket','r146',2,0),('wrong_scale_target','r173',3,1),
      ('added_auxiliary_correction','r169',1,'+'),('wrong_P','Pminus1',2,'N1')]:
        bad=deepcopy(graph);row=next(r for r in bad['source']if r[0]==gate);row[index]=replacement
        # Each mutation is checked in the earliest exact stage that contains it.
        if gate in ('r121','r146'):different=evaluator(bad,cuts1)('r148')!=bc
        else:different=evaluator(bad,cuts)('polynomial')!=expected
        require(different,'Algebraic corruption rejected '+name);controls.append(name)
    return {'coefficient_cuts':dict(zip(names,VARIABLES[:12])),
      'coefficient_B':rows(bc),'coefficient_H':rows(hc),'residual_cuts':dict(zip(names2,VARIABLES[:10])),
      'complete_residual_formula':rows(expected),'algebraic_corruptions':controls,
      'scope':'Complete staged polynomial identities bind every new literal gate to the Lean definitions; the positive-zero claim is proved separately in Lean.'}


def check_degree(graph):
    full=evaluator(graph);P=full('N0');Q=full('N1');S=full('r155')
    require(degree(P)==22 and degree(Q)==18 and degree(S)==21,'Complete norm and syzygy degrees')
    B=mul(symbol('beta'),symbol('J'));k=add(symbol('eta'),symbol('zeta'))
    sexpected=product([(B,13),(k,2),(symbol('s'),4),(symbol('w'),1),(add(k,product([(symbol('gamma'),1)],4),-1),1)],-4)
    require(leading(S)==sexpected,'Independent complete S21 factorization')
    layers={n:(1 if n in VARIABLES else 0,symbol(n))for n in SYMBOLS}
    leaders={};gate_records={};store={};cancellations=[];width=7
    for name,op,l,r in graph['source']:
        if name in ('outPQ','outZ','outU','outSum','polynomial'):
            da,a=degree(leaders[l]),leaders[l];db,b=degree(leaders[r]),leaders[r]
            if op=='*':result=mul(a,b);bound=da+db
            else:
                bound=max(da,db);result=add(a if da==bound else {},b if db==bound else {})
            require(result and degree(result)==bound,'Exact final residual branch leader')
        else:
            da,a=(0,const(l))if type(l)is int else layers[l];db,b=(0,const(r))if type(r)is int else layers[r]
            bound=da+db if op=='*'else max(da,db)
            if op=='*':
                result={}
                for ma,ca in a.items():
                    for mb,cb in b.items():
                        if sum(ma[:13])+sum(mb[:13])<bound-width:continue
                        mm=tuple(x+y for x,y in zip(ma,mb));result[mm]=result.get(mm,0)+ca*cb
                result={m:c for m,c in result.items()if c}
            else:result=add(a,b,1 if op=='+'else-1)
            result={m:c for m,c in result.items()if sum(m[:13])>=bound-width}
            if name in ('N0','N1','r155'):
                whole={'N0':P,'N1':Q,'r155':S}[name];newbound=degree(whole)
                if newbound!=bound:cancellations.append({'gate':name,'old_bound':bound,'sharp_bound':newbound,'full_expansion':True})
                bound=newbound;result={m:c for m,c in whole.items()if sum(m[:13])>=bound-width}
            require(result and degree(result)>=bound-width,'Every gate leader remains in exact retained window '+name)
            layers[name]=(bound,result)
        actual=degree(result);leader=leading(result);leaders[name]=leader
        if actual<bound:cancellations.append({'gate':name,'propagated_bound':bound,'actual_degree':actual,'retained_floor':bound-width})
        raw=rows(leader);digest=sha(encoded(raw));store.setdefault(digest,raw)
        gate_records[name]={'degree':actual,'terms':len(leader),'complete_leader_sha256':digest}
    aux=leaders['r169'];expected=power(aux,2)
    require(degree(aux)==43 and degree(expected)==86 and leaders['polynomial']==expected,'Full output homogeneous polynomial is complete auxiliary43 squared')
    require(gate_records['outPQ']['degree']==80 and gate_records['outZ']['degree']==72,'Both other exact branch degrees')
    # The proposal used k=eta+zeta. Select its eta^2 monomial after expanding.
    chosen={'J':27,'beta':27,'f':6,'T':1,'s':3,'w':4,'eta':2}
    key=tuple(chosen.get(n,0)for n in SYMBOLS)
    require(aux.get(key)==64 and [(m,c)for m,c in aux.items()if m[:13]==key[:13]]==[(key,64)],'Actual auxiliary coefficient64beta27')
    key2=tuple(2*x for x in key)
    require(expected.get(key2)==4096 and [(m,c)for m,c in expected.items()if m[:13]==key2[:13]]==[(key2,4096)],'Actual output coefficient4096beta54')
    return {'exact_degree':86,'all_gate_leaders':gate_records,'complete_leaders':store,
      'auxiliary_leader_sha256':gate_records['r169']['complete_leader_sha256'],
      'output_leader_sha256':gate_records['polynomial']['complete_leader_sha256'],
      'auxiliary_terms':len(aux),'output_terms':len(expected),'cancellations':cancellations,
      'complete_norm_terms':{'P':len(P),'Q':len(Q),'S':len(S)},'selected_unknown_monomial':chosen,
      'selected_auxiliary_coefficient':'64*beta^27','selected_output_coefficient':'4096*beta^54',
      'method':'Eight highest layers at unsharpened propagated bounds, except three fully expanded norms. Exact top leaders suffice for the five final residual-square gates. Full unique leaders are stored once by hash; no full polynomial expansion is claimed.'}


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
            'selected_actual_leader_coefficient_magnitude':record(4096*beta**54),
            'selected_actual_leader_coefficient_sign':1,'MF_shifted_exactly_once':True,
            'actual_polynomial_dependence':dependence_witnesses(graph,values)}



def check_actual_gate_degrees(degrees,ports):
    # A nonzero coefficient modulo this integer certifies that the complete
    # homogeneous leader survives specialization to the actual full ports.
    # This is exact nonvanishing, not a random identity or zero-set test.
    modulus=ports['actual_polynomial_dependence']['modulus']
    fixed=ports['actual_polynomial_dependence']['whole_port_residues']
    witnesses={}
    for digest,terms in degrees['complete_leaders'].items():
        coefficients={}
        for monomial,c in terms:
            value=c
            for alias,e in zip(PORTS,monomial[13:]):
                value=value*pow(fixed[alias],e,modulus)%modulus
            key=tuple(monomial[:13])
            coefficients[key]=(coefficients.get(key,0)+value)%modulus
        nonzero=sorted((m,c)for m,c in coefficients.items()if c)
        require(nonzero,'Complete homogeneous leader survives actual ports '+digest)
        key,c=nonzero[0]
        witnesses[digest]={'unknown_monomial':list(key),'coefficient_modulus':c}
    for gate,r in degrees['all_gate_leaders'].items():
        require(sum(witnesses[r['complete_leader_sha256']]['unknown_monomial'])==r['degree'],
                'Actual exact gate degree '+gate)
    return {'modulus':modulus,'whole_port_residues':fixed,'all_178_actual_gate_degrees_verified':True,
      'nonzero_leader_coefficients':witnesses,
      'scope':'Nonzero modular specialization proves each stored complete leader is nonzero at the exact current ports; no whole-polynomial or positive-zero identity follows from evaluation.'}


def negative_controls(graph,parent):
    failures=[]
    for name in ('wrong_scale','wrong_syzygy','wrong_target','wrong_port','rational_leaf','extra_variable','dead_gate','missing_correction'):
        bad=deepcopy(graph);gates={r[0]:r for r in bad['source']}
        if name=='wrong_scale':gates['r149'][2]=5
        elif name=='wrong_syzygy':gates['r151'][2]=7
        elif name=='wrong_target':gates['r173'][3]=1
        elif name=='wrong_port':bad['coefficient_binding']['ports']['MF']['bits']-=1
        elif name=='rational_leaf':gates['r121'][2]=16.0
        elif name=='extra_variable':bad['witnesses'].append('unused')
        elif name=='dead_gate':bad['source'].append(['dead','+','f',1])
        else:gates['outU'][2]=gates['outU'][3]='Na'
        try:check_graph(bad,parent)
        except ValueError as error:failures.append({'mutation':name,'rejected_by':str(error)})
        else:raise ValueError('Corruption accepted: '+name)
    return failures


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--write',action='store_true');args=parser.parse_args()
    require(shutil.disk_usage(HERE).free>512*1024**2,'512MiB reserve before audit')
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenSecondFirstNormCorrections.lean',PARENT_LEAN_SHA)
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenScaledNormSyzygy86.lean',LEAN_SHA)
    pinned(ROOT/'Lean/DiophantineConsistency/ThirteenScaledNormSyzygy86Checks.lean',CHECKS_SHA)
    pinned(HERE/'PROOF.md',ZERO_SET_PROOF_SHA)
    parent=json.loads(pinned(PARENT/'polynomial88.json',PARENT_SHA));pinned(PARENT/'CERTIFICATE.json',PARENT_CERT_SHA)
    graph=expected_graph(parent);raw=encoded(graph)
    if args.write:
        (HERE/'coefficients').mkdir(exist_ok=True)
        for e in graph['coefficient_binding']['ports'].values():
            (HERE/'coefficients'/e['file']).write_bytes(pinned(PARENT/'coefficients'/e['file'],e['gzip_sha256']))
        (HERE/'polynomial.json').write_bytes(raw)
    else:require((HERE/'polynomial.json').read_bytes()==raw,'Whole graph bytes')
    report={'schema':'thirteen_scaled_norm_syzygy178_degree86_v1','auditor_sha256':sha(Path(__file__).read_bytes()),
      'parent_graph_sha256':PARENT_SHA,'parent_lean_sha256':PARENT_LEAN_SHA,'lean_sha256':LEAN_SHA,
      'checks_sha256':CHECKS_SHA,'proof_sha256':ZERO_SET_PROOF_SHA,'graph_sha256':sha(raw),
      'graph':check_graph(graph,parent),'formula':check_formula(graph),'degree':check_degree(graph),
      'ports':check_ports(graph),'negative_controls':negative_controls(graph,parent),
      'scope':'Exact entire paid graph/staged formulas/all complete gate leaders/current full integer ports. Same positive zero sets and external ConZFC are proved separately in the pinned Lean leaf. No internal HA/PA/ZFC claim.'}
    report['actual_gate_degrees']=check_actual_gate_degrees(report['degree'],report['ports'])
    # A modular positive assignment certifies nonidentity with the parent.
    def mod_eval(g):
        mod=1000003;inputs={n:1 for n in VARIABLES}
        for alias,e in g['coefficient_binding']['ports'].items():
            inputs[alias]=int.from_bytes(gzip.decompress((HERE/'coefficients'/e['file']).read_bytes()),'big')%mod
        for name,op,l,r in g['source']:
            a=l if type(l)is int else inputs[l];b=r if type(r)is int else inputs[r]
            inputs[name]=(a*b if op=='*'else a+b if op=='+'else a-b)%mod
        return inputs['polynomial']
    old,new=mod_eval(parent),mod_eval(graph);require(old!=new,'Actual positive nonidentity witness')
    report['nonidentity']={'modulus':1000003,'all_unknowns':1,'parent':old,'new':new}
    # Compact JSON avoids duplicating a large human-formatted monomial array.
    data=(json.dumps(report,sort_keys=True,separators=(',',':'))+'\n').encode()
    require(len(data)<48*1024**2,'48MiB maximum certificate')
    if args.write:
        require(shutil.disk_usage(HERE).free-len(data)>512*1024**2,'512MiB reserve after writing certificate')
        (HERE/'CERTIFICATE.json').write_bytes(data)
    else:require((HERE/'CERTIFICATE.json').read_bytes()==data,'Exact deterministic certificate')
    print(json.dumps({'status':'PASS','variables':13,'operations':178,'degree':86,'raw_port_bytes':47313,
      'auxiliary_terms':report['degree']['auxiliary_terms'],'leader_terms':report['degree']['output_terms'],
      'certificate_bytes':len(data),'certificate_sha256':sha(data)},sort_keys=True))


if __name__=='__main__':main()
