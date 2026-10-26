#!/usr/bin/env python3
"""Independent complete current2011 fourteen-variable normalized67/106 audit.
No project code is imported. --write changes only this new packet; normal/-O
recompute and compare every deterministic artifact with explicit guards.
"""
import argparse
from collections import Counter
from copy import deepcopy
import gzip
import hashlib
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'research/fourteen-nonzero-spheres'
PARENT_SHA='937752350556a94539584db8f646ff9e02d25a7113e6d4af70ac22c1b1e01ad2'
SCALED=ROOT/'research/scaled-auxiliary118/polynomial.json'
SCALED_SHA='588f295e6d965ff5f7b78deda02b808575aaf818908af528a738a98ecda5c72f'
LEAN_SHA='efaa7ff2df3751b00cae602aaf17c6e3140c568c6bee956fa7a28fda6596e46f'
CHECKS_SHA='e269c855713dbb0badc9b11f276a9cdb5b068f6ea364d2b401f2122f6ee7b0c6'
ORDINARY_SHA='751910f2c2c24681fab32413e43c70f51e4157fb68bf3fd1cd6a06198b899883'
SCALED_LEAN_SHA='2e222efd3b40626e6734fe30e5b7239fb7a7abd5fd9c14bee8e4a238c237c620'
NATIVE=ROOT/'research/padding-staircase-independent'
PROOF_SHA='69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8'
CERT_SHA='fae49c56a9c57d394335c8a47da395f000a0c25cb8267d1330104eddbbc7850f'
ARRAY_SHA='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93'
VARIABLES=['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma']
PORTS=['beta','K0','MC','MF']
SYMBOLS=VARIABLES+PORTS
ZERO=(0,)*len(SYMBOLS)

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


def check_degree(graph):
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
    expected=product([(gamma,1),(i,2),(w,8),(s,17),(k0,9),(q0,59),(f,6),(t,2),(factors['Nt'],1)],8)
    chosen={'J':60,'beta':60,'eta':9,'gamma':1,'i':2,'w':9,'s':17,'f':6,'T':2}
    require(leaders['polynomial']==expected and degree(expected)==106 and len(expected)==40,
            'Complete forty-term degree106 leader')
    require(expected.get(tuple(chosen.get(n,0) for n in SYMBOLS))==8,'Selected8*beta^60 coefficient')
    return {'exact_degree':106,'symbols':SYMBOLS,'main_norm_terms':len(main),
        'main_norm_sha256':sha(encoded(rows(main))),'cancellations':cancellations,
        'complete_factor_leaders':{n:rows(v) for n,v in factors.items()},
        'complete_leader':rows(expected),'selected_coefficient_factor':8,'selected_beta_exponent':60,
        'selected_unknown_monomial':{n:e for n,e in chosen.items() if n in VARIABLES},
        'all_gate_leaders':{n:{'degree':degree(leaders[n]),'terms':len(leaders[n]),
            'sha256':sha(encoded(rows(leaders[n]))),'complete_leader':rows(leaders[n])}
            for n,_,_,_ in graph['source']}}

TAIL=[['product0','*','N0','N1'],['product1','*','product0','U'],
      ['product2','*','product1','Nt'],['product3','*','product2','Z'],
      ['polynomial','-','product3',1]]
COUNTS={'*':38,'+':16,'-':13}


def expected_graph(parent):
    require(len(parent['source'])==71 and parent['source'][61]==['U','+','auxiliary','y2'],
            'Pinned complete common prefix boundary')
    graph=deepcopy(parent)
    graph.update(name='fourteen_current2011_normalized_product67_degree106',operations=67,
        operation_counts=COUNTS,exact_degree=106,
        arithmetic_proof='../../Lean/DiophantineConsistency/CarrierNormalizedProduct106.lean',
        arithmetic_proof_sha256=LEAN_SHA,proof='PROOF.md',zero_set_proof_sha256=ORDINARY_SHA,
        parent_polynomial='../fourteen-nonzero-spheres/polynomial71.json',parent_polynomial_sha256=PARENT_SHA,
        proof_boundary='Complete current2011 normalized product, identical entire positive zero set via nonzero-delta cancellation; external Lean ConZFC endpoint, no internal HA/ZFC claim or global minimum.')
    graph['source']=deepcopy(parent['source'][:62]+TAIL)
    return graph


def check_graph(graph,parent):
    require(graph==expected_graph(parent),'Entire expected graph and metadata')
    require(graph['witnesses']==VARIABLES and graph['fixed_numerals']==PORTS,'Exact14+4 leaves')
    known=set(SYMBOLS);gates={}
    for name,op,l,r in graph['source']:
        require(type(name) is str and name not in known and op in ('+','-','*'),'Unique legal gate')
        require(all(type(x) is int or type(x) is str and x in known for x in (l,r)),
                'Integer leaves and topological inputs')
        gates[name]=(op,l,r);known.add(name)
    live=set()
    def visit(n):
        if type(n) is int or n in live:return
        live.add(n)
        if n in gates:visit(gates[n][1]);visit(gates[n][2])
    visit('polynomial')
    require(live==known and len(gates)==67,'All67 producers and14+4 leaves live')
    require(Counter(r[1] for r in graph['source'])==COUNTS,'All paid binary operations')
    require(Counter(r[1] for r in graph['source'][:62])=={'*':34,'+':16,'-':12},'Common62 ledger')
    require(all(n in known for n in graph['display_scalar_names']),'Live aliases')
    return {'operations':COUNTS,'live_gates':67,'live_variables':14,'live_ports':4,
            'unchanged_prefix':62,'removed_sphere_tail':parent['source'][62:],'replacement_tail':TAIL}


def check_identity(graph,scaled):
    P,Q,W,D,F,S,V,Y=[symbol(n) for n in VARIABLES[:8]]
    cuts=dict(zip(['N0','N1','Nt','Delta','f2','strong_term','V2','y2'],[P,Q,W,D,F,S,V,Y]))
    U=add(mul(mul(D,add(F,const(1),-1)),add(V,Y,-1)),Y)
    Z=add(F,S,-1)
    expected=add(product([(P,1),(Q,1),(U,1),(W,1),(Z,1)]),const(1),-1)
    actual=evaluator(graph,cuts)('polynomial')
    require(actual==expected,'Every new row binds independent normalized formula')
    scuts={k:v for k,v in cuts.items() if k!='strong_term'}
    scuts['normalized_S2']=mul(D,S)
    old=evaluator(scaled,scuts)('polynomial')
    require(old==mul(D,actual),'Complete scaled66 graph equals delta times complete67 graph')
    require(scaled['source'][:51]==graph['source'][:51], 'All51 original arithmetic rows agree')
    require(actual!=old,'Normalization is not equality to the scaled polynomial')
    rejected=[]
    for name in ('wrong_constant','omitted_W','omitted_Z','old_scaled_Z','missing_i_square','wrong_theta'):
        bad=deepcopy(graph);g={r[0]:r for r in bad['source']}
        if name=='wrong_constant':g['polynomial'][3]=2
        elif name=='omitted_W':g['product2'][3]=1
        elif name=='omitted_Z':g['product3'][3]=1
        elif name=='old_scaled_Z':g['product3'][3]='Delta'
        elif name=='missing_i_square':g['strong_term'][2]='i2'
        else:g['Theta'][3]='f2'
        # The missing-i mutation lies below the abstract strong cut, so remove
        # that cut and compare against the same uncut genuine expression.
        usecuts=cuts
        if name=='missing_i_square':
            usecuts={k:v for k,v in cuts.items() if k!='strong_term'}
            usecuts.update(i=symbol('w'),Dc2=symbol('n'),c2=symbol('eta'))
        require(evaluator(bad,usecuts)('polynomial')!=evaluator(graph,usecuts)('polynomial'),
                'Full formula detects '+name)
        rejected.append(name)
    return {'cut_symbols':dict(zip(cuts,VARIABLES[:8])),'full_new_cut_polynomial':rows(actual),
            'full_scaled_cut_polynomial':rows(old),'identity':'scaled66=Delta*normalized67',
            'mutations':rejected,'scope':'Ring identity; positive zero-set equivalence additionally uses the separately proved delta>0.'}


def negative_controls(graph,parent):
    rejected=[]
    for name in ('wrong_degree','wrong_count','wrong_port','rational_leaf','extra_variable','dead_gate'):
        bad=deepcopy(graph)
        if name=='wrong_degree':bad['exact_degree']=105
        elif name=='wrong_count':bad['operations']=66
        elif name=='wrong_port':bad['coefficient_binding']['ports']['MF']['bits']-=1
        elif name=='rational_leaf':bad['source'][-1][3]=1.0
        elif name=='extra_variable':bad['witnesses'].append('unused')
        else:bad['source'].append(['unused','+',1,1])
        try:check_graph(bad,parent)
        except ValueError as error:rejected.append({'mutation':name,'rejected_by':str(error)})
        else:raise ValueError('Corruption accepted '+name)
    return rejected


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    for name,digest in [('CarrierNormalizedProduct106',LEAN_SHA),('CarrierNormalizedProduct106Checks',CHECKS_SHA),
                        ('CarrierScaledAuxiliary118',SCALED_LEAN_SHA)]:
        pinned(ROOT/'Lean/DiophantineConsistency'/f'{name}.lean',digest)
    pinned(HERE/'PROOF.md',ORDINARY_SHA)
    parent=json.loads(pinned(PARENT/'polynomial71.json',PARENT_SHA))
    scaled=json.loads(pinned(SCALED,SCALED_SHA))
    graph=expected_graph(parent);data=encoded(graph)
    if args.write:
        (HERE/'coefficients').mkdir(exist_ok=True)
        for e in graph['coefficient_binding']['ports'].values():
            (HERE/'coefficients'/e['file']).write_bytes(pinned(PARENT/'coefficients'/e['file'],e['gzip_sha256']))
        (HERE/'polynomial.json').write_bytes(data)
    else:require((HERE/'polynomial.json').read_bytes()==data,'Exact deterministic graph bytes')
    g=check_graph(graph,parent);values,ports=check_ports(graph);d=check_degree(graph)
    d['actual_selected_coefficient']=record(8*values['beta']**60)
    out={'schema':'fourteen_current2011_normalized_product67_106_v1','audit_sha256':sha(Path(__file__).read_bytes()),
         'parent_graph_sha256':PARENT_SHA,'formal_scaled_graph_sha256':SCALED_SHA,
         'formal_scaled_metadata_adopted':False,'lean_sha256':LEAN_SHA,'checks_sha256':CHECKS_SHA,
         'ordinary_proof_sha256':ORDINARY_SHA,'scaled_lean_sha256':SCALED_LEAN_SHA,
         'graph_sha256':sha(data),'graph':g,'degree':d,'whole_identity':check_identity(graph,scaled),
         'ports':ports,'negative_controls':negative_controls(graph,parent),
         'actual_dependence':dependence_witnesses(graph,values),
         'scope':'Complete67-operation graph, degree106 and exactcurrent2011 tuple; ring identity separate from Lean wholepositivezero maps. No internal HA/ZFC or minimum claim.'}
    receipt=encoded(out)
    if args.write:(HERE/'CERTIFICATE.json').write_bytes(receipt)
    else:require((HERE/'CERTIFICATE.json').read_bytes()==receipt,'Exact deterministic receipt bytes')
    print(json.dumps({'status':'PASS','variables':14,'operations':67,'degree':106,
                      'raw_port_bytes':47313,'certificate_sha256':sha(receipt)},sort_keys=True))


if __name__=='__main__':main()
