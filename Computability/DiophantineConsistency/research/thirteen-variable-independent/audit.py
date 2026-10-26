#!/usr/bin/env python3
"""Audit both complete13-positive integer DAGs at the authenticated2471 ports."""
import argparse
from collections import Counter
from copy import deepcopy
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PROOF_SHA = 'd2e40a04fdc670a5f5a05d2c8e7e762e07ef559eb051e5ff6f5c82e7e3e8f6a8'
PARENT = ROOT / 'candidates/one-page-phase-split-carrier65-2471/polynomial.json'
PARENT_SHA = '4814aa91ee692e68b82a55debbf29bda8f136cf51482fbf4ef84dc012670d421'
SOURCE = ROOT / 'con-zfc-diophantine-forms/192-pell-centers-fused-bounds/compact13'
SOURCE_SHA = '9574f3db6cfc549d565d278f84d7d9f0a53fec92cdcc05762c95d1e54db49c7c'
SOURCE_PROOF_SHA = '5d210d457196c40bec061ecd79b86eeb1aeabb46a3d5e037d88bc34773fba07f'
CARRIER_SHA = '53ec75050c7f4a00386d9738f8c515f3a816d8e4d94afcebb54b3497d972e749'
NATIVE_SHA = '934c7984038b578a68b1396fffdb8db71a9039b01a86455a74c8639264a1b966'
CERT_SHA = 'f6c576194bfd60d10457c6ba9c43c0b7a8537639588c4f022e7a0362b9051bef'
ARRAY_SHA = '43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93'
VARIABLES = ['J','F','alpha','f','i','T','s','w','n','eta','zeta','m','gamma']
PORTS = ['beta','K0','MC','MF']
SYMBOLS = VARIABLES + PORTS
ZERO = (0,)*len(SYMBOLS)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def encoded(value):
    return (json.dumps(value,indent=2,sort_keys=True)+'\n').encode()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def pinned(path, digest):
    raw=path.read_bytes()
    require(sha(raw)==digest,'Pinned input differs: '+str(path))
    return raw


def add(a,b,sign=1):
    out=dict(a)
    for m,c in b.items():
        out[m]=out.get(m,0)+sign*c
        if out[m]==0:
            del out[m]
    return out


def mul(a,b):
    out={}
    for ma,ca in a.items():
        for mb,cb in b.items():
            m=tuple(x+y for x,y in zip(ma,mb))
            out[m]=out.get(m,0)+ca*cb
    return {m:c for m,c in out.items() if c}


def power(a,n):
    out={ZERO:1}
    for _ in range(n):
        out=mul(out,a)
    return out


def symbol(name):
    m=list(ZERO);m[SYMBOLS.index(name)]=1
    return {tuple(m):1}


def product(factors,coefficient=1):
    out={ZERO:coefficient}
    for a,n in factors:
        out=mul(out,power(a,n))
    return out


def degree(a):
    return max((sum(m[:len(VARIABLES)]) for m in a),default=-1)


def leading(a):
    d=degree(a)
    return {m:c for m,c in a.items() if sum(m[:len(VARIABLES)])==d}


def polynomial_rows(a):
    return [[list(m),c] for m,c in sorted(a.items())]


def carrier_rows(parent):
    """Explicitly derive every69 row from the accepted complete65 graph."""
    rows=[]
    deleted={'transport_partial','zqm','Nt','product3'}
    for row in parent['source']:
        name=row[0]
        if name in deleted:
            continue
        if name=='transport':
            rows.extend([list(row),['B','-','transport','F']])
        elif name=='normalized_S':
            rows.extend([['hi','*','qm','i'],['normalized_S','*','hi','Dc2']])
        elif name=='y2':
            rows.extend([['LB','*','V2','B'],['mLB','-','m','LB'],
                         ['h_mLB','*','qm','mLB'],['carrier','-','h_mLB','B'],
                         ['four_carrier','*',4,'carrier'],['y','+','four_carrier',1],list(row)])
        elif name=='product4':
            rows.append(['product4','*','product1','scaled_Ns'])
        else:
            rows.append(list(row))
    return rows


def expected_graph(parent,incoming,scaled):
    rows=carrier_rows(parent)
    require(rows==incoming['source'],'Every reconstructed69 row equals the authenticated inert source schedule')
    require(incoming['witnesses']==VARIABLES and incoming['fixed_numerals']==PORTS
            and incoming['operations']==69 and incoming['exact_degree']==174,
            'Inert source has the complete expected interface; its older ports are not imported')
    if scaled:
        new=[]
        for row in rows:
            if row[0]=='scaled_f2':
                continue
            if row[0]=='aux_product':
                new.extend([['scaled_f2','*','Delta','f2'],['Theta','-','scaled_f2','Delta'],
                            ['aux_product','*','Theta','V2minusY2']])
            else:
                new.append(row)
        rows=new
    binding=deepcopy(parent['coefficient_binding'])
    binding['path']='../../candidates/one-page-phase-split-carrier65-2471/coefficients/'
    return {'schema':'literal_integer_arithmetic_dag_v1',
            'name':'thirteen_positive2471_'+('scaled70_degree140' if scaled else 'carrier69_degree174'),
            'witness_domain':'strictly positive integers','witnesses':VARIABLES,
            'fixed_numerals':PORTS,'source':rows,'output':'polynomial',
            'operations':70 if scaled else 69,'operation_counts':{'*':39,'+':16,'-':15 if scaled else 14},
            'exact_degree':140 if scaled else 174,'coefficient_binding':binding,
            'proof':'PROOF.md','arithmetic_proof':'PROOF.md','arithmetic_proof_sha256':PROOF_SHA,
            'parent_polynomial':'../../candidates/one-page-phase-split-carrier65-2471/polynomial.json',
            'parent_polynomial_sha256':PARENT_SHA,
            'inert_source_graph':'../../con-zfc-diophantine-forms/192-pell-centers-fused-bounds/compact13/positive13_square.json',
            'inert_source_graph_sha256':SOURCE_SHA,
            'display_scalar_names':{'qm':'b','B':'G','main_root':'D','normalized_S':'S',
                                    'N0':'P','N1':'Q','Na':'U' if scaled else 'Uold','scaled_Ns':'Z'},
            'proof_boundary':'Complete thirteen-positive existence maps at the frozen2471 native tuple; scaled variant has identical thirteen-coordinate positive zero set. Retained syntactic and ordinary contracts; no new formal-kernel replay.'}


def check_graph(graph,parent,incoming,scaled):
    require(graph==expected_graph(parent,incoming,scaled),'Entire graph, metadata, interface and fixed-port binding')
    require(parent['operations']==65 and parent['exact_degree']==150,'Complete accepted65 parent')
    rows=graph['source'];count=70 if scaled else 69
    require(len(rows)==count and graph['witnesses']==VARIABLES and graph['fixed_numerals']==PORTS,
            'Entire literal13-positive interface and operation length')
    known=set(SYMBOLS);by_name={}
    for row in rows:
        require(type(row) is list and len(row)==4,'Every gate is binary')
        name,op,left,right=row
        require(type(name) is str and name not in known and op in ('+','-','*'),'Unique integer arithmetic producer')
        require(all(type(a) is int or type(a) is str and a in known for a in (left,right)),
                'Every operand is an integer leaf or preceding producer')
        known.add(name);by_name[name]=row
    counts=dict(sorted(Counter(row[1] for row in rows).items()))
    require(counts=={'*':39,'+':16,'-':15 if scaled else 14}==graph['operation_counts'],'Exact literal operation metric')
    live=set()
    def visit(name):
        if type(name) is int or name in live:return
        live.add(name)
        if name in by_name:
            visit(by_name[name][2]);visit(by_name[name][3])
    visit('polynomial')
    require(live==known,'Every gate, all13 variables and all four ports are live')
    parent_rows={row[0]:row for row in parent['source']}
    old69={row[0]:row for row in carrier_rows(parent)}
    removed=set(parent_rows)-set(old69);added=set(old69)-set(parent_rows)
    changed={n for n in set(parent_rows)&set(old69) if parent_rows[n]!=old69[n]}
    require(removed=={'transport_partial','zqm','Nt','product3'}
            and added=={'B','hi','LB','mLB','h_mLB','carrier','four_carrier','y'}
            and changed=={'normalized_S','product4'},'Exact complete65-to69 row difference')
    if scaled:
        require(set(by_name)-set(old69)=={'Theta'} and set(old69)<=set(by_name)
                and {n for n in old69 if old69[n]!=by_name[n]}=={'aux_product'},
                'Exact69-to70 change; every69 producer remains live')
    full_cache={name:symbol(name) for name in SYMBOLS}
    def full(name):
        if type(name) is int:return {ZERO:name} if name else {}
        if name not in full_cache:
            _,op,l,r=by_name[name];a,b=full(l),full(r)
            full_cache[name]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
        return full_cache[name]
    main=full('N1');u=add(full('X'),mul(symbol('gamma'),full('H')))
    main_identity=add(add(power(u,2),product([(full('a'),1),(full('c'),1),(u,1)],2)),
                      mul(full('H'),power(full('c'),2)),-1)
    require(main==main_identity and degree(main)==18,'Exact complete main-norm cancellation')
    leaders={name:symbol(name) for name in SYMBOLS};cancellations=[]
    for name,op,left,right in rows:
        a={ZERO:left} if type(left) is int else leaders[left]
        b={ZERO:right} if type(right) is int else leaders[right]
        if op=='*':result=mul(a,b)
        else:
            da,db=degree(a),degree(b)
            if da>db:result=a
            elif db>da:result=b if op=='+' else mul({ZERO:-1},b)
            else:result=add(a,b,1 if op=='+' else -1)
            if not result:
                cancellations.append(name);result=leading(full(name))
        leaders[name]=result
    require(cancellations==['N1'],'Every top-degree cancellation resolved by full expansion')
    q0=mul(symbol('beta'),symbol('J'));k0=add(symbol('eta'),symbol('zeta'))
    C0=add(add(q0,symbol('F'),-1),symbol('alpha'),-1)
    w,s,f,t,i,gamma=[symbol(n) for n in ('w','s','f','T','i','gamma')]
    y0=product([(q0,7),(k0,2),(s,2),(w,1),(f,4),(t,2),(C0,1)],-4)
    S0=product([(q0,15),(k0,2),(s,4),(w,2),(i,1)])
    require(leaders['B']==mul(w,C0) and leaders['y']==y0 and degree(y0)==19
            and leaders['normalized_S']==S0 and degree(S0)==24,'Entire new transport, signed-y and strong-seed leaders')
    U0=(product([(q0,22),(k0,4),(s,6),(w,4),(f,10),(t,4),(C0,2)],-16) if scaled
        else product([(q0,44),(k0,8),(s,12),(w,6),(f,8),(t,4),(C0,2),(i,2)],-16))
    if scaled:
        theta0=product([(w,2),(s,2),(q0,8),(f,2)])
        require(leaders['Theta']==theta0 and degree(theta0)==14,'Entire newTheta leader')
    factors={'N0':product([(w,2),(s,4),(k0,2),(q0,14)],-1),
             'N1':product([(gamma,1),(w,2),(s,3),(k0,1),(q0,11)],8),
             'Na':U0,'scaled_Ns':product([(i,2),(w,4),(s,8),(k0,4),(q0,30)],-1)}
    for name,value in factors.items():require(leaders[name]==value,'Complete factor leader '+name)
    degrees={n:degree(v) for n,v in factors.items()}
    require(list(degrees.values())==[22,18,52 if scaled else 86,48],'Every exact factor degree')
    expected=(product([(q0,77),(gamma,1),(i,2),(k0,11),(w,12),(s,21),(f,10),(t,4),(C0,2)],-128) if scaled
              else product([(q0,99),(gamma,1),(i,4),(k0,15),(w,14),(s,27),(f,8),(t,4),(C0,2)],-128))
    require(leaders['polynomial']==expected and degree(expected)==graph['exact_degree'],
            'Entire all-variable leading homogeneous polynomial and exact total degree')
    jexp=79 if scaled else 101
    chosen={'J':jexp,'beta':jexp,'gamma':1,'i':2 if scaled else 4,'eta':11 if scaled else 15,
            'w':12 if scaled else 14,'s':21 if scaled else 27,'f':10 if scaled else 8,'T':4}
    require(expected.get(tuple(chosen.get(n,0) for n in SYMBOLS))==-128,'Nonzero fixed-beta coefficient')
    return {'operations':counts,'live_gates':count,'live_positive_variables':13,'live_ports':4,
            'removed_parent_rows':sorted(removed),'added_carrier_rows':sorted(added),'changed_parent_rows':sorted(changed),
            'factor_degrees':degrees,'exact_degree':degree(expected),'leader_symbols':SYMBOLS,
            'complete_main_norm_terms':len(main),'main_norm_sha256':sha(encoded(polynomial_rows(main))),
            'signed_y_leader':polynomial_rows(y0),'strong_seed_leader':polynomial_rows(S0),
            'complete_factor_leaders':{n:polynomial_rows(v) for n,v in factors.items()},
            'complete_leader':polynomial_rows(expected),'complete_leader_terms':len(expected),
            'leader_sha256':sha(encoded(polynomial_rows(expected))),
            'selected_coefficient':'-128*beta^'+str(jexp),'accounted_cancellations':cancellations,
            'all_gate_leaders':{n:{'degree':degree(leaders[n]),'terms':len(leaders[n]),
                                  'sha256':sha(encoded(polynomial_rows(leaders[n])))} for n in by_name}}


def check_identities():
    # Independent cut variables: Delta,f,i,b,c,V,G,m,P,Q.
    delta,f,i,b,c,V,G,m,P,Q=[symbol(n) for n in ('J','F','alpha','f','i','T','s','w','n','eta')]
    S=product([(b,1),(i,1),(delta,1),(c,2)])
    y=add({ZERO:1},mul({ZERO:4},add(mul(b,add(m,mul(power(V,2),G),-1)),G,-1)))
    expanded_y=add(add({ZERO:1},product([(b,1),(m,1)],4)),
                   mul(add({ZERO:1},mul(b,power(V,2))),G),-4)
    require(y==expanded_y,'Exact signed carrier y=1+4bm-4(1+bV^2)G')
    S2=power(S,2);df2=mul(delta,power(f,2));Z=add(df2,S2,-1)
    zbar=add(power(f,2),product([(delta,1),(b,2),(i,2),(c,4)]),-1)
    require(Z==mul(delta,zbar),'Exact divisibility Z=Delta*[f^2-Delta*(bic^2)^2]')
    theta=add(df2,delta,-1);difference=add(power(V,2),power(y,2),-1)
    Uold=add(mul(S2,difference),power(y,2));U=add(mul(theta,difference),power(y,2))
    correction=mul(add(Z,delta,-1),difference)
    require(add(theta,S2,-1)==add(Z,delta,-1) and add(U,Uold,-1)==correction,
            'Complete scaled auxiliary polynomial identity with actual signed carrier')
    common=product([(P,1),(Q,1),(Z,1)])
    old=add(mul(common,Uold),delta,-1);new=add(mul(common,U),delta,-1)
    require(add(new,old,-1)==mul(common,correction),'Whole13-coordinate polynomial difference identity')
    require(add(add(mul(add(df2,delta),difference),power(y,2)),Uold,-1)!=correction,
            'Wrong-signTheta rejects exact identity')
    # The soundness witness sets z=G/b+1. Clearing b verifies native restoration.
    transport=add(mul(b,add(add(G,b),{ZERO:1})),mul(add(G,b),b),-1)
    require(transport==b,'Exact restored transport factor after clearing the witness quotient')
    residue_cases=0;residues=set()
    for a0 in range(4):
        d=((a0+2)**2-1)%4
        for f0 in range(4):
            for b0 in range(4):
                for i0 in range(4):
                    for c0 in range(4):
                        r=(f0*f0-d*(b0*i0*c0*c0)**2)%4
                        require(r!=3,'Strong quotient cannot be negative unit modulo4')
                        residues.add(r);residue_cases+=1
    # Verify the corrected recurrence bases as exact polynomials, not sampled A values.
    A=symbol('gamma');A2=power(A,2)
    q1=add(mul({ZERO:4},add({ZERO:1},A2,-1)),{ZERO:3},-1)
    signed_psi3=add({ZERO:1},mul({ZERO:4},A2),-1)
    coefficient=add(mul({ZERO:4},add({ZERO:1},A2,-1)),{ZERO:2},-1)
    require(q1==signed_psi3 and coefficient==add({ZERO:2},mul({ZERO:4},A2),-1),
            'Corrected exact Q1 and signed-odd-psi recurrence coefficient')
    require(q1!=add({ZERO:3},mul({ZERO:4},A2),-1),'Earlier3-4A^2 initialization is explicitly rejected')
    return {'identities':['y=1+4bm-4(1+bV^2)G','Z=Delta*Zbar','Theta-S^2=Z-Delta',
                          'U-Uold=(Z-Delta)*(V^2-y^2)','p-pold=P*Q*Z*(Z-Delta)*(V^2-y^2)',
                          'cleared_native_transport=b','Q1(1-A^2)=1-4A^2'],
            'mod4_cases':residue_cases,'quotient_residues':sorted(residues),
            'wrong_Theta_sign_negative':True,'wrong_recurrence_initialization_negative':True,
            'scope':'Exact cut-ring identities and finite residues. Unbounded Pell classification, positivity, witness divisibility and both existence maps belong to the pinned ordinary proof.'}


def port_record(value):
    require(type(value) is int and value>0,'Positive whole integer')
    raw=value.to_bytes((value.bit_length()+7)//8,'big')
    return {'bits':value.bit_length(),'bytes':len(raw),'sha256':sha(raw)}


def check_ports(graphs):
    folder=ROOT/'research/phase-split-independent'
    pinned(folder/'PROOF.md',NATIVE_SHA)
    cert=json.loads(pinned(folder/'certificate.json',CERT_SHA))
    c=json.loads(pinned(folder/'coefficients.json',ARRAY_SHA))
    require(len(c)==3297 and all(type(v) is int and v>=0 for v in c),'Entire coefficient array')
    rp=lambda e:1<<(47*e)
    G=lambda n:sum(rp(e) for e in range(n))
    beta=rp(2471)-1
    K=rp(18)+rp(1004)+rp(2480)+sum(v*rp(1462-e) for e,v in enumerate(c) if v)
    MC=beta-G(951)-rp(960)*G(26)-rp(1004)
    native=8*G(917)-4+((1<<45)-4)*rp(1462)+rp(960)*G(9)+rp(987)*G(8)+rp(1004)
    values={'beta':beta,'K':K,'MC':MC,'MF_source':beta+native}
    records={n:port_record(v) for n,v in values.items()}
    require(records==cert['constant_ports'] and beta>=31 and K>0 and 0<MC<beta<beta+native<2*beta,
            'All complete reconstructed certified2471 ports and scalar boxes')
    for graph in graphs:
        binding=graph['coefficient_binding']
        require((HERE/binding['ordinary_proof']).resolve()==(folder/'PROOF.md').resolve()
                and binding['ordinary_proof_sha256']==NATIVE_SHA
                and (HERE/binding['certificate']).resolve()==(folder/'certificate.json').resolve()
                and binding['certificate_sha256']==CERT_SHA,'All resolved proof/certificate bindings')
        for graph_name,native_name in {'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}.items():
            entry=binding['ports'][graph_name]
            raw=gzip.decompress(pinned(HERE/binding['path']/entry['file'],entry['gzip_sha256']))
            require(int.from_bytes(raw,'big')==values[native_name] and sha(raw)==entry['raw_sha256']
                    and len(raw)==entry['raw_bytes'] and values[native_name].bit_length()==entry['bits'],
                    'Every materialized whole integer leaf: '+graph_name)
        require(sum(v['bytes'] for v in records.values())==binding['raw_bytes']==58125,'Entire raw-port cost')
    require(port_record(MC+rp(1004))!=records['MC'],'Whole physical marker omission negative')
    return {'native_proof_sha256':NATIVE_SHA,'native_certificate_sha256':CERT_SHA,
            'complete_array_sha256':ARRAY_SHA,'ports':records,'raw_bytes':58125,'scalar_boxes':True,
            'selected_actual_coefficients':{str(e):{'sign':-1,'magnitude':port_record(128*beta**e)} for e in (101,79)},
            'marker_omission_negative':True,
            'scope':'Both graphs share all four complete accepted2471 integers. No old incoming port or finite zero search substitutes for the native theorem.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='write only deterministic CERTIFICATE.json')
    args=parser.parse_args()
    pinned(HERE/'PROOF.md',PROOF_SHA)
    pinned(ROOT/'research/carrier65-independent/PROOF.md',CARRIER_SHA)
    pinned(SOURCE/'PROOF.md',SOURCE_PROOF_SHA)
    incoming=json.loads(pinned(SOURCE/'positive13_square.json',SOURCE_SHA))
    parent=json.loads(pinned(PARENT,PARENT_SHA))
    checked={};graphs=[];digests={};negatives=[]
    for scaled,name in ((False,'polynomial69.json'),(True,'polynomial70.json')):
        raw=(HERE/name).read_bytes();graph=json.loads(raw)
        require(raw==encoded(expected_graph(parent,incoming,scaled)),'Canonical entire literal graph bytes: '+name)
        checked[name]=check_graph(graph,parent,incoming,scaled);graphs.append(graph);digests[name]=sha(raw)
        for mutation in ('missing_b','wrong_y_sign','rational_leaf','omitted_factor','extra_unknown','degree','port'):
            bad=deepcopy(graph);rows={r[0]:r for r in bad['source']}
            if mutation=='missing_b':rows['hi'][2]=1
            elif mutation=='wrong_y_sign':rows['carrier'][1]='+'
            elif mutation=='rational_leaf':rows['four_carrier'][2]=4.0
            elif mutation=='omitted_factor':rows['product4'][3]=1
            elif mutation=='extra_unknown':bad['witnesses'].append('unused')
            elif mutation=='degree':bad['exact_degree']-=1
            else:bad['coefficient_binding']['ports']['MC']['bits']-=1
            try:check_graph(bad,parent,incoming,scaled)
            except ValueError as error:negatives.append({'graph':name,'mutation':mutation,'rejected_by':str(error)})
            else:raise ValueError('Corrupt complete graph accepted: '+name+' '+mutation)
    data={'schema':'thirteen_positive2471_literal_pair_audit_v1','audit_sha256':sha(Path(__file__).read_bytes()),
          'ordinary_proof_sha256':PROOF_SHA,'parent_graph_sha256':PARENT_SHA,
          'carrier65_proof_sha256':CARRIER_SHA,'inert_source_graph_sha256':SOURCE_SHA,
          'inert_source_proof_sha256':SOURCE_PROOF_SHA,'complete_graph_sha256':digests,
          'graphs':checked,'polynomial_identities':check_identities(),'complete2471_ports':check_ports(graphs),
          'negative_controls':negatives,
          'scope':'Complete literal69/70 integer graphs, all-variable exact leading forms, exact polynomial identities and all whole fixed ports. The incoming source is authenticated JSON/text data only. No incoming or project code imports, no rendered-page claim, no formal-kernel replay or consistency decision.'}
    raw=encoded(data);target=HERE/'CERTIFICATE.json'
    if args.write:target.write_bytes(raw)
    else:require(target.read_bytes()==raw,'Deterministic certificate byte equality')
    print(json.dumps({'status':'PASS','positive_variables':13,'operations':[69,70],'degrees':[174,140],
                      'raw_ports':58125,'audit_sha256':data['audit_sha256'],
                      'graph_sha256':digests,'certificate_sha256':sha(raw)},sort_keys=True))


if __name__=='__main__':
    main()
