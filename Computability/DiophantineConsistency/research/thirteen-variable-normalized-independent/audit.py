#!/usr/bin/env python3
"""Audit the complete normalized13-positive71-operation degree128 integer DAG."""
import argparse
from collections import Counter
from copy import deepcopy
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PROOF_SHA = '22670c2f7c35a9e0b88b9505620c924f2a867922cb62464bee0bcf54f752529d'
PARENT_FOLDER = ROOT / 'research/thirteen-variable-independent'
PARENT_SHA = 'b36b1b4fa645b772d5cafe82a0359eca264e228114cacd2fcce6da902b2eac82'
PARENT69_SHA = '3400069ead0bbf7b85d382c47fdd790bc18d68d9979e049f475d4e1c52d4182f'
PARENT_PROOF_SHA = 'd2e40a04fdc670a5f5a05d2c8e7e762e07ef559eb051e5ff6f5c82e7e3e8f6a8'
PARENT_CERT_SHA = '595d70e2b2213e89bd76c0f1f3a5d8b992e4ebd4d63fce971e7bdc24e147fcdf'
LEAD_SHA = '50c2adcb78198e111abba88344fccabfd2a493399cf02772316418eae3ea9f57'
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


def expected_graph(parent):
    graph=deepcopy(parent)
    graph.update({'name':'thirteen_positive2471_normalized71_degree128','operations':71,
                  'operation_counts':{'*':40,'+':16,'-':15},'exact_degree':128,
                  'proof':'PROOF.md','arithmetic_proof':'PROOF.md','arithmetic_proof_sha256':PROOF_SHA,
                  'parent_polynomial':'../thirteen-variable-independent/polynomial70.json',
                  'parent_polynomial_sha256':PARENT_SHA,
                  'proof_boundary':'Exact identity p70=Delta*p71 and Delta>0 on all13-positive assignments, composed with the complete frozen2471 theorem; retained ordinary contracts, no new formal-kernel replay.'})
    # Incoming ancestry remains in the authenticated parent, rather than a stale local path.
    del graph['inert_source_graph'];del graph['inert_source_graph_sha256']
    graph['display_scalar_names'].pop('scaled_Ns')
    graph['display_scalar_names'].pop('normalized_S')
    graph['display_scalar_names']['normalized_Ns']='Z'
    rows=[]
    for row in parent['source']:
        if row[0]=='normalized_S':
            rows.extend([['hi2','*','hi','hi'],['intermediate','*','hi2','Dc2'],
                         ['strong_term','*','intermediate','c2']])
        elif row[0]=='normalized_S2':
            continue
        elif row[0]=='scaled_Ns':
            rows.append(['normalized_Ns','-','f2','strong_term'])
        elif row[0]=='product4':
            rows.append(['product4','*','product1','normalized_Ns'])
        elif row[0]=='polynomial':
            rows.append(['polynomial','-','product4',1])
        else:
            rows.append(list(row))
    graph['source']=rows
    return graph


def check_parent_pair(parent69,parent70,receipt):
    rows=[]
    for row in parent69['source']:
        if row[0]=='scaled_f2':continue
        if row[0]=='aux_product':
            rows.extend([['scaled_f2','*','Delta','f2'],['Theta','-','scaled_f2','Delta'],
                         ['aux_product','*','Theta','V2minusY2']])
        else:rows.append(row)
    require(rows==parent70['source'],'Entire authenticated69-to70 schedule identity')
    require(parent69['witnesses']==parent70['witnesses']==VARIABLES
            and parent69['fixed_numerals']==parent70['fixed_numerals']==PORTS
            and parent69['coefficient_binding']==parent70['coefficient_binding'],
            'Both complete retained interfaces and actual native ports agree')
    require(receipt['ordinary_proof_sha256']==PARENT_PROOF_SHA
            and receipt['complete_graph_sha256']=={'polynomial69.json':PARENT69_SHA,'polynomial70.json':PARENT_SHA},
            'Entire retained pair certificate and corrected proof binding')


def check_graph(graph,parent,parent_receipt):
    require(graph==expected_graph(parent),'Every literal row, metadata field and fixed-port binding')
    require(graph['witnesses']==VARIABLES and graph['fixed_numerals']==PORTS
            and graph['witness_domain']=='strictly positive integers','Exact13-positive interface')
    rows=graph['source'];require(len(rows)==71,'All71 binary rows')
    known=set(SYMBOLS);by_name={}
    for row in rows:
        require(type(row) is list and len(row)==4,'Literal binary row shape')
        name,op,l,r=row
        require(type(name) is str and name not in known and op in ('+','-','*'),'Unique legal gate')
        require(all(type(v) is int or type(v) is str and v in known for v in (l,r)),
                'Integer-only leaves and complete topological dependencies')
        known.add(name);by_name[name]=row
    counts=dict(sorted(Counter(r[1] for r in rows).items()))
    require(counts=={'*':40,'+':16,'-':15}==graph['operation_counts'],'Exact integer-leaf operation count')
    live=set()
    def visit(name):
        if type(name) is int or name in live:return
        live.add(name)
        if name in by_name:
            visit(by_name[name][2]);visit(by_name[name][3])
    visit('polynomial');require(live==known,'Every remaining producer,13 unknowns and four ports is live')
    old={row[0]:row for row in parent['source']}
    deleted=set(old)-set(by_name);added=set(by_name)-set(old)
    changes={n for n in set(old)&set(by_name) if old[n]!=by_name[n]}
    require(deleted=={'normalized_S','normalized_S2','scaled_Ns'}
            and added=={'hi2','intermediate','strong_term','normalized_Ns'}
            and changes=={'product4','polynomial'},'Every change from the complete70-row parent')
    full_cache={n:symbol(n) for n in SYMBOLS}
    def full(name):
        if type(name) is int:return {ZERO:name} if name else {}
        if name not in full_cache:
            _,op,l,r=by_name[name];a,b=full(l),full(r)
            full_cache[name]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
        return full_cache[name]
    main=full('N1');root=add(full('X'),mul(symbol('gamma'),full('H')))
    main_identity=add(add(power(root,2),product([(full('a'),1),(full('c'),1),(root,1)],2)),
                      mul(full('H'),power(full('c'),2)),-1)
    require(main==main_identity and degree(main)==18,'Entire main-norm cancellation resolved by full expansion')
    leaders={n:symbol(n) for n in SYMBOLS};cancellations=[]
    for name,op,l,r in rows:
        a={ZERO:l} if type(l) is int else leaders[l]
        b={ZERO:r} if type(r) is int else leaders[r]
        if op=='*':v=mul(a,b)
        else:
            da,db=degree(a),degree(b)
            if da>db:v=a
            elif db>da:v=b if op=='+' else mul({ZERO:-1},b)
            else:v=add(a,b,1 if op=='+' else -1)
            if not v:
                cancellations.append(name);v=leading(full(name))
        leaders[name]=v
    require(cancellations==['N1'],'Every gate leading cancellation explicitly resolved')
    q0=mul(symbol('beta'),symbol('J'));k0=add(symbol('eta'),symbol('zeta'))
    C0=add(add(q0,symbol('F'),-1),symbol('alpha'),-1)
    w,s,f,t,i,gamma=[symbol(n) for n in ('w','s','f','T','i','gamma')]
    delta0=product([(w,2),(s,2),(q0,8)])
    strong0=product([(i,2),(w,2),(s,6),(k0,4),(q0,22)])
    require(leaders['Delta']==delta0 and degree(delta0)==12,'Exact positive discriminant leading form')
    require(leaders['hi2']==product([(q0,2),(i,2)])
            and leaders['intermediate']==product([(q0,16),(i,2),(w,2),(s,4),(k0,2)])
            and leaders['strong_term']==strong0,'All three new strong-product leaders')
    factors={'N0':product([(w,2),(s,4),(k0,2),(q0,14)],-1),
             'N1':product([(gamma,1),(w,2),(s,3),(k0,1),(q0,11)],8),
             'Na':product([(q0,22),(k0,4),(s,6),(w,4),(f,10),(t,4),(C0,2)],-16),
             'normalized_Ns':mul({ZERO:-1},strong0)}
    for n,v in factors.items():require(leaders[n]==v,'Complete factor leader '+n)
    degrees={n:degree(v) for n,v in factors.items()}
    require(list(degrees.values())==[22,18,52,36],'Every exact factor degree')
    expected=product([(q0,69),(gamma,1),(i,2),(k0,11),(w,10),(s,19),(f,10),(t,4),(C0,2)],-128)
    require(leaders['polynomial']==expected and degree(expected)==128==graph['exact_degree'],
            'Entire degree128 leading homogeneous polynomial')
    chosen={'J':71,'beta':71,'gamma':1,'i':2,'eta':11,'w':10,'s':19,'f':10,'T':4}
    require(expected.get(tuple(chosen.get(n,0) for n in SYMBOLS))==-128,'Nonzero actual fixed-beta coefficient')
    prior=parent_receipt['graphs']['polynomial70.json']
    require(prior['leader_symbols']==SYMBOLS,'Complete parent leader coordinate order')
    parent_leader={tuple(m):v for m,v in prior['complete_leader']}
    require(mul(delta0,expected)==parent_leader and degree(parent_leader)==140,
            'Entire homogeneous identity agrees with complete accepted140 leader')
    return {'operations':counts,'live_gates':71,'live_positive_variables':13,'live_fixed_ports':4,
            'deleted_parent_rows':sorted(deleted),'added_rows':sorted(added),'changed_rows':sorted(changes),
            'factor_degrees':degrees,'exact_degree':128,'leader_symbols':SYMBOLS,
            'complete_main_norm_terms':len(main),'main_norm_sha256':sha(encoded(polynomial_rows(main))),
            'complete_factor_leaders':{n:polynomial_rows(v) for n,v in factors.items()},
            'complete_leader':polynomial_rows(expected),'complete_leader_terms':len(expected),
            'leader_sha256':sha(encoded(polynomial_rows(expected))),
            'selected_coefficient':'-128*beta^71','accounted_cancellations':cancellations,
            'parent140_leader_identity':True,
            'all_gate_leaders':{n:{'degree':degree(leaders[n]),'terms':len(leaders[n]),
                                  'sha256':sha(encoded(polynomial_rows(leaders[n])))} for n in by_name}}


def check_whole_identity(graph,parent):
    # Evaluate both actual literal DAGs with common subexpressions as independent cuts.
    delta,f,b,i,c,P,Q,U=[symbol(n) for n in ('J','F','alpha','f','i','T','s','w')]
    cuts={'Delta':delta,'f2':power(f,2),'hi':mul(b,i),'c2':power(c,2),
          'Dc2':mul(delta,power(c,2)),'N0':P,'N1':Q,'Na':U}
    def evaluate(g):
        rows={row[0]:row for row in g['source']};cache=dict(cuts)
        def rec(n):
            if type(n) is int:return {ZERO:n} if n else {}
            if n not in cache:
                _,op,l,r=rows[n];a,b=rec(l),rec(r)
                cache[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
            return cache[n]
        return rec('polynomial'),rec
    old,old_eval=evaluate(parent);new,new_eval=evaluate(graph)
    strong=product([(delta,1),(b,2),(i,2),(c,4)])
    zbar=add(power(f,2),strong,-1)
    require(new_eval('strong_term')==strong and new_eval('normalized_Ns')==zbar,
            'Actual literal normalized strong factor equals its full symbolic recipe')
    require(old_eval('scaled_Ns')==mul(delta,zbar),'Actual parent strong factor equalsDelta times normalized factor')
    require(old==mul(delta,new),'Whole actual literal polynomial identity p70=Delta*p71')
    independent=add(product([(P,1),(Q,1),(U,1),(zbar,1)]),{ZERO:1},-1)
    require(new==independent,'Independent whole normalized polynomial formula')
    wrong=deepcopy(graph)
    next(r for r in wrong['source'] if r[0]=='polynomial')[3]='Delta'
    wrong_value,_=evaluate(wrong)
    require(old!=mul(delta,wrong_value),'Actual output-minusDelta mutation breaks whole identity')
    wrong2=deepcopy(graph)
    next(r for r in wrong2['source'] if r[0]=='strong_term')[3]=1
    wrong_value,_=evaluate(wrong2)
    require(old!=mul(delta,wrong_value),'Actual missing c-squared mutation breaks whole identity')
    # Discriminant positivity is universal for the positive domain, not inferred from samples.
    a=symbol('gamma');delta_formula=add(add(power(a,2),mul({ZERO:4},a)),{ZERO:3})
    require(delta_formula==mul(add(a,{ZERO:1}),add(a,{ZERO:3})),
            'Exact Delta=(a+1)(a+3) factorization for the ordinary positivity argument')
    return {'cut_symbols':{'Delta':'J','f':'F','b':'alpha','i':'f','c':'i','P':'T','Q':'s','U':'w'},
            'actual_parent_polynomial':polynomial_rows(old),'actual_normalized_polynomial':polynomial_rows(new),
            'identity':'p70=Delta*p71','strong_identity':'Zold=Delta*Zbar',
            'positive_discriminant_identity':'Delta=(a+1)*(a+3)',
            'wrong_output_subtrahend_negative':True,'missing_c_squared_negative':True,
            'scope':'Exact formal identities evaluated from both actual whole DAGs with common independently variable cuts. The pinned ordinary proof establishes Delta>0 and both complete positive-zero-set implications.'}


def port_record(value):
    require(type(value) is int and value>0,'Positive complete integer')
    raw=value.to_bytes((value.bit_length()+7)//8,'big')
    return {'bits':value.bit_length(),'bytes':len(raw),'sha256':sha(raw)}


def check_ports(graph):
    folder=ROOT/'research/phase-split-independent'
    pinned(folder/'PROOF.md',NATIVE_SHA)
    cert=json.loads(pinned(folder/'certificate.json',CERT_SHA))
    c=json.loads(pinned(folder/'coefficients.json',ARRAY_SHA))
    require(len(c)==3297 and all(type(v) is int and v>=0 for v in c),'Entire3297 coefficient array')
    rp=lambda e:1<<(47*e)
    G=lambda n:sum(rp(e) for e in range(n))
    beta=rp(2471)-1
    K=rp(18)+rp(1004)+rp(2480)+sum(v*rp(1462-e) for e,v in enumerate(c) if v)
    MC=beta-G(951)-rp(960)*G(26)-rp(1004)
    native=8*G(917)-4+((1<<45)-4)*rp(1462)+rp(960)*G(9)+rp(987)*G(8)+rp(1004)
    values={'beta':beta,'K':K,'MC':MC,'MF_source':beta+native}
    records={n:port_record(v) for n,v in values.items()}
    require(records==cert['constant_ports'] and beta>=31 and K>0 and 0<MC<beta<beta+native<2*beta,
            'Every reconstructed whole2471 integer and exact scalar boxes')
    binding=graph['coefficient_binding']
    require((HERE/binding['ordinary_proof']).resolve()==(folder/'PROOF.md').resolve()
            and binding['ordinary_proof_sha256']==NATIVE_SHA
            and (HERE/binding['certificate']).resolve()==(folder/'certificate.json').resolve()
            and binding['certificate_sha256']==CERT_SHA,'Every resolved native proof and certificate binding')
    for alias,name in {'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}.items():
        entry=binding['ports'][alias]
        raw=gzip.decompress(pinned(HERE/binding['path']/entry['file'],entry['gzip_sha256']))
        require(int.from_bytes(raw,'big')==values[name] and sha(raw)==entry['raw_sha256']
                and len(raw)==entry['raw_bytes'] and values[name].bit_length()==entry['bits'],
                'Entire actual materialized integer leaf '+alias)
    require(sum(v['bytes'] for v in records.values())==binding['raw_bytes']==58125,'Full four-port raw-byte cost')
    require(port_record(MC+rp(1004))!=records['MC'],'Actual physical marker omission changes complete port')
    return {'native_proof_sha256':NATIVE_SHA,'native_certificate_sha256':CERT_SHA,
            'complete_array_sha256':ARRAY_SHA,'ports':records,'raw_bytes':58125,'scalar_boxes':True,
            'selected_actual_coefficient':{'sign':-1,'magnitude':port_record(128*beta**71)},
            'physical_marker_omission_negative':True,
            'scope':'The entire unchanged2471 tuple is reconstructed and byte-compared. Native witness maps and logical calibration remain in the pinned ordinary theorem.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='write only deterministic CERTIFICATE.json')
    args=parser.parse_args()
    pinned(HERE/'PROOF.md',PROOF_SHA)
    pinned(PARENT_FOLDER/'PROOF.md',PARENT_PROOF_SHA)
    pinned(PARENT_FOLDER/'NORMALIZED_LEAD.md',LEAD_SHA)
    pinned(ROOT/'research/carrier65-independent/PROOF.md',CARRIER_SHA)
    parent69=json.loads(pinned(PARENT_FOLDER/'polynomial69.json',PARENT69_SHA))
    parent=json.loads(pinned(PARENT_FOLDER/'polynomial70.json',PARENT_SHA))
    prior=json.loads(pinned(PARENT_FOLDER/'CERTIFICATE.json',PARENT_CERT_SHA))
    check_parent_pair(parent69,parent,prior)
    raw=(HERE/'polynomial.json').read_bytes();graph=json.loads(raw)
    require(raw==encoded(expected_graph(parent)),'Canonical entire normalized graph bytes')
    checked=check_graph(graph,parent,prior)
    identity=check_whole_identity(graph,parent);ports=check_ports(graph)
    negatives=[]
    for mutation in ('missing_b','missing_c_squared','wrong_strong_coefficient','wrong_output','wrong_Theta_sign',
                     'rational_leaf','omitted_factor','unused_unknown','degree_metadata','port_metadata'):
        bad=deepcopy(graph);rows={r[0]:r for r in bad['source']}
        if mutation=='missing_b':rows['hi'][2]=1
        elif mutation=='missing_c_squared':rows['strong_term'][3]=1
        elif mutation=='wrong_strong_coefficient':rows['intermediate'][3]='c2'
        elif mutation=='wrong_output':rows['polynomial'][3]='Delta'
        elif mutation=='wrong_Theta_sign':rows['Theta'][1]='+'
        elif mutation=='rational_leaf':rows['four_carrier'][2]=4.0
        elif mutation=='omitted_factor':rows['product4'][3]=1
        elif mutation=='unused_unknown':bad['witnesses'].append('unused')
        elif mutation=='degree_metadata':bad['exact_degree']=127
        else:bad['coefficient_binding']['ports']['MC']['bits']-=1
        try:check_graph(bad,parent,prior)
        except ValueError as error:negatives.append({'mutation':mutation,'rejected_by':str(error)})
        else:raise ValueError('Actual corrupted complete graph accepted: '+mutation)
    data={'schema':'thirteen_positive2471_normalized71_degree128_audit_v1',
          'audit_sha256':sha(Path(__file__).read_bytes()),'ordinary_proof_sha256':PROOF_SHA,
          'parent_proof_sha256':PARENT_PROOF_SHA,'parent69_graph_sha256':PARENT69_SHA,'parent70_graph_sha256':PARENT_SHA,
          'parent_pair_certificate_sha256':PARENT_CERT_SHA,'normalization_lead_sha256':LEAD_SHA,
          'complete_graph_sha256':sha(raw),'graph':checked,'whole_polynomial_identity':identity,
          'complete2471_ports':ports,'negative_controls':negatives,
          'scope':'Complete71-row integer graph, all-variable exact leaders, whole polynomial identity and every fixed integer. No incoming or project code is imported or executed; no page, unrestricted lift, formal-kernel replay or consistency decision is claimed.'}
    result=encoded(data);target=HERE/'CERTIFICATE.json'
    if args.write:target.write_bytes(result)
    else:require(target.read_bytes()==result,'Deterministic complete certificate byte equality')
    print(json.dumps({'status':'PASS','positive_variables':13,'operations':71,'degree':128,'raw_ports':58125,
                      'audit_sha256':data['audit_sha256'],'graph_sha256':sha(raw),
                      'certificate_sha256':sha(result)},sort_keys=True))


if __name__=='__main__':
    main()
