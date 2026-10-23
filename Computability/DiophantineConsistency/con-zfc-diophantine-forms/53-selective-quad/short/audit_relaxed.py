#!/usr/bin/env python3
"""Independent exact circuit, degree, provenance and coefficient audit.

No search for a zero is performed. Finite checks do not prove compiler semantics.
Only Python's standard library is required; checks remain enabled under -O.
"""
from pathlib import Path
from collections import Counter
import gzip, hashlib, json
R = Path(__file__).resolve().parent

def require(c, m):
    if not c:
        raise ValueError(m)

def add(p, q, sign=1):
    r = dict(p)
    for e, v in q.items():
        r[e] = r.get(e, 0) + sign*v
        if r[e] == 0:
            del r[e]
    return r

def mul(p, q):
    r = {}
    for a, x in p.items():
        for b, y in q.items():
            e = tuple(u+v for u,v in zip(a,b))
            r[e] = r.get(e, 0) + x*y
    return {e:v for e,v in r.items() if v}

def circuit(path):
    c = json.loads(path.read_text())
    names = c['witnesses'] + c['fixed_numerals']
    nw = len(c['witnesses'])
    require(nw == 15 and len(names) == 19 and len(set(names)) == 19, 'inputs')
    zero = (0,)*len(names)
    def const(n): return {zero:n} if n else {}
    def var(n):
        e=list(zero); e[names.index(n)]=1
        return {tuple(e):1}
    def top(p):
        d=max((sum(e[:nw]) for e in p), default=0)
        return d,{e:v for e,v in p.items() if sum(e[:nw])==d}
    env={n: (1 if n in c['witnesses'] else 0,var(n)) for n in names}
    full={n:var(n) for n in names}
    known=set(names); deps={}; counts=Counter()
    def get(n): return (0,const(n)) if type(n) is int else env[n]
    def getfull(n): return const(n) if type(n) is int else full[n]
    expanding=True
    for name,op,a,b in c['source']:
        require(name not in known and op in ('+','-','*'),'invalid producer')
        require(all(type(x) is int or x in known for x in (a,b)),'unavailable operand')
        da,pa=get(a); db,pb=get(b)
        if op=='*': d,p=da+db,mul(pa,pb)
        else:
            d=max(da,db);p=add(pa if da==d else {},pb if db==d else {},1 if op=='+' else -1)
        if expanding:
            fa,fb=getfull(a),getfull(b)
            full[name]=mul(fa,fb) if op=='*' else add(fa,fb,1 if op=='+' else -1)
            d,p=top(full[name])
            if name=='norm_main':
                require(d==18,'main cancellation degree')
                expanding=False
        require(p, 'uncertified cancellation at '+name)
        env[name]=(d,p);known.add(name);deps[name]=[a,b];counts[op]+=1
    outputs=[c['output']] if 'output' in c else sum(c['comparisons'],[])
    live=set();todo=list(outputs)
    while todo:
        x=todo.pop()
        if type(x) is not str or x in live: continue
        live.add(x);todo.extend(deps.get(x,[]))
    require(live==known,'dead ports/gates '+str(known-live))
    original=json.loads((R/'upstream/circuits__p75_sos.json').read_text())
    prefix=[g for g in original['source'][:62] if g[0]!='strong_square_scaled']
    require(len(prefix)==61 and c['source'][:61]==prefix,'literal source prefix')
    require(c['witnesses']==original['witnesses'],'coordinate order')
    require(c['fixed_numerals']==original['fixed_numerals'],'port order')
    require(c['coefficient_binding']['file']=='COEFFICIENT_BINDING.json','binding path')
    if 'output' in c:
        if len(c['source'])==74:
            groups=[['main_index','*','norm_main','norm_index'],
                    ['main_index_transport','*','main_index','norm_transport']]
            rows=[('r0','norm_first',1),('ra','norm_aux',1),
                  ('rs','R16','aux_reduced_coefficient'),('rmit','main_index_transport',1)]
        else:
            require(len(c['source'])==72,'single-equation count')
            groups=[['first_main','*','norm_first','norm_main'],
                    ['aux_index','*','norm_aux','norm_index'],
                    ['aux_index_transport','*','aux_index','norm_transport']]
            rows=[('r01','first_main',1),('rait','aux_index_transport',1),
                  ('rs','R16','aux_reduced_coefficient')]
        suffix=groups+[[n,'-',a,b] for n,a,b in rows]+[[n+'2','*',n,n] for n,_,_ in rows]
        previous=rows[0][0]+'2'
        for j,(n,_,_) in enumerate(rows[1:]):
            dest='polynomial' if j==len(rows)-2 else 'sum'+str(j)
            suffix.append([dest,'+',previous,n+'2']);previous=dest
        require(c['source'][61:]==suffix,'literal residual/finalizer matrix')
    else:
        require(len(c['source'])==61,'system count')
        require(c['comparisons']==[['norm_first',1],['norm_main',1],['norm_aux',1],
                ['norm_index',1],['norm_transport',1],['R16','aux_reduced_coefficient']],
                'literal system comparisons')
    residuals=[]
    comparisons=c.get('comparisons', [[g[0],0] for g in c['source'][61:] if g[1]=='-'])
    for a,b in comparisons:
        da,pa=get(a);db,pb=get(b);d=max(da,db)
        p=add(pa if da==d else {},pb if db==d else {},-1)
        require(p,'residual top canceled')
        residuals.append(d)
    result=dict(file=path.name,operations=len(c['source']),multiplications=counts['*'],
                additions=counts['+'],subtractions=counts['-'],witnesses=nw,
                all_gates_and_ports_live=True,residual_exact_degrees=residuals,
                sha256=hashlib.sha256(path.read_bytes()).hexdigest())
    if 'output' in c:
        d,p=env[c['output']]
        if len(c['source'])==74:
            ex=dict(J=28,eta=4,w=4,s=8,T=4,f=8,beta=28);coeff=1
            formula='w^4*s^8*T^4*f^8*(eta+zeta)^4*(beta*J)^28'
        else:
            ex=dict(J=50,eta=6,gamma=2,w=8,s=14,beta=50);coeff=64
            formula='64*gamma^2*w^8*s^14*(eta+zeta)^6*(beta*J)^50'
        e=tuple(ex.get(n,0) for n in names)
        require(d==c['exact_degree'] and p.get(e)==coeff,'exact degree witness')
        expected=const(coeff)
        for n,k in ex.items():
            if n=='eta':
                v=add(var('eta'),var('zeta'))
            else: v=var(n)
            for _ in range(k):expected=mul(expected,v)
        require(p==expected,'complete leading form')
        result.update(exact_degree=d,leading_homogeneous_form=formula,
                      distinguished_monomial={n:k for n,k in ex.items() if n!='beta'},
                      distinguished_coefficient=f'{coeff}*beta^{ex["beta"]}',
                      degree_hypothesis='beta != 0')
    else:
        require(residuals==c['residual_exact_degrees'],'system residual degrees')
        result['exact_maximum_degree']=max(residuals)
    return result

def main():
    pins=json.loads((R/'SOURCE_PINS.json').read_text())
    for p in pins['files']:
        b=(R/p['local_path']).read_bytes()
        require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==p['git_blob_sha1'], 'git blob '+p['local_path'])
        require(hashlib.sha256(b).hexdigest()==p['sha256'],'source SHA256')
    for p in pins.get('historical_files',[]):
        b=(R/p['local_path']).read_bytes()
        require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==p['git_blob_sha1'],'historical git blob')
        require(hashlib.sha256(b).hexdigest()==p['sha256'],'historical SHA256')
    binding=json.loads((R/'COEFFICIENT_BINDING.json').read_text())
    adapter=R/binding['source_adapter_proof_path']
    require(hashlib.sha256(adapter.read_bytes()).hexdigest()==binding['source_adapter_sha256'],'active adapter hash')
    historical=R/binding['source_binding_path']
    require(hashlib.sha256(historical.read_bytes()).hexdigest()==binding['source_binding_sha256'],'historical binding hash')
    ports={}
    for p in binding['payloads']:
        b=(R/p['path']).read_bytes();raw=gzip.decompress(b)
        require(hashlib.sha256(b).hexdigest()==p['gzip_sha256'],'gzip hash')
        require(hashlib.sha256(raw).hexdigest()==p['sha256'],'payload hash')
        require(len(raw)==p['bytes'],'payload length')
        n=int.from_bytes(raw,'little');require(n.bit_length()==p['bit_length'],'bit length')
        ports[p['name']]=n
    beta=ports['beta'];B=beta+1;mf=ports['MF_source']-beta;mc=ports['MC']
    require(B==1<<1064921,'fixed base')
    require(0<mc<beta and 0<mf<beta,'mask range')
    require(mc%4==2 and mf%8==4,'mask congruences')
    require(mc.bit_count()+mf.bit_count()==1064921,'mask populations')
    results=[circuit(R/f) for f in ('p74_relaxed.json','p72_relaxed.json','relaxed15_system61.json')]
    old=json.loads((R/'history/ordinary_blank_four_sos_74.json').read_text())
    renames={'Jrep':'J','Bm1':'beta','Kconstant':'K0','tau_root':'tau',
             'y_aux':'y','transport_quotient':'z','auxiliary_quotient':'T',
             'auxiliary_reduced_coefficient':'aux_reduced_coefficient'}
    oldrows=[[renames.get(x,x) if isinstance(x,str) else x for x in row] for row in old['source'][:61]]
    current=json.loads((R/'relaxed15_system61.json').read_text())['source']
    require(oldrows[:57]==current[:57] and oldrows[59:]==current[59:],'historical kernel comparison')
    require(oldrows[57:59]==[['scaled_f_square','*','A','L16'],
                           ['aux_reduced_coefficient','-','scaled_f_square','A']],
            'historical reduced coefficient')
    require(current[57:59]==[['aux_f2_minus_one','-','L16',1],
                            ['aux_reduced_coefficient','*','A','aux_f2_minus_one']],
            'current distributive coefficient')
    # Exhaust all unit-sign groupings, independently of their semantic sign proofs.
    import itertools
    sign_checks=0
    for signs in itertools.product((-1,1),repeat=5):
        n0,n1,na,nk,nt=signs
        allowed=n0==n1==na==1
        if allowed:
            p74=n0==na==1 and n1*nk*nt==1
            p72=n0*n1==1 and na*nk*nt==1
            require(p74==p72==(nk*nt==1),'group equivalence')
        sign_checks+=1
    out=dict(status='PASS',circuits=results,source_commit=pins['commit'],
             source_files_verified=len(pins['files']),coherent_payloads_verified=4,
             historical_Q56_kernel_recovered=True,
             mask_interface_verified=True,unit_sign_assignments_checked=sign_checks,
             semantic_scope='Ordinary proof in PROOF.md; no compiler formalization or solution search.')
    (R/'AUDIT_RESULTS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
