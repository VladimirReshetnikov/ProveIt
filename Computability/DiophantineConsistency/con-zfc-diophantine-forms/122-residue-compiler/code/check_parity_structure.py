#!/usr/bin/env python3
"""Independent finite checks of parity, frame, index and digit interfaces.

Imports no producer or optimizer. These checks complement the unbounded proof.
"""
from pathlib import Path
from collections import Counter
from math import factorial
import argparse, copy, hashlib, json

def need(c,m):
    if not c:raise ValueError(m)
def add(*ps):
    z=Counter()
    for p in ps:
        for m,c in p.items():z[m]+=c
    return {m:c for m,c in z.items() if c}
def scale(p,c):return {m:c*v for m,v in p.items() if c*v}
def mul(p,q):
    z=Counter()
    for a,c in p.items():
        for b,d in q.items():z[tuple(sorted(a+b))]+=c*d
    return {m:c for m,c in z.items() if c}
def atom(a):return {():a[1]} if a[0]=='c' else {(a[1],):1}
def square(p):return mul(p,p)
def product(ps):
    z={():1}
    for p in ps:z=mul(z,p)
    return z

def verify(meta,interface):
    rows=meta['rows'];vs=meta['variables'];gates={int(k):v for k,v in meta['gates'].items()}
    lookup={r['label']:[] for r in rows}
    for r in rows:lookup[r['label']].append(r)
    def row(label):
        need(len(lookup.get(label,[]))==1,'missing or duplicated row '+label)
        return {tuple(m):c for c,m in lookup[label][0]['terms']}
    def rhs(v):
        r={tuple(m):c for c,m in rows[gates[v]]['terms']}
        need(r.get((v,))==1,'nonmonic source gate')
        need(all(v not in m for m in r if m!=(v,)),'self-referential gate')
        return scale({m:c for m,c in r.items() if m!=(v,)},-1)
    def expression(p,boundaries):
        stop={a[1] for a in boundaries if a[0]=='v'};cache={}
        def value(v):
            if v in stop or v not in gates:return {(v,):1}
            if v not in cache:cache[v]=expand(rhs(v))
            return cache[v]
        def expand(p):
            return add(*(scale(product(value(v) for v in m),c) for m,c in p.items()))
        return expand(p)
    def equal(label,expected,boundaries):
        need(expression(row(label),boundaries)==expected,'row identity failed '+label)
    def value(a,boundaries):return expression(atom(a),boundaries)
    names={v['name']:('v',i) for i,v in enumerate(vs)}
    parity={};lower={}
    for v in range(len(vs)):
        if v not in gates:parity[v]=None;lower[v]=0;continue
        p=rhs(v);terms=[];lb=0;nonnegative=all(c>=0 for c in p.values())
        for m,c in p.items():
            need(all(j<v for j in m),'nontriangular gate')
            bits=[parity[j] for j in m]
            terms.append(0 if c%2==0 or 0 in bits else None if None in bits else 1)
            if nonnegative:
                q=c
                for j in m:q*=lower[j]
                lb=min(64,lb+q)
        parity[v]=None if None in terms else sum(terms)%2
        lower[v]=lb if nonnegative else 0
    def par(a):return a[1]%2 if a[0]=='c' else parity[a[1]]
    def lo(a):return a[1] if a[0]=='c' else lower[a[1]]
    amp=meta['amplification'];rad=meta['radix'];outer=amp['outer_values']
    t,x,y,F=[outer[n] for n in ('t','x','y','F')];N,K,B,C=[amp[n] for n in ('N','K','B','index')]
    q=rad['radix'];V=rad['V'];horizon=interface['horizon_minimum']
    fh=meta['factorials'][0]['half_output'];r0=names['endpoint.r0']
    need(value(F,[fh])==scale(atom(fh),2),'factorial output not literally even')
    need(value(t,[names['t0']])==add(scale(atom(names['t0']),2),{():horizon}),'horizon parity')
    need(value(x,[names['xhalf_minus1']])==add(scale(atom(names['xhalf_minus1']),2),{():2}),'x parity')
    need(value(y,[F,r0])==add(atom(F),scale(atom(r0),2),{():2}),'y parity')
    need(all(par(z)==0 for z in (t,x,y,F,K,C)),'outer parity not syntactic')
    need(lo(t)>=12 and lo(x)>=2 and lo(y)>=2,'outer positive floor')
    for s in meta['seeds']:
        need(par(s['exponent'])==0,'seed exponent is not provably even')
        need(lo(s['exponent'])>=2,'seed exponent not provably positive')
    need(not any('YminusK' in v['name'] for v in vs),'unexpected index gap coordinate')
    need(not any('index_at_most_Y' in r['label'] for r in rows),'unexpected index gap constraint')
    U,Vaux,Baux=meta['auxiliary'];W,A,Z=meta['scale']
    need(Vaux==interface['strict_auxiliary_ordinate'] and lo(Vaux)>=1,'strict common ordinate absent')
    need(value(Vaux,[names['shared_index.Vminus1']])==add(atom(names['shared_index.Vminus1']),{():1}),'strict ordinate definition')
    L=names['shared.lower_A'];As=names['shared.A_slack']
    need(value(A,[L,As])==add(atom(L),atom(As)),'cofinal A definition')
    equal('shared.last_norm_lower',add(square(atom(L)),scale(mul(product([atom(W),atom(W),atom(W)]),mul(add(atom(W),{():2}),square(atom(Z)))),-1),{():-1}),[L,W,Z])
    exact_atoms={tuple(a) for p in meta['powers'] for a in(p['base'],p['exponent'],p['output'])}
    frame_atoms=exact_atoms|{tuple(r['n']) for r in rad['modular_requests']}
    expected=add(atom(W),{():-2},*(scale(atom(a),-1) for a in frame_atoms))
    equal('shared.frame_definition',expected,[W]+list(frame_atoms))
    for s in meta['seeds']:
        k=s['exponent'];X,Y=s['pair'];tag=vs[X[1]]['name'].rsplit('.',1)[0]
        S,R,sq,rq=[names[tag+'.'+n] for n in ('S','R','Squotient','Rquotient')]
        stop=[A,Baux,U,Vaux,k,X,Y,S,R,sq,rq]
        equal(tag+'.norm1',add(square(atom(X)),square(atom(Y)),scale(mul(square(atom(A)),square(atom(Y))),-1),{():-1}),stop)
        equal(tag+'.norm3',add(square(atom(S)),square(atom(R)),scale(mul(square(atom(Baux)),square(atom(R))),-1),{():-1}),stop)
        equal(tag+'.S_mod_U',add(atom(S),scale(atom(X),-1),scale(mul(atom(U),atom(sq)),-1)),stop)
        equal(tag+'.R_mod_4Y',add(atom(R),scale(atom(k),-1),scale(mul(atom(Y),atom(rq)),-4)),stop)
    ys=[s['pair'][1] for s in meta['seeds']];vm1=names['shared_index.Vquotient_minus1']
    equal('shared_index.V_positive_product',add(atom(Vaux),scale(mul(product(square(atom(z)) for z in ys),add(atom(vm1),{():1})),-1)),[Vaux,vm1]+ys)
    ut,u0=names['endpoint.ut'],names['endpoint.u0']
    equal('endpoint.last_quotient',add(atom(x),{():-1},scale(mul(add({():1},mul(add(atom(t),{():1}),atom(y))),atom(ut)),-1)),[x,t,y,ut])
    equal('endpoint.first_quotient',add(atom(x),scale(atom(F),-1),{():-1},scale(mul(add(atom(y),{():1}),atom(u0)),-1)),[x,F,y,u0])
    enc=amp['encoded_values'];expected_ranges=[]
    for i,n in enumerate(meta['local_names']):
        expected_ranges.append((enc[n],t if i<4 else y if i<6 else x,N,'crt.range.'+n))
        need(par(enc[n])==0 and lo(enc[n])>=2,'encoded representative not positive even')
    expected_ranges.append((C,t,N,'crt.range.index'))
    J=amp['derived_label_sum'];twiceJ=amp['derived_range_argument']
    need(value(twiceJ,[J])==scale(atom(J),2),'derived argument not twice J')
    last=meta['ranges'][-1];need(last[0]==twiceJ and last[2]==N,'derived range binding')
    need(value(last[1],[t])==scale(atom(t),2),'derived lower index not twice t')
    expected_ranges.append(tuple(last))
    need([list(v) for v in expected_ranges]==meta['ranges'],'range family differs')
    ag=rad['aggregate_slack'];reps=[C]+list(enc.values())
    equal('crt.aggregate_representative_bound',add(scale(square(atom(N)),18),*(scale(atom(z),-1) for z in reps),scale(atom(ag),-1)),[N,ag]+reps)
    defs=interface['even_power_derivations'];need(len(defs)==1,'expected one derived power')
    dd=defs[0]
    need(dd['base']==q and dd['half_exponent']==t,'wrong doubled power base/exponent')
    need(value(dd['exponent'],[t])==scale(atom(t),2),'wrong double exponent')
    need(value(dd['output'],[dd['half_output']])==square(atom(dd['half_output'])),'doubled power is not square')
    power_map={(tuple(p['base']),tuple(p['exponent'])):p['output'] for p in meta['powers']}
    need(power_map[tuple(q),tuple(t)]==dd['half_output'],'doubled power source not certified')
    dx=power_map[tuple(q),tuple(x)];M=rad['common_root_modulus'];rq=rad['root_quotient'];qb=rad['root_base']
    need(value(M,[N,dx])==mul(atom(N),atom(dx)),'dominant modulus differs')
    need(value(qb,[q])==add(atom(q),{():1}),'root base differs')
    equal('modular.common_root',add(scale(mul(atom(A),add(atom(q),{():1})),2),scale(square(add(atom(q),{():1})),-1),{():-1},scale(mul(mul(atom(N),atom(dx)),atom(rq)),-1)),[A,q,N,dx,rq])
    idx={tuple(i['exponent']):i['pair'] for i in meta['indices']}
    for req in rad['modular_requests']:
        label=req['label'];X,Y=req['pair'];n=req['n'];den=req['den'];res=req['remainder'];rs=req['remainder_slack'];quo=req['quotient'];mod=req['modulus']
        need(idx[tuple(n)]==req['pair'],'wrong modular index pair')
        modulus=mul(atom(den),atom(q if req['kind']=='exact' else N))
        need(value(mod,[den,q,N])==modulus,'wrong digit modulus')
        residue=atom(res);stop=[X,Y,A,q,den,N,res,rs,quo]
        if req['kind']=='exact':
            out=req['output'];os=names[label+'.modular_oslack'];stop.extend([out,os]);residue=add(residue,mul(atom(den),atom(out)))
            equal(label+'.digit_bound',add(atom(q),scale(atom(out),-1),scale(atom(os),-1),{():-1}),stop)
        equal(label+'.modular_digit',add(atom(X),mul(add(atom(q),{():1}),atom(Y)),scale(mul(atom(A),atom(Y)),-1),scale(residue,-1),scale(mul(modulus,atom(quo)),-1)),stop)
        equal(label+'.remainder_bound',add(atom(den),scale(atom(res),-1),scale(atom(rs),-1),{():-1}),stop)
    E=meta['local_majorant']['emitted_exponent'];ell=meta['local_majorant']['derived_label_majorant']['emitted_exponent'];fm=factorial(horizon);a=fm.bit_length()-1
    need(horizon>=12 and horizon%2==0,'invalid horizon floor')
    need(a*E<2**a and 2*E<=2**a and horizon*(3*ell+1)<=fm,'budget floor failed')
    return {'verified':True,'seed_indices':len(meta['seeds']),'syntactically_even_positive_seeds':len(meta['seeds']),'exact_powers':len(meta['powers']),'modular_digits':len(rad['modular_requests']),'literal_shared_index_rows_checked':4*len(meta['seeds']),'frame_includes_all_modular_indices':True,'derived_power_squares':len(defs),'horizon_floor':horizon,'source_majorant_exponent':E,'label_majorant_exponent':ell,'factorial_floor':fm,'aggregate_capacity':18}

def run(directory):
    d=Path(directory);meta=json.loads((d/'raw/raw_audit_input.json').read_text());interface=json.loads((d/'raw/parity_interface.json').read_text())
    result=verify(meta,interface)
    bad=copy.deepcopy(meta);bad['seeds'][0]['exponent']=['v',0]
    try:verify(bad,interface)
    except ValueError:result['changed_seed_negative_control']='rejected'
    else:raise ValueError('bad parity seed accepted')
    result['metadata_sha256']=hashlib.sha256((d/'raw/raw_audit_input.json').read_bytes()).hexdigest()
    return result
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('directory',type=Path);p.add_argument('--output',type=Path);a=p.parse_args()
    r=run(a.directory);s=json.dumps(r,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(s)
    print(s)
