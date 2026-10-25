#!/usr/bin/env python3
"""Independent literal audit of the precompression modular source.

Imports only the Python standard library.  It does not import its producer,
the polynomial optimizer, or their certificates.  The signed mathematical
meaning is proved in MODULAR_PROOF.md; this checks the finite interface.
"""
from __future__ import annotations
from collections import defaultdict
from pathlib import Path
import argparse, hashlib, json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def add(*ps):
    d=defaultdict(int)
    for p in ps:
        for m,c in p.items():d[m]+=c
    return {m:c for m,c in d.items() if c}
def scale(p,c):return {m:a*c for m,a in p.items() if a*c}
def mul(p,q):
    d=defaultdict(int)
    for m,a in p.items():
        for n,b in q.items():d[tuple(sorted(m+n))]+=a*b
    return {m:c for m,c in d.items() if c}
def sq(p):return mul(p,p)
def C(c):return {():c} if c else {}
def V(i):return {(i,):1}
def norm(ts):return add(*[{tuple(sorted(m)):c} for c,m in ts])
def equal(p,q,label):
    delta=add(p,scale(q,-1))
    if delta:raise ValueError((label,'polynomial difference',delta))

def audit(path,parent):
    src=json.loads(path.read_text());old=json.loads(parent.read_text());vs=src['variables'];names={v['name']:i for i,v in enumerate(vs)}
    if len(names)!=len(vs):raise ValueError('duplicate variable names')
    if vs[:len(old['variables'])]!=old['variables']:raise ValueError('preexisting variable ledger changed')
    expected_new=['frame.L','free_A.u','free_A.v','free_A.w','self_radix.H','choose0.odd_half','modular_root.quotient']
    if [v['name'] for v in vs[len(old['variables']):]]!=expected_new:raise ValueError('unexpected fresh coordinates')
    if len(src['residuals'])!=len(old['residuals'])+4:raise ValueError('wrong row count')
    labels=defaultdict(list)
    for rr in src['residuals']:
        p=norm(rr['terms']);labels[rr['label']].append(p)
        if any(len(m)>2 for m in p):raise ValueError(('nonquadratic residual',rr['label']))
        if any(not isinstance(c,int) or any(not isinstance(i,int) or not 0<=i<len(vs) for i in m) for m,c in p.items()):raise ValueError('nonintegral/invalid sparse term')
    def row(name):
        if len(labels[name])!=1:raise ValueError(('nonunique row',name,len(labels[name])))
        return labels[name][0]
    def vv(name):return V(names[name])
    t=add(vv('t0'),C(16));x=vv('x');y=vv('y');R=vv('radius.R');B=vv('choose0.output');q=vv('pow2.output');A=vv('shared.A');W=vv('shared.W');H=vv('self_radix.H');BH=vv('self_radix.BH')
    reps=[add(V(i),C(1)) for i in range(16,25)];J=add(vv('add.380'),C(1));out=lambda k:R if k==0 else vv(f'pow{k}.output')
    req=[(C(16),t,out(0),'index0'),(B,x,out(1),'index12'),(BH,x,out(2),'index12'),
      (add(q,C(1)),add(R,t),out(3),'index2'),(q,t,out(4),'index0'),
      (add(q,C(1)),reps[0],out(5),'index3'),(q,add(t,C(1)),out(6),None),
      (add(q,C(1)),reps[1],out(7),'index5'),(add(q,C(1)),reps[2],out(8),'index6'),
      (add(q,C(1)),reps[3],out(9),'index7'),(add(q,C(1)),reps[4],out(10),'index8'),
      (q,add(y,C(1)),out(11),'index9'),(add(q,C(1)),reps[5],out(12),'index10'),
      (add(q,C(1)),reps[6],out(13),'index11'),(q,x,out(14),'index12'),
      (add(q,C(1)),reps[7],out(15),'index13'),(add(q,C(1)),reps[8],out(16),'index14'),
      (add(q,C(1)),J,out(17),'index15')]
    modular={3,5,7,8,9,10,12,13,15,16,17};exact={0,1,2,4,11,14}
    changed={'shared.frame_definition','shared.last_norm','self_radix.base_definition','pow6.power_congruence'}|{f'pow{k}.power_congruence' for k in modular}
    untouched=0
    for i,rr in enumerate(old['residuals']):
        if rr['label'] not in changed:
            if src['residuals'][i]!=rr:raise ValueError(('unexpected parent-row mutation',i,rr['label']))
            untouched+=1
    appended=[rr['label'] for rr in src['residuals'][len(old['residuals']):]]
    if appended!=['free_A.cofinal_constructor','self_radix.signed_majorant','choose0.odd_constructor','modular_root.common_congruence']:raise ValueError(('new rows',appended))
    equal(row('cofinal.horizon'),add(vv('t0'),scale(sq(vv('cofinal.horizon_root')),-1)),'cofinal horizon')
    equal(row('self_radix.signed_majorant'),add(H,C(-2),scale(add(R,t),-2),*[scale(sq(a),-1) for a in reps]),'squared majorant')
    equal(row('self_radix.base_definition'),add(BH,scale(mul(B,H),-1)),'radix base BH')
    equal(row('choose0.odd_constructor'),add(B,scale(vv('choose0.odd_half'),-2),C(-1)),'odd binomial output')
    equal(row('radix.progression'),add(q,scale(vv('radix.progression_parameter'),-6),C(-3)),'radix progression')
    equal(row('beta.RB'),add(vv('beta.RB'),scale(mul(R,B),-1)),'linear beta product')
    equal(row('beta.odd_square_multiplier'),add(vv('beta.odd_square_multiplier'),scale(sq(add(scale(vv('beta.odd_square_root_half'),2),C(1))),-1)),'odd beta square')
    equal(row('bootstrap.beta_base_fixed_radius'),add(y,scale(mul(vv('beta.RB'),vv('beta.odd_square_multiplier')),-1)),'beta definition')
    atoms={tuple(sorted(p.items())):p for n,k,m,prefix in req for p in (n,k,m)}
    for k in modular:atoms.pop(tuple(sorted(out(k).items())))
    equal(row('shared.frame_definition'),add(W,C(-2),*[scale(sq(p),-1) for p in atoms.values()]),'frame excludes exactly modular outputs')
    equal(row('free_A.cofinal_constructor'),add(A,scale(sq(vv('frame.L')),-1),scale(sq(vv('free_A.u')),-1),scale(sq(vv('free_A.v')),-1),scale(sq(vv('free_A.w')),-1),scale(vv('free_A.w'),-1)),'cofinal free center')
    # Expand elementary multiplication gates without importing any producer.
    gate={}
    for p in labels['multiplication']:
        cs=[m[0] for m,c in p.items() if len(m)==1 and c==1 and vs[m[0]]['kind']=='gate']
        if len(cs)!=1:raise ValueError(('ambiguous elementary gate',p))
        i=cs[0]
        if i in gate or any(i in m for m in p if m!=(i,)):raise ValueError(('nonfunctional gate',i))
        gate[i]=scale(add(p,scale(V(i),-1)),-1)
    stop={i for n,k,m,prefix in req for p in (n,k,m) for mon in p for i in mon}|{names['shared.A'],names['shared.W']}
    def expand(p,stack=()):
        result=[]
        for mon,c in p.items():
            v=C(c)
            for i in mon:
                if i in gate and i not in stop:
                    if i in stack:raise ValueError(('cycle',stack,i))
                    f=expand(gate[i],stack+(i,))
                else:f=V(i)
                v=mul(v,f)
            result.append(v)
        return add(*result)
    expected_norm=add(sq(vv('frame.L')),scale(mul(mul(sq(W),W),mul(add(W,C(2)),sq(add(scale(vv('shared.Zminus1'),2),C(1))))),-1),C(-1))
    equal(expand(row('shared.last_norm')),expected_norm,'independent lower Pell frame')
    principal={}
    for n,k,m,prefix in req:
        if prefix:
            if prefix in principal:equal(principal[prefix],k,'shared principal nominal index')
            principal[prefix]=k
    pool=[]
    for prefix,k in principal.items():
        X=vv(prefix+'.X');Y=vv(prefix+'.Y')
        equal(expand(row(prefix+'.norm1')),add(sq(X),sq(Y),scale(mul(sq(A),sq(Y)),-1),C(-1)),prefix+' norm')
        pool.extend([sq(add(X,C(-1))),sq(add(Y,scale(k,-1)))])
    pool.append(scale(mul(add(A,C(-1)),vv('cap.pooled_quotient')),-1))
    equal(row('cap.pooled_index_residue'),add(*pool),'fourteen signed principal pairs in pool')
    bases=[C(16),B,BH,add(q,C(1)),q]
    for i,n in enumerate(bases):
        equal(expand(row(f'base{i}.T_definition')),add(scale(mul(A,n),2),scale(sq(n),-1),C(-1),scale(vv(f'base{i}.T'),-1)),f'modulus {i}')
    base_index={0:0,1:1,2:2,4:4,11:4,14:4}
    for call in exact:
        n,k,m,prefix=req[call];X=vv(prefix+'.X');Y=vv(prefix+'.Y')
        expected=add(X,mul(add(n,scale(A,-1)),Y),scale(m,-1),scale(mul(vv(f'base{base_index[call]}.T'),vv(f'pow{call}.quotient')),-1))
        equal(expand(row(f'pow{call}.power_congruence')),expected,f'exact power {call}')
    for call in modular:
        n,k,m,prefix=req[call]
        equal(row(f'modular_numerator{call}.definition'),add(vv(prefix+'.X'),mul(add(q,C(1),scale(A,-1)),vv(prefix+'.Y')),scale(m,-1)),f'modular evaluation {call}')
        if labels[f'pow{call}.power_congruence']:raise ValueError(('obsolete exact numerator retained',call))
    equal(row('radix.successor_power'),add(out(6),scale(mul(q,out(4)),-1)),'successor power multiplication')
    NM=vv('mul.430');N=out(1);M=out(14)
    equal(expand(NM),mul(N,M),'existing shared range modulus')
    equal(row('modular_root.common_congruence'),add(vv('base3.T'),scale(mul(NM,vv('modular_root.quotient')),-1)),'one common modular root')
    for i,den in enumerate((out(4),out(6),out(11))):
        equal(row(f'remainder_budget.ratio{i}'),add(M,scale(mul(den,vv(f'remainder_budget.ratio{i}')),-1)),f'positive denominator ratio {i}')
    return {'status':'passed','scope':'Independent literal interface audit; mathematical semantics are separate.',
      'raw_source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'parent_raw_sha256':hashlib.sha256(parent.read_bytes()).hexdigest(),
      'raw_variables':len(vs),'raw_rows':len(src['residuals']),'unchanged_parent_rows':untouched,'fresh_coordinates':len(expected_new),
      'exact_power_requests_checked':len(exact),'modular_evaluations_checked':len(modular),'principal_signed_pairs_checked':len(principal),'successor_power_multiplications':1,'common_modular_roots':1,'frame_atoms':len(atoms)}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=ROOT/'stages/modular/raw_source.json');ap.add_argument('--parent',type=Path,default=ROOT/'stages/fixed_base/raw_source.json');ap.add_argument('--output',type=Path,default=ROOT/'stages/modular/interface_audit.json')
    a=ap.parse_args();r=audit(a.source,a.parent);a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(json.dumps(r,indent=2))
