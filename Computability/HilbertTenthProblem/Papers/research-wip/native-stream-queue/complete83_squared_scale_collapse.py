#!/usr/bin/env python3
"""Fresh bounded transfer audit; predecessor sources are inert bytes/JSON."""
import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

PINS = {
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'complete75_asymmetric_squared_scale_refutation.md':'7d0612495a52f8c9674a5715f8757b331beb2dff8d3815931b247c9f089b156a',
 'complete75_asymmetric_squared_scale_refutation.json':'e7371b420038ce489beb6e031018a80dfe9fcb6ab58adeedc937178bba4ef1fd',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 'pell_kernel_half_binomial42.md':'0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992',
 'complete85_auxiliary_bezout_projection.md':'d8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b',
 'complete86_transport_quotient_shear.md':'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541',
 'complete80_first_index_deletion_collapse.md':'a6fb0955f6a19a7564a3070cbf5bdc4e76a6a39a572b46a4d8f656ae9113a575',
}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def load(raw):
    def pairs(items):
        out = {}
        for k,v in items:
            need(k not in out, 'duplicate key')
            out[k] = v
        return out
    def bad(x):
        raise ValueError('noninteger JSON '+x)
    return json.loads(raw, object_pairs_hook=pairs, parse_float=bad, parse_constant=bad)

def exact(a,b):
    if type(a) is not type(b): return False
    if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def execute(rows, ports, operation=None):
    env = dict(ports)
    for n,op,a,b in rows:
        a = a if type(a) is int else env[a]
        b = b if type(b) is int else env[b]
        env[n] = operation(op,a,b) if operation else a*b if op=='*' else a+b if op=='+' else a-b
    return env

def ledger(rows, free, output):
    known=set(free); by={}
    for n,op,a,b in rows:
        need(n not in known and op in ['+','-','*'], 'row schema')
        need(all(type(v) is int or type(v) is str and v in known for v in [a,b]), 'closure')
        known.add(n); by[n]=(a,b)
    live=set(); todo=[output]
    while todo:
        n=todo.pop()
        if type(n) is int or n in live: continue
        live.add(n); todo.extend(by.get(n,()))
    need(live==set(by)|set(free), 'all rows and ports live')
    M=sum(row[1]=='*' for row in rows)
    return {'M':M,'A':len(rows)-M,'total':len(rows),'all_rows_and_ports_live':True}

class Ring:
    def __init__(self,names): self.names=names; self.zero=(0,)*len(names)
    def const(self,c): return {self.zero:c} if c else {}
    def var(self,n):
        e=list(self.zero);e[self.names.index(n)]=1
        return {tuple(e):1}
    def op(self,op,a,b):
        if type(a) is int: a=self.const(a)
        if type(b) is int: b=self.const(b)
        out={}
        if op=='*':
            for e,x in a.items():
                for f,y in b.items():
                    g=tuple(u+v for u,v in zip(e,f));out[g]=out.get(g,0)+x*y
        else:
            out=dict(a);sign=-1 if op=='-' else 1
            for e,y in b.items():out[e]=out.get(e,0)+sign*y
        return {e:c for e,c in out.items() if c}
    def add(self,a,b):return self.op('+',a,b)
    def sub(self,a,b):return self.op('-',a,b)
    def mul(self,a,b):return self.op('*',a,b)
    def square(self,a):return self.mul(a,a)
    def digest(self,a):return sha(json.dumps(sorted(a.items()),separators=(',',':')).encode())

def norm_cuts():
    r=Ring(['a','c','H','L']);v={n:r.var(n) for n in r.names}
    delta=r.add(r.square(v['a']),v['H'])
    direct=r.sub(r.square(r.add(r.mul(v['a'],v['c']),v['L'])),r.mul(delta,r.square(v['c'])))
    expanded=r.sub(r.add(r.mul(2,r.mul(r.mul(v['a'],v['c']),v['L'])),r.square(v['L'])),r.mul(v['H'],r.square(v['c'])))
    need(direct==expanded,'norm cancellation identity')
    return {'coefficient_entries':len(direct),'sha256':r.digest(direct)}

def transport_cuts():
    r=Ring(['q','w','C','K','F','T']);v={n:r.var(n) for n in r.names}
    def nt(w,t):
        return r.sub(r.add(r.mul(r.add(v['K'],w),v['C']),r.sub(v['q'],v['F'])),r.mul(t,r.sub(v['q'],1)))
    first=nt(r.mul(v['q'],v['w']),r.add(v['T'],r.mul(v['w'],v['C'])))
    second=nt(v['w'],v['T'])
    need(first==second,'balanced full transport pullback')
    original=nt(r.mul(r.square(v['q']),v['w']),r.add(v['T'],r.mul(r.add(v['q'],1),r.mul(v['w'],v['C']))))
    need(original==second,'balanced original unsheared transport')
    return {'coefficient_entries':len(second),'sha256':r.digest(second)}

def auxiliary_cuts():
    r=Ring(['c','f','R','o']);v={n:r.var(n) for n in r.names}
    # c*T=o+R*f is a proven exact divisibility relation on the counterfamily.
    current=r.sub(r.sub(r.mul(r.add(v['o'],r.mul(v['R'],v['f'])),v['f']),v['c']),r.mul(v['R'],r.square(v['f'])))
    old=r.sub(r.mul(v['o'],v['f']),v['c'])
    need(current==old,'actual Bezout numerator identity')
    return {'coefficient_entries':len(current),'sha256':r.digest(current)}

def pell(base,index):
    x,y=1,0
    u,v=base,1
    D=base*base-1
    while index:
        if index&1:x,y=x*u+D*y*v,x*v+y*u
        u,v=u*u+D*v*v,2*u*v
        index//=2
    return x,y

def component_samples():
    records=[]
    for base in [2,3,4,5,6,8]:
        Delta=base*base-1
        for R in [3]:
            _,c=pell(base,R)
            m=2*c*R
            f,z=pell(base,m)
            need(z % (c*c)==0,'aux i integral')
            i=z//(c*c);S=Delta*z
            ch,y=pell(S,R)
            need(ch % S==0,'odd auxiliary quotient')
            V=ch//S
            need((V+c)%f==0 and (V+R)%c==0,'two quotient congruences')
            o=(V+c)//f
            need((o+R*f)%c==0,'actual supplied T integral')
            T=(o+R*f)//c
            need(min(i,T,y)>0 and c*(T*f-1)-R*f*f==V,'positive actual quotient')
            need(Delta*f*f-(i*Delta*c*c)**2==Delta,'scaled strong')
            need(S*S*(V*V-y*y)+y*y==1,'actual auxiliary')
            records.append({'base':base,'R':R,'c':c,'main_auxiliary_index':m,'f_bits':f.bit_length(),'T_bits':T.bit_length()})
    return records

def verify(root):
    for n,h in PINS.items():need(sha((root/n).read_bytes())==h,'pin '+n)
    parent=load((root/'complete84_scaled_strong_output.json').read_bytes())['packet']
    old=parent['source'];by={row[0]:row for row in old}
    required={
     'n2':['n2','*','Lbig','q'], 'Lbig':['Lbig','*','q','q'],
     'sn2':['sn2','*','s','n2'], 'wn2':['wn2','*','w','q'],
     'R10b':['R10b','+','eta','zeta'], 'R10a':['R10a','+','ksn2','eta'],
     'R12':['R12','+','UM','sn2'], 'cam2':['cam2','*','R10a','R12'],
     'A':['A','+','a_square','a4m5'], 'c2':['c2','*','R10a','R10a'],
     'Ac2':['Ac2','*','A','c2'], 'norm_main':['norm_main','-','L15','Ac2'],
     'kinner':['kinner','+','Kconstant','w'],
     'norm_transport':['norm_transport','-','transport_partial','local_rhs'],
     'aux_u_rhs':['aux_u_rhs','-','auxiliary_c_Tf','auxiliary_R_f2'],
     'aux_coefficient_root':['aux_coefficient_root','*','i','Ac2'],
     'R16':['R16','*','aux_coefficient_root','aux_coefficient_root'],
     'norm_strong':['norm_strong','-','scaled_f_square','R16'],
     'polynomial':['polynomial','-','seven_units','A']}
    need(all(by[n]==row for n,row in required.items()),'actual parent producers')
    need([r[0] for r in old if 'n2' in r[2:]]==['sn2'],'private q-cube consumer')
    factors=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']
    variants={};numeric=0
    for j in [1,2]:
        rows=[]
        for row in old:
            if row[0]=='n2':continue
            row=row[:]
            if row[0]=='sn2':row[3]='Lbig'
            if j==2 and row[0]=='wn2':row[3]='Lbig'
            rows.append(row)
        count=ledger(rows,parent['free'],parent['output'])
        need(count['M']==46 and count['A']==37 and count['total']==83,'whole ledger')
        diagnostics=[]
        for beta,ell in [(15,8),(31,10),(63,12),(127,14)]:
            ring=Ring(['t']);t=ring.var('t')
            ports={n:t for n in parent['free']}
            fixed=dict(zip(parent['fixed_numerals'],[beta,7,ell,5,6,12]))
            need(set(fixed)=={'Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF'},'numeral order')
            ports.update({n:ring.const(v) for n,v in fixed.items()})
            env=execute(rows,ports,ring.op)
            degrees={n:max(e[0] for e in env[n]) for n in factors}
            expected=dict(zip(factors,[2*j+16,2*j+13,5*j+22,4*j+46,j+5,2,4*j+34]))
            need(degrees==expected,'all factor degrees')
            poly=env[parent['output']];degree=max(e[0] for e in poly)
            leading=-(2**17)*(ell+3)*beta**(18*j+62)*(beta-2)**2*(beta+1)**2
            need(degree==18*j+138 and poly[(degree,)]==leading,'uniform degree-line specialization')
            diagnostics.append({'Bm1':beta,'twice_cell_bits':ell,'factor_degrees':degrees,'degree':degree,'leading_coefficient':leading,'whole_polynomial_sha256':ring.digest(poly)})
        for case in range(32):
            values={n:Fraction(((case+3)*(i+2))%13-6,1+(case+i)%3) for i,n in enumerate(parent['free'])}
            values.update(Bm1=15,Jrep=1+case%3)
            newenv=execute(rows,values);q=newenv['q'];C=newenv['marked_rhs']
            oldvalues=dict(values);oldvalues['s']=values['s']/q
            if j==2:
                oldvalues['w']=q*values['w']
                oldvalues['transport_quotient']=values['transport_quotient']+values['w']*C
            oldenv=execute(old,oldvalues)
            need(all(oldenv[n]==newenv[n] for n in factors+[parent['output']]),'complete parent pullback')
            numeric+=1
        variants['X_q'+str(j)+'_Y_q2']={
         'source':rows,'free':parent['free'],'witnesses':parent['witnesses'],
         'fixed_numerals':parent['fixed_numerals'],'ordinary_input':'x','output':parent['output'],
         'ledger':count,'exact_degree':18*j+138,'factor_exact_degrees':expected,
         'degree_diagnostics':diagnostics,
         'uniform_diagonal_leader':'-2^17*(ell+3)*beta^(18*j+62)*(beta-2)^2*(beta+1)^2',
         'domain':'18 strictly positive integer witnesses; inherited fixed compiler numerals',
         'language_status':'Refuted: every positive input on every inherited modified compiler slice has a full positive zero.'}
    return {'schema':'complete83-squared-scale-collapse-v1','source_sha256':sha(Path(__file__).read_bytes()),
            'pins':PINS,'variants':variants,'norm_cancellation':norm_cuts(),
            'transport_identities':transport_cuts(),'auxiliary_identity':auxiliary_cuts(),
            'auxiliary_components':component_samples(),'whole_parent_pullback_assignments':numeric,
            'scope':'Transfer of the pinned historical all-input theorem; no compiler history or enormous full zero materialized; no predecessor code executed.'}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',required=True,type=Path)
    mode=p.add_mutually_exclusive_group(required=True);mode.add_argument('--output',type=Path);mode.add_argument('--expect',type=Path)
    args=p.parse_args();receipt=verify(args.root)
    if args.expect:need(exact(receipt,load(args.expect.read_bytes())),'receipt mismatch')
    else:
        with args.output.open('x') as f:f.write(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'status':'PASS_REFUTED_SQUARED_SCALE_CHARTS','counts':{n:v['ledger'] for n,v in receipt['variants'].items()},'degrees':[v['exact_degree'] for v in receipt['variants'].values()]},sort_keys=True))

if __name__=='__main__':main()
