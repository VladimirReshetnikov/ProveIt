#!/usr/bin/env python3
"""Audit emitted formulas using residues of the four actual fixed integers.

Standard library only. This verifier imports no builder. Its primary norm
check multiplies all eight conjugates in an eight-dimensional quotient ring,
independently of the optimized scalar-norm circuit. Modular evaluations are
transcription/binding diagnostics, not consistency witnesses or semantic proofs.
"""
from pathlib import Path
from hashlib import sha256
from itertools import product
import gzip
import json
import random

ROOT=Path(__file__).resolve().parents[1]
VARIANT='wang943-mixed125-external-padding-5pow9'
ALIASES={'beta':'beta','Bm1':'beta','K0':'K','Kconstant':'K','MC':'MC','MF':'MF_source'}

def require(condition,message):
    if not condition: raise ValueError(message)

def evaluate(packet,values,p):
    a={k:v%p for k,v in values.items()}
    names=set(a)
    for name,op,left,right in packet['source']:
        require(name not in names,'duplicate gate '+name)
        require(op in ('+','-','*'),'unknown operation')
        x=left if isinstance(left,int) else a[left]
        y=right if isinstance(right,int) else a[right]
        a[name]=(x+y if op=='+' else x-y if op=='-' else x*y)%p
        names.add(name)
    return a

def base(w,f,p):
    q=(f['beta']*w['J']+1)%p
    X=w['w']*q%p;Y=w['s']*pow(q,3,p)%p;E=X*Y%p
    k=(w['eta']+w['zeta'])%p;c=(k*Y+w['eta'])%p
    a=(E+Y)%p;H=(4*a+3)%p;Delta=(a*a+H)%p
    Cw=(q-w['F']-w['alpha'])%p
    R=(((q-1)*(q-w['F'])+w['alpha'])*(q*q-1)+(f['MC']+q*f['MF'])*w['J'])%p
    Nk=(k-w['h']*E-R)%p
    Nt=((f['K0']+w['w'])*Cw+q-w['F']-w['z']*(q-1))%p
    return dict(q=q,X=X,Y=Y,E=E,k=k,c=c,a=a,H=H,Delta=Delta,Cw=Cw,R=R,Nk=Nk,Nt=Nt)

def direct_norm(w,f,p,weight='square',carrier='unweighted'):
    a=base(w,f,p);c=a['c'];Delta=a['Delta'];H=a['H'];k=a['k']
    ell=a['E']*k*a['Y']%p;A=(1+ell*(ell+k))%p
    G=(1+Delta*c*c)%p;b0=(a['X']+a['a']*c)%p
    I=w['i']*c*c%p;D=(1+Delta*I*I)%p
    Q=pow(Delta*I,2,p);d=(Q-1)%p
    v=c*w['T']%p;b=(c+a['R']*D)%p
    e=(Q*(D*v*v+b*b)-1)%p;Baux=2*Q*v*b%p
    M=pow(k*I+w['T'],2,p) if weight=='square' else (k*I*I+w['T']**2)%p
    L=(1+H*M)%p;S=((L*b0 if carrier=='weighted' else b0)+H*w['r'])%p
    rad=(G,A,D)
    def multiply(x,y):
        z=[0]*8
        for i,xi in enumerate(x):
            for j,yj in enumerate(y):
                v=xi*yj
                for mask,rr in zip((1,2,4),rad):
                    if i&j&mask:v=v*rr%p
                z[i^j]=(z[i^j]+v)%p
        return z
    answer=[1]+[0]*7
    for su,st,sf in product((-1,1),repeat=3):
        root=[S,-su*L,-st*H*M,0,0,0,0,0]
        term=[d*x%p for x in multiply(root,root)]
        term[0]=(term[0]-H*H*e)%p
        term[4]=(term[4]+sf*H*H*Baux)%p
        answer=multiply(answer,term)
    require(not any(answer[1:]),'formal conjugate product did not descend')
    return a['Nk'],a['Nt'],answer[0]

def verify_baseline(packet,w,ports,p):
    if packet['name'].startswith('product67'):
        rename={'Jrep':'J','transport_quotient':'z','auxiliary_quotient':'T',
                'tau_root':'tau','y_aux':'y'}
        common={rename.get(k,k):v for k,v in w.items()}
        a=base(common,ports,p);c=a['c'];Delta=a['Delta'];X=a['X'];Y=a['Y'];k=a['k']
        Dmain=X+a['a']*c+common['gamma']*a['H']
        V=c*(common['T']*common['f']-1)-a['R']*common['f']**2
        Ka=(common['i']*Delta*c*c)**2
        factors=[common['tau']**2-(X*Y*Y)*(X*Y*Y+1)*k*k,
                 Dmain*Dmain-Delta*c*c,Ka*(V*V-common['y']**2)+common['y']**2,
                 a['Nk'],a['Nt'],Delta*common['f']**2-Ka]
        expected=1
        for x in factors:expected=expected*x%p
        expected=(expected-Delta)%p
        inp=dict(w);inp.update({k:ports[{'Bm1':'beta','Kconstant':'K0'}.get(k,k)] for k in packet['fixed_numerals']})
        got=evaluate(packet,inp,p)
        require(got[packet['output']]==expected,'P67 fixed formula mismatch')
    else:
        a=base(w,ports,p);c=a['c'];Delta=a['Delta'];Y=a['Y'];k=a['k']
        ell=a['E']*k*Y;Dmain=a['X']+a['a']*c+w['gamma']*a['H']
        V=w['o']*w['f']-c;U=w['j']*c-a['R'];I=w['i']*c*c
        A0=Delta*(w['f']**2-1)
        expect=[w['tau']**2-ell*(ell+k)-1,Dmain*Dmain-Delta*c*c-1,
                A0*(V*V-w['y']**2)+w['y']**2-1,a['Nk']-1,
                (ports['K0']+w['w'])*a['Cw']-w['F']-w['z']*(a['q']-1),
                I*I-A0,U-V]
        inp=dict(w);inp.update(ports);got=evaluate(packet,inp,p)
        read=lambda x:x if isinstance(x,int) else got[x]
        result=[(read(x)-read(y))%p for x,y in packet['comparisons']]
        require(result==[x%p for x in expect],'Retained59 fixed formula mismatch')

def main():
    binding=json.loads((ROOT/'coefficients/COEFFICIENT_BINDING.json').read_text())
    require(binding['variant']==VARIANT,'tuple identity')
    fixed={}
    for rec in binding['audit']['files']:
        blob=(ROOT/'coefficients'/rec['path']).read_bytes();raw=gzip.decompress(blob)
        require(sha256(raw).hexdigest()==rec['sha256'],'coefficient hash '+rec['name'])
        require(sha256(blob).hexdigest()==rec['gzip_sha256'],'gzip hash '+rec['name'])
        fixed[rec['name']]=int.from_bytes(raw,'little')
    packets={p.stem:json.loads(p.read_text()) for p in (ROOT/'arithmetic').glob('hybrid12_*.json')}
    baselines=[json.loads(p.read_text()) for p in (ROOT/'baselines').glob('*.json')]
    for packet in list(packets.values())+baselines:
        require(packet['coefficient_binding']['variant']==VARIANT,'mixed tuple metadata')
        require(all(n in ALIASES for n in packet['fixed_numerals']),'unbound port')
    rng=random.Random(20261022);comparisons=0;baseline_comparisons=0
    for prime in (1000000007,1000000009,998244353):
        ports={n:fixed[k]%prime for n,k in {'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}.items()}
        for _ in range(16):
            w={n:rng.randrange(1,24) for n in packets['hybrid12_square_unweighted_product']['witnesses']}
            for weight,carrier in [('square','unweighted'),('square','weighted'),('sum','weighted')]:
                Nk,Nt,N=direct_norm(w,ports,prime,weight,carrier)
                prefix='hybrid12_'+weight+'_'+carrier
                for kind in ('system','product','sos'):
                    packet=packets[prefix+'_'+kind];vals=evaluate(packet,dict(w,**ports),prime)
                    if kind=='product':expect=(Nk*Nt*(1+N)-1)%prime;got=vals['polynomial']
                    elif kind=='sos':expect=((Nk-1)**2+(Nt-1)**2+N*N)%prime;got=vals['sos']
                    else:
                        expect=[(Nk-1)%prime,(Nt-1)%prime,N]
                        read=lambda x:x if isinstance(x,int) else vals[x]
                        got=[(read(x)-read(y))%prime for x,y in packet['comparisons']]
                    require(got==expect,'actual fixed norm mismatch '+prefix+' '+kind)
                    comparisons+=1
            for packet in baselines:
                bv={n:rng.randrange(1,24) for n in packet['witnesses']}
                verify_baseline(packet,bv,ports,prime);baseline_comparisons+=1
    report={'status':'PASS','actual_materialized_coefficients':4,'coefficient_variant':VARIANT,
            'primes':[1000000007,1000000009,998244353],'tuples_per_prime':16,
            'hybrid_fixed_instance_comparisons':comparisons,'baseline_fixed_instance_comparisons':baseline_comparisons,
            'independent_representation':'Eight-component quotient-ring conjugate product; no builder imported.',
            'scope':'Modular transcription and binding audit. Not a solution search or proof of consistency.'}
    (ROOT/'verification/FIXED_INSTANCE_CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
