#!/usr/bin/env python3
"""Experimental factorized Wang compiler: finite coefficient construction.

This script checks local linear identities and numeric controller conditions.
The accompanying proof note documents the decoder extension, which is not
an end-to-end formal proof-assistant certificate.
"""
import json,math,gzip,hashlib
from pathlib import Path
from itertools import product

HERE=Path(__file__).resolve().parent
ROWS=json.loads((HERE/'k215_transitions.json').read_text())['transitions']
OFFSETS=(539,528,517,495)
ANCHORS=(600,1203,1807)
T1,T2=2409,3015
SHIFT=46
BARE=(33,68,603,1207)
DUMMY=(507,508)
QR=tuple(range(567,575)); QL=tuple(range(575,583)); BSYM=583
GATE_R=1<<9; GATE_L=1<<18; GATE_B=1<<27
WEIGHT=lambda j: 1<<(29+2*j)

def language():
    right=sorted({t for q,b,v,m,t in ROWS if m==1})
    left=sorted({t for q,b,v,m,t in ROWS if m==-1})
    hd=lambda q,b:512+2*q+b
    rr=lambda q:256+q
    ll=lambda q:512+q
    ts=set((0,hd(q,b),rr(t),v) if m==1 else (ll(t),hd(q,b),0,v)
           for q,b,v,m,t in ROWS)
    ts.update((0,hd(215,b),0,hd(215,b)) for b in (0,1))
    ts.update((0,b,0,b) for b in (0,1))
    ts.update((0,c,0,6) for c in (0,1,hd(215,0),hd(215,1)))
    ts.update([(2,2,2,0),(2,3,3,1),(3,4,4,hd(93,0)),(4,4,4,0)])
    ts.update((1,6,1,c) for c in (2,3,4))
    ts.update((a,5,b,5) for a in (0,1,4) for b in (0,1,2))
    start,forbidden=(2,3,3,1),(5,0,0,0)
    recvR,recvL=(256,0,0,512),(0,0,512,512)
    ts.update([forbidden,recvR,recvL])
    tiles=[start,forbidden]+sorted(ts-{start,forbidden})
    assert len(tiles)==457
    return tiles,tiles.index(recvR),tiles.index(recvL)

def recipe():
    tiles,ir,il=language()
    ce={}
    for i,tile in enumerate(tiles):
        c=1
        c+=255*GATE_R*(i!=ir)+255*GATE_L*(i!=il)+GATE_B*(i not in (ir,il))
        c+=sum(WEIGHT(11*s+j) for s,x in enumerate(tile) for j in range(11)
               if ((x+1024)>>j)&1)
        c+=sum(WEIGHT(j) for j in range(44,47))
        ce[i]=c
    for s in range(4):
        for j in range(11):ce[OFFSETS[s]+j]=WEIGHT(11*s+j)
    for j in range(8):
        ce[QR[j]]=(1<<j)*GATE_R+WEIGHT(j)+WEIGHT(33+j+1)
        ce[QL[j]]=(1<<j)*GATE_L+WEIGHT(22+j)+WEIGHT(33+j+1)
    ce[BSYM]=GATE_B+WEIGHT(11)+WEIGHT(33)
    for j,e in enumerate(ANCHORS):ce[e]=WEIGHT(44+j)
    for e in DUMMY:ce[e]=0
    assert len(ce)==523
    mu=510+(1<<8)*GATE_R+(1<<8)*GATE_L+2*GATE_B+sum(WEIGHT(j) for j in range(47))
    dc={e:1 for e in BARE}
    for e,c in ce.items():
        if c:
            for T in (T1,T2):dc[T-e]=dc.get(T-e,0)+c
    targets=[(528+j,{495+j},set(),{528+j}) for j in range(11)]
    targets += [(585+j,{517+j},{539+j},set()) for j in range(11)]
    targets += [(1203,{600},set(),{1203}),(1807,{600},set(),{1807})]
    return dict(tiles=tiles,ir=ir,il=il,ce=ce,mu=mu,dc=dc,targets=targets)

def audit(data):
    E=set(data['ce']);dc=data['dc'];checks=0
    for t,a,c,y in data['targets']:
        for e in E:
            assert dc.get(t-e,0)==int(e in a),(t,e,'DC')
            assert int(e+SHIFT==t)==int(e in c),(t,e,'DR')
            assert int(e==t)==int(e in y),(t,e,'temporal')
            checks+=3
    for T in (T1,T2):
        for e in E:
            assert dc.get(T-e,0)==data['ce'][e],(T,e,'clause')
            assert e+SHIFT!=T
            checks+=2
    assert {T1-e for e in E}.isdisjoint({T2-e for e in E})
    assert {1203-e for e in E}&{1807-e for e in E}=={0}
    mass=(len(E)+2)*(2*sum(data['ce'].values())+6)
    threshold=max(4*mass+8,2*data['mu']+4,16)
    b=threshold.bit_length()
    if b%2==0:b+=1
    pc_initial=1+2*data['mu'].bit_count()+len(data['targets'])
    padding_count=len(E)-pc_initial
    maxprod=max(dc)+max(E)
    padding={};rem=padding_count;e=maxprod+1
    while rem:
        size=min(rem,b-2);padding[e]=(1<<size)-1;rem-=size;e+=1
    minL=e
    if minL%2==0:minL+=1
    return dict(b=b,minL=minL,maxprod=maxprod,padding=padding,
                padding_count=padding_count,mu_population=data['mu'].bit_count(),
                checks=checks,carry_threshold_bits=threshold.bit_length())

def prime(n):
    return n>=2 and all(n%p for p in range(2,math.isqrt(n)+1))

def factor(n):
    f={};p=2
    while p*p<=n:
        while n%p==0:f[p]=f.get(p,0)+1;n//=p
        p+=1
    if n>1:f[n]=1
    return f

def order(a,m):
    assert math.gcd(a,m)==1
    n=m
    for p in factor(m):n=n//p*(p-1)
    for p in factor(n):
        while n%p==0 and pow(a,n//p,m)==1:n//=p
    return n

def residue(data,b,L,p):
    rho=pow(2,b,p);B=pow(2,b*L,p)
    DC=sum((c%p)*pow(rho,e,p) for e,c in data['dc'].items())%p
    DR=pow(rho,SHIFT,p)
    return B,(B*B-1)%p,(1+B*DC+B*B*(DR+1))%p

def controller(data,a):
    b=a['b']
    for L in range(a['minL'],a['minL']+500,2):
        d=b*L
        fac=factor(d)
        if any(not all(residue(data,b,L,p)[1:]) for p in fac):continue
        period=order(pow(2,d,d),d)
        for m in range(1,2000):
            lam=m*period+1
            if lam<=3 or not prime(lam) or d%lam==0:continue
            if not all(residue(data,b,L,lam)[1:]):continue
            lift=pow(2,d*(lam-1),lam*lam)
            if lift==1:continue
            assert lift%lam==1
            return dict(b=b,L=L,d=d,factorization=fac,order_mod_d=period,
                        lam=lam,step=lam-1,lift=lift,
                        unit_residues={p:residue(data,b,L,p) for p in (*fac,lam)})
    raise ValueError('controller not found')

def materialize(data,a,c):
    b,L,d=c['b'],c['L'],c['d'];B=1<<d
    DC=sum(v<<(b*e) for e,v in data['dc'].items());DR=1<<(b*SHIFT)
    MC=B-1-sum(1<<(b*e) for e in data['ce'] if e!=1)-(2<<(b*DUMMY[0]))
    MF=4+sum(data['mu']<<(b*T) for T in (T1,T2))
    MF+=sum(1<<(b*t) for t,*_ in data['targets'])
    MF+=sum(v<<(b*e) for e,v in a['padding'].items())
    assert 0<DC<B and 0<MC<B-1 and 0<MF<B-1
    assert MC.bit_count()==d-len(data['ce']) and MF.bit_count()==len(data['ce'])
    assert MC%4==2 and MF%8==4
    out=HERE/'experimental_coefficients';out.mkdir(exist_ok=True)
    result=[]
    for k,v in dict(beta=B-1,K=DC+B*DR,MC=MC,MF_source=MF+B-1).items():
        raw=v.to_bytes((v.bit_length()+7)//8,'little');z=gzip.compress(raw,mtime=0)
        (out/(k+'.bin.gz')).write_bytes(z)
        result.append(dict(port=k,bits=v.bit_length(),raw_bytes=len(raw),
                           gzip_bytes=len(z),sha256=hashlib.sha256(raw).hexdigest()))
    return result

def check_decoder():
    # Exact occupied-state finite gate audit; gates constrain payloads independently.
    gates=0
    for nr in (0,1):
        actual=[q for q in range(256) if not ((255*nr+q)&256)]
        assert actual==(list(range(256)) if nr==0 else [0]);gates+=256
    for nb in (0,1):
        assert [x for x in (0,1) if not ((nb+x)&2)]==([0,1] if nb==0 else [0]);gates+=2
    assert [n for n in range(458) if not (n&510)]==[0,1]
    return dict(gate_checks=gates,selector_bound=457,
                local_soundness='Proof note required for empty-cell auxiliary bits.')

if __name__=='__main__':
    data=recipe();a=audit(data);c=controller(data,a);p=materialize(data,a,c)
    result=dict(description='Factorized receiver compiler; experimental adapter',
                local_decoder=check_decoder(),geometry=a,controller=c,payload=p,
                support_size=len(data['ce']),selectors=len(data['tiles']),
                total_raw_bytes=sum(x['raw_bytes'] for x in p),
                total_gzip_bytes=sum(x['gzip_bytes'] for x in p))
    (HERE/'factorized_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
