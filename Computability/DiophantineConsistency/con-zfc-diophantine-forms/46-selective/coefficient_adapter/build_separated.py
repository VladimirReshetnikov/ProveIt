#!/usr/bin/env python3
"""Parity-separated factorized receiver coefficients: complete finite recipe.

Attribution: source40 factorized Wang receivers and geometry; source44
aggregate complement clauses. New: reverse label convention, one-bit
separation of empty payloads, removal of four occupancy copies, and
positive coefficients for auxiliary payload increments.
"""
import json,math,gzip,hashlib
from pathlib import Path
import build_factorized as old
HERE=Path(__file__).resolve().parent
M=44
H=29
SCALE=1<<H
MOD=1<<M
LABEL_BITS=42
LOW_MASK=(1<<LABEL_BITS)-1
WIDTHS=(11,10,11,10)
STARTS=(0,11,21,32)
ANCHORS=(1203,1807)
BARE=(33,68,664,1268)

def require(ok,message):
    if not ok: raise ValueError(message)

def label_vector(t):
    w,n,e,s=t
    return (2*w)+(n<<11)+(2*e<<21)+(s<<32)

def recipe():
    tiles,ir,il=old.language()
    ce={}
    for i,t in enumerate(tiles):
        vec=label_vector(t)
        require(0<=vec<1<<LABEL_BITS,"tile label bound")
        ce[i]=1+255*old.GATE_R*(i!=ir)+255*old.GATE_L*(i!=il)+old.GATE_B*(i not in (ir,il))+SCALE*(1+vec)
    for s in range(4):
        for j in range(WIDTHS[s]):
            ce[old.OFFSETS[s]+j]=SCALE*(1<<(STARTS[s]+j))
    for j in range(8):
        vr=(1<<(j+1))+(1<<(33+j))
        vl=(1<<(22+j))+(1<<(33+j))
        ce[old.QR[j]]=(1<<j)*old.GATE_R+SCALE*vr
        ce[old.QL[j]]=(1<<j)*old.GATE_L+SCALE*vl
    ce[old.BSYM]=old.GATE_B+SCALE*((1<<11)+(1<<32))
    ce[old.OFFSETS[0]]+=SCALE*(1<<LABEL_BITS)
    for e in ANCHORS:
        ce[e]=SCALE*(1<<LABEL_BITS)
    for e in old.DUMMY:ce[e]=0
    mu=510+(1<<17)+(1<<26)+(1<<28)+SCALE*(MOD-1)
    dc={e:1 for e in BARE}
    for e,c in ce.items():
        if c:
            for T in (old.T1,old.T2):
                dc[T-e]=dc.get(T-e,0)+c
    targets=[(528+j,{495+j},set(),{528+j}) for j in range(10)]
    targets += [(585+j,{517+j},{539+j},set()) for j in range(11)]
    targets += [(1203,{539},set(),{1203}),(1807,{539},set(),{1807})]
    return dict(tiles=tiles,ir=ir,il=il,ce=ce,mu=mu,dc=dc,targets=targets)

def aux(data,qr,ql,u):
    value=sum(data['ce'][old.QR[j]] for j in range(8) if qr>>j&1)
    value+=sum(data['ce'][old.QL[j]] for j in range(8) if ql>>j&1)
    return value+data['ce'][old.BSYM]*u

def certify_local(data):
    count=mutations=0
    for i,t in enumerate(data['tiles']):
        if i==data['ir']:
            variants=(((256+q,u,0,512+2*q+u),q,0,u) for q in range(256) for u in (0,1))
        elif i==data['il']:
            variants=(((0,u,512+q,512+2*q+u),0,q,u) for q in range(256) for u in (0,1))
        else:variants=[(t,0,0,0)]
        for tile,qr,ql,u in variants:
            base=data['ce'][i]+aux(data,qr,ql,u)
            W=MOD-1-label_vector(tile)
            require((base+SCALE*W)&data['mu']==0,"occupied decoder")
            require(W>>LABEL_BITS==3,"three anchors")
            require((W&1)==1 and ((W>>21)&1)==1,"occupied horizontal separator")
            for bit in range(LABEL_BITS):
                changed=(W^(1<<bit))-(1<<LABEL_BITS) if bit==0 else W^(1<<bit)
                require((base+SCALE*changed)&data['mu']!=0,"copy mutation")
                mutations+=1
            # Each of the two standalone physical anchors has equal weight.
            require((base+SCALE*(W-(1<<LABEL_BITS)))&data['mu']!=0,"anchor mutation")
            mutations+=2
            count+=1
    empty=0
    for qr in range(256):
        for ql in range(256):
            for u in (0,1):
                V=(2*qr)+(u<<11)+(2*ql<<21)+((2*qr+2*ql+u)<<32)
                require(0<=V<1<<LABEL_BITS,"empty increment bound")
                W=(-V)%MOD
                require((aux(data,qr,ql,u)+SCALE*W)&data['mu']==0,"empty decoder")
                require(W&1==0,"empty west separator")
                require(W>>LABEL_BITS in (0,3),"empty anchor count")
                require(V==0 or W>>LABEL_BITS>2,"empty ghost unrepresentable")
                empty+=1
    return dict(occupied=count,single_physical_bit_mutations=mutations,
                empty_payloads=empty,occupied_west_parity=1,
                occupied_east_parity=1,empty_west_parity=0,empty_accepted_payloads=1,
                shared_anchor_source=539,standalone_anchors=list(ANCHORS))

def finite_geometry(data,b):
    E=set(data['ce']); dc=data['dc'];checks=0
    for t,a,c,y in data['targets']:
        for e in E:
            require(dc.get(t-e,0)==int(e in a),(t,e,"DC"))
            require(int(e+old.SHIFT==t)==int(e in c),(t,e,"DR"))
            require(int(e==t)==int(e in y),(t,e,"temporal"))
            checks+=3
    for T in (old.T1,old.T2):
        for e in E:
            require(dc.get(T-e,0)==data['ce'][e],(T,e,"clause"))
            require(e+old.SHIFT!=T,(T,e,"DR-clause")); checks+=2
    require({old.T1-e for e in E}.isdisjoint({old.T2-e for e in E}),"clean bands")
    require({1203-e for e in E}&{1807-e for e in E}=={0},"anchors")
    mass=(len(E)+2)*(2*sum(data['ce'].values())+6)
    require(max(4*mass+8,2*data['mu']+4,16)<1<<b,"uniform carry threshold")
    padding_count=len(E)-(1+2*data['mu'].bit_count()+len(data['targets']))
    maxprod=max(dc)+max(E)
    padding={};rem=padding_count;e=maxprod+1
    while rem:
        size=min(rem,b-2);padding[e]=(1<<size)-1;rem-=size;e+=1
    minL=e
    if minL%2==0:minL+=1
    require(2*max(padding.values())+4<1<<b,"padding bound")
    return dict(b=b,minL=minL,maxprod=maxprod,padding=padding,
                padding_count=padding_count,mu_population=data['mu'].bit_count(),
                checks=checks,carry_threshold_bits=(4*mass+8).bit_length(),
                mass=str(mass),sum_ce=str(sum(data['ce'].values())))

def materialize(data,a,c):
    b,L,d=c['b'],c['L'],c['d'];B=1<<d
    DC=sum(v<<(b*e) for e,v in data['dc'].items());DR=1<<(b*old.SHIFT)
    MC=B-1-sum(1<<(b*e) for e in data['ce'] if e!=1)-(2<<(b*old.DUMMY[0]))
    MF=4+sum(data['mu']<<(b*T) for T in (old.T1,old.T2))
    MF+=sum(1<<(b*t) for t,*_ in data['targets'])
    MF+=sum(v<<(b*e) for e,v in a['padding'].items())
    require(0<DC<B and 0<MC<B-1 and 0<MF<B-1,"coefficient bounds")
    require(MC.bit_count()==d-len(data['ce']) and MF.bit_count()==len(data['ce']),"populations")
    require(MC%4==2 and MF%8==4,"low congruences")
    out=HERE/'separated_coefficients';out.mkdir(exist_ok=True)
    result=[]
    for k,v in dict(beta=B-1,K=DC+B*DR,MC=MC,MF_source=MF+B-1).items():
        raw=v.to_bytes((v.bit_length()+7)//8,'little');z=gzip.compress(raw,mtime=0)
        (out/(k+'.bin.gz')).write_bytes(z)
        require(int.from_bytes(gzip.decompress(z),'little')==v,"round trip")
        result.append(dict(port=k,bits=v.bit_length(),raw_bytes=len(raw),
                           gzip_bytes=len(z),sha256=hashlib.sha256(raw).hexdigest()))
    return result

def fixed_controller(data,a=None):
    b,L,lam=89,4831,106261
    d=b*L;step=lam-1
    require(old.prime(lam),"prime controller")
    fac=old.factor(d)
    require(fac=={89:1,4831:1},"d factorization")
    order=old.order(pow(2,d,d),d)
    require(order==26565 and step%order==0,"order modulo d")
    lift=pow(2,d*step,lam*lam)
    require(lift==8376873414 and lift%lam==1 and lift!=1,"lifting valuation")
    units={p:old.residue(data,b,L,p) for p in (*fac,lam)}
    require(all(all(row[1:]) for row in units.values()),"controller units")
    c=dict(b=b,L=L,d=d,factorization=fac,order_mod_d=order,lam=lam,
           step=step,lift=lift,unit_residues=units)
    return finite_geometry(data,b),c

if __name__=='__main__':
    data=recipe()
    mass=(len(data['ce'])+2)*(2*sum(data['ce'].values())+6)
    b=max(4*mass+8,2*data['mu']+4,16).bit_length()
    if b%2==0:b+=1
    a,c=fixed_controller(data,dict(b=b))
    p=materialize(data,a,c)
    local=certify_local(data)
    result=dict(description="Parity-separated factorized receivers",
                source_pin="124c07c0b77a9e20e84676514d8b1ff78536ea3f",
                local_decoder=local,geometry=a,controller=c,payload=p,
                support_size=len(data['ce']),selectors=len(data['tiles']),
                total_raw_bytes=sum(x['raw_bytes'] for x in p),
                total_gzip_bytes=sum(x['gzip_bytes'] for x in p))
    (HERE/'separated_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
