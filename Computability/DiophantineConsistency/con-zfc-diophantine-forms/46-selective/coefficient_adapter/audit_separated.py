#!/usr/bin/env python3
"""Independent finite audit of the separated coefficient tuple.

No import of build_separated.py or build_factorized.py. Reconstructs the
literal language, transformed mode coefficients, interface, controller and
actual integer bytes. Checks are active under python -O.
"""
from pathlib import Path
from hashlib import sha256
from math import gcd,isqrt
import json,gzip
HERE=Path(__file__).resolve().parent

def req(x,msg):
    if not x: raise ValueError(msg)

def factor(n):
    r={};p=2
    while p*p<=n:
        while n%p==0:r[p]=r.get(p,0)+1;n//=p
        p+=1
    if n>1:r[n]=1
    return r

raw=(HERE/'k215_transitions.json').read_bytes()
req(sha256(raw).hexdigest()=='880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755','K215 hash')
actions=json.loads(raw)['transitions']
req(len(actions)==430 and len({(q,b) for q,b,v,m,t in actions})==430,'430 literal actions')
R=sorted({t for q,b,v,m,t in actions if m==1})
L=sorted({t for q,b,v,m,t in actions if m==-1})
req((len(R),len(L))==(199,45),'direction counts')
rr={q:6+j for j,q in enumerate(R)}
ll={q:205+j for j,q in enumerate(L)}
head=lambda q,b:2*q+2+b
tiles=set()
for q,b,v,m,t in actions:
    tiles.add((0,head(q,b),rr[t],v) if m==1 else (ll[t],head(q,b),0,v))
for b in (0,1):
    tiles.add((0,head(215,b),0,head(215,b)))
    tiles.add((0,b,0,b))
    for q in R:tiles.add((rr[q],b,0,head(q,b)))
    for q in L:tiles.add((0,b,ll[q],head(q,b)))
for t in (0,1,head(215,0),head(215,1)):tiles.add((0,t,0,438))
tiles.update(((2,434,2,0),(2,435,3,1),(3,436,4,head(93,0)),(4,436,4,0)))
for t in (434,435,436):tiles.add((1,438,1,t))
for w in (0,1,4):
    for e in (0,1,2):tiles.add((w,437,e,437))
tiles.add((5,0,0,0))
ordered=[(2,435,3,1),(5,0,0,0)]+sorted(tiles-{(2,435,3,1),(5,0,0,0)})
tbytes=(json.dumps(ordered,separators=(',',':'))+'\n').encode()
req(len(ordered)==943 and sha256(tbytes).hexdigest()=='66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f','literal Wang943')
hm={x:x for x in range(6)}
hm.update({rr[q]:256+q for q in R})
hm.update({ll[q]:512+q for q in L})
vm={0:0,1:1,434:2,435:3,436:4,437:5,438:6}
vm.update({head(q,b):512+2*q+b for q in range(216) for b in (0,1)})
expanded_old={(hm[w],vm[n],hm[e],vm[s]) for w,n,e,s in ordered}
receivers={(256+q,b,0,512+2*q+b) for q in R for b in (0,1)}
receivers|={(0,b,512+q,512+2*q+b) for q in L for b in (0,1)}
base=(expanded_old-receivers)|{(256,0,0,512),(0,0,512,512)}
start,forbidden=(2,3,3,1),(5,0,0,0)
modes=[start,forbidden]+sorted(base-{start,forbidden})
req(len(modes)==457,'mode count')
ir,il=modes.index((256,0,0,512)),modes.index((0,0,512,512))
offsets=(539,528,517,495)
widths=(11,10,11,10);starts=(0,11,21,32)
T=2**42;M=2**44;scale=2**29

def lv(tile):
    w,n,e,s=tile
    return 2*w+2048*n+(2*e)*2**21+s*2**32

weights={}
for i,t in enumerate(modes):
    weights[i]=1+255*2**9*(i!=ir)+255*2**18*(i!=il)+2**27*(i not in (ir,il))+scale*(1+lv(t))
for o,width,st in zip(offsets,widths,starts):
    for j in range(width):weights[o+j]=2**(29+st+j)
weights[539]+=scale*T
for j in range(8):
    weights[567+j]=2**(9+j)+scale*(2**(j+1)+2**(33+j))
    weights[575+j]=2**(18+j)+scale*(2**(22+j)+2**(33+j))
weights[583]=2**27+scale*(2**11+2**32)
weights[1203]=weights[1807]=scale*T
weights[507]=weights[508]=0
req(len(weights)==520,'support count')
mask=510+2**17+2**26+2**28+scale*(M-1)
req(mask.bit_count()==55,'clause population')
req([n for n in range(458) if not(n&510)]==[0,1],'selectors')
for inactive in (0,1):
    req([q for q in range(256) if not((255*inactive+q)&256)]==([0] if inactive else list(range(256))),'direction gates')
    req([u for u in (0,1) if not((inactive+u)&2)]==([0] if inactive else [0,1]),'symbol gate')

def aux(qr,ql,u):
    value=sum(weights[567+j] for j in range(8) if qr>>j&1)
    value+=sum(weights[575+j] for j in range(8) if ql>>j&1)
    return value+weights[583]*u

expansion=set();witnesses=mutations=0
for i,t in enumerate(modes):
    if i==ir:
        variants=(((256+q,u,0,512+2*q+u),q,0,u) for q in range(256) for u in (0,1))
    elif i==il:
        variants=(((0,u,512+q,512+2*q+u),0,q,u) for q in range(256) for u in (0,1))
    else:variants=[(t,0,0,0)]
    for tile,qr,ql,u in variants:
        z=T-1-lv(tile)
        req(0<=z<T and z&1==1 and (z>>21)&1==1,'occupied copied labels')
        total=weights[i]+aux(qr,ql,u)+weights[1203]+weights[1807]
        used=[]
        for o,width,st in zip(offsets,widths,starts):
            for j in range(width):
                bit=(z>>(st+j))&1
                total+=weights[o+j]*bit
                used.append((o+j,bit))
        req(total&mask==0,'physical occupied clause')
        for pos,bit in used+[(1203,1),(1807,1)]:
            corrupted=total+weights[pos]*(1-2*bit)
            req(corrupted&mask!=0,'single physical bit corruption')
            mutations+=1
        witnesses+=1;expansion.add(tile)
req(len(expansion)==1479 and expanded_old<=expansion,'expansion set')
east={t[2] for t in expansion};west={t[0] for t in expansion}
extras=expansion-expanded_old
req(len(extras)==536,'extra receiver count')
for w,n,e,s in extras:req(w not in east or e not in west,'unmatched extra')
req({t for t in expansion if t[0] in east and t[2] in west}==expanded_old-{forbidden},'exact trimmed language')

empty_checked=0
for qr in range(256):
    for ql in range(256):
        for u in (0,1):
            V=2*qr+2048*u+(2*ql)*2**21+(2*qr+2*ql+u)*2**32
            req(0<=V<T and V%2==0,'empty increment bound')
            W=(-V)%M
            westbit=W&1
            req(westbit==0,'empty copied parity')
            if V:
                req(W//T==3 and W//T>2+westbit,'empty ghost impossible')
            else:req(qr==ql==u==W==0,'unique zero empty')
            empty_checked+=1

E=set(weights);dc={s:1 for s in (33,68,664,1268)}
for e,c in weights.items():
    for target in (2409,3015):dc[target-e]=dc.get(target-e,0)+c
dc={e:c for e,c in dc.items() if c}
targetrows=[(528+j,{495+j},set(),{528+j}) for j in range(10)]
targetrows += [(585+j,{517+j},{539+j},set()) for j in range(11)]
targetrows += [(1203,{539},set(),{1203}),(1807,{539},set(),{1807})]
checks=0
for target,a,b,c in targetrows:
    for e in E:
        req(dc.get(target-e,0)==int(e in a),'DC basis')
        req(int(e+46==target)==int(e in b),'DR basis')
        req(int(e==target)==int(e in c),'temporal basis');checks+=3
for target in (2409,3015):
    for e in E:
        req(dc.get(target-e,0)==weights[e],'clause basis')
        req(e+46!=target,'DR clause');checks+=2
b,L,d,lam=89,4831,429959,106261
req({(2409-e)%L for e in E}.isdisjoint({(3015-e)%L for e in E}),'clean-band intersection')
req({(1203-e)%L for e in E}&{(1807-e)%L for e in E}=={0},'anchor intersection')
req(max(dc)+max(E)==4822 and min(dc)>0,'unshifted support')
mass=(len(E)+2)*(2*sum(weights.values())+6)
req(mass==21943453599356796577770480 and max(4*mass+8,2*mask+4,16)<2**b,'carry mass')
pad={e:2**87-1 for e in range(4823,4827)}
pad[4827]=2**38-1
req(sum(x.bit_count() for x in pad.values())==386,'padding population')
req(max(pad)<L and 2*max(pad.values())+4<2**b,'padding carry')

B=2**d;DC=sum(c<<(b*e) for e,c in dc.items());DR=2**(46*b)
MC=B-1-sum(1<<(b*e) for e in E if e!=1)-(2<<(b*507))
MF=4+sum(mask<<(b*t) for t in (2409,3015))
MF+=sum(1<<(b*t) for t,*_ in targetrows)
MF+=sum(c<<(b*e) for e,c in pad.items())
req(0<DC<B and 0<MC<B-1 and 0<MF<B-1,'port bounds')
req(MC.bit_count()==d-520 and MF.bit_count()==520,'port populations')
req(MC%4==2 and MF%8==4,'low congruences')
entries=[]
for name,value in {'beta':B-1,'K':DC+B*DR,'MC':MC,'MF_source':MF+B-1}.items():
    raw=value.to_bytes((value.bit_length()+7)//8,'little')
    actual=gzip.decompress((HERE/'separated_coefficients'/f'{name}.bin.gz').read_bytes())
    req(actual==raw,'actual coefficient bytes')
    entries.append(dict(port=name,bits=value.bit_length(),bytes=len(raw),sha256=sha256(raw).hexdigest()))

for p in (89,4831,lam):req(all(p%q for q in range(2,isqrt(p)+1)),'primality')
req(d==89*4831,'d factorization')
period=26565
req(pow(B,period,d)==1 and all(pow(B,period//q,d)!=1 for q in factor(period)),'exact order')
req((lam-1)%period==0,'period divides lambda-1')
req(pow(B,lam-1,lam*lam)==8376873414 and 8376873414%lam==1,'lifting')
unitrows=[]
for p in (89,4831,lam):
    row=(B%p,(B*B-1)%p,(1+B*DC+B*B*(DR+1))%p)
    req(row[1]!=0 and row[2]!=0,'unit condition')
    unitrows.append(dict(prime=p,B=row[0],B_squared_minus_one=row[1],H0=row[2]))
receipt=dict(status='PASS',imports_no_builder=True,python_assertions_used=False,
             source_sha256=sha256((HERE/'k215_transitions.json').read_bytes()).hexdigest(),
             modes=457,support=520,expanded_tiles=1479,unmatched_extras=536,
             occupied_witnesses=witnesses,physical_bit_corruptions=mutations,
             empty_auxiliary_assignments=empty_checked,accepted_empty_auxiliary_assignments=1,
             native_basis_checks=checks,b=b,L=L,d=d,lambda_=lam,
             total_raw_bytes=sum(x['bytes'] for x in entries),coefficients=entries,
             controller_units=unitrows)
(HERE/'separated_audit.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
