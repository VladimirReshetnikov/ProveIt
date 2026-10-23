"""Independent formula-based verification of wave-7 complemented receivers.

All inputs are inert JSON/gzip data. No upstream Python is imported or run.
The finite mode-language definition is reimplemented from the literal
transition table and source's declarative tile families. Unbounded tiling,
native-window and K215/calculus theorems are not proved by this checker.
"""
import json,gzip,math,hashlib,itertools
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SRC=ROOT
actions=json.loads((SRC/'k215_transitions.json').read_text())['transitions']
assert len(actions)==430
tiles=set()
for state,bit,write,direction,next_state in actions:
    head=512+2*state+bit
    if direction==1: tiles.add((0,head,256+next_state,write))
    else:
        assert direction==-1
        tiles.add((512+next_state,head,0,write))
for bit in [0,1]:
    tiles.add((0,942+bit,0,942+bit))
    tiles.add((0,bit,0,bit))
for top in [0,1,942,943]:tiles.add((0,top,0,6))
tiles.update([(2,2,2,0),(2,3,3,1),(3,4,4,698),(4,4,4,0)])
for bottom in [2,3,4]:tiles.add((1,6,1,bottom))
for west,east in itertools.product([0,1,4],[0,1,2]):tiles.add((west,5,east,5))
start,forbidden=(2,3,3,1),(5,0,0,0)
right,left=(256,0,0,512),(0,0,512,512)
tiles.update([forbidden,right,left])
modes=[start,forbidden]+sorted(tiles-{start,forbidden})
assert len(modes)==457
ri,li=modes.index(right),modes.index(left)
T=1<<42; M=4*T; H=1<<29
def label(t):
    w,n,e,s=t
    return 2*w+(n<<11)+(2*e<<21)+(s<<32)
coeff={}
for index,t in enumerate(modes):
    coeff[index]=1+255*(1<<9)*(index!=ri)+255*(1<<18)*(index!=li)+(1<<27)*(index not in (ri,li))+H*(1+label(t))
for offset,width,shift in [(539,11,0),(528,10,11),(517,11,21),(495,10,32)]:
    for j in range(width):coeff[offset+j]=1<<(29+shift+j)
coeff[539]+=H*T
for j in range(8):
    coeff[567+j]=(1<<(9+j))+H*((1<<(j+1))+(1<<(33+j)))
    coeff[575+j]=(1<<(18+j))+H*((1<<(22+j))+(1<<(33+j)))
coeff[583]=(1<<27)+H*((1<<11)+(1<<32))
coeff[1203]=coeff[1807]=H*T
coeff[507]=coeff[508]=0
support=set(coeff);assert len(support)==520
mask=510+(1<<17)+(1<<26)+(1<<28)+H*(M-1)
assert mask.bit_count()==55
current={33:1,68:1,664:1,1268:1}
for e,c in coeff.items():
    for target in [2409,3015]:
        if c:current[target-e]=current.get(target-e,0)+c
tests=[]
for j in range(10):tests.append((528+j,495+j,None,528+j))
for j in range(11):tests.append((585+j,517+j,539+j,None))
for target in [1203,1807]:tests.append((target,539,None,target))
identities=0
for target,c,s,t in tests:
    for e in support:
        assert current.get(target-e,0)==(e==c)
        assert (e+46==target)==(e==s)
        assert (e==target)==(e==t)
        identities+=3
for target in [2409,3015]:
    for e in support:
        assert current.get(target-e,0)==coeff[e]
        assert e+46!=target
        identities+=2
assert identities==37960
L=4831;b=89;d=b*L
assert {((2409-e)%L) for e in support}.isdisjoint({((3015-e)%L) for e in support})
assert {((1203-e)%L) for e in support}&{((1807-e)%L) for e in support}=={0}
mass=(len(support)+2)*(2*sum(coeff.values())+6)
assert mass==21943453599356796577770480
assert max(4*mass+8,2*mask+4,16)<1<<b
assert max(current)+max(support)==4822
pad={e:(1<<87)-1 for e in range(4823,4827)};pad[4827]=(1<<38)-1
assert 2*max(pad.values())+4<1<<b
B=1<<d
DC=sum(c<<(b*e) for e,c in current.items());DR=1<<(b*46)
MC=B-1-sum(1<<(b*e) for e in support if e!=1)-(2<<(b*507))
MF=4+(mask<<(b*2409))+(mask<<(b*3015))
MF+=sum(1<<(b*t) for t,*_ in tests)
MF+=sum(c<<(b*e) for e,c in pad.items())
assert 0<DC<B and 0<MC<B-1 and 0<MF<B-1
assert MC.bit_count()==d-520 and MF.bit_count()==520
assert MC%4==2 and MF%8==4
actual={'beta':B-1,'K':DC+B*DR,'MC':MC,'MF_source':MF+B-1}
ports=[]
for name,v in actual.items():
    blob=(SRC/f'{name}.bin.gz').read_bytes()
    raw=gzip.decompress(blob)
    want=v.to_bytes((v.bit_length()+7)//8,'little')
    assert raw==want
    ports.append(dict(name=name,bits=v.bit_length(),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),gzip_sha256=hashlib.sha256(blob).hexdigest()))
assert sum(p['bytes'] for p in ports)==215492
def aux(qr,ql,u):
    return sum(coeff[567+j] for j in range(8) if qr>>j&1)+sum(coeff[575+j] for j in range(8) if ql>>j&1)+u*coeff[583]
occupied=mutations=0
expanded=set()
for idx,mode in enumerate(modes):
    if idx==ri: choices=[((256+q,u,0,512+2*q+u),q,0,u) for q,u in itertools.product(range(256),range(2))]
    elif idx==li:choices=[((0,u,512+q,512+2*q+u),0,q,u) for q,u in itertools.product(range(256),range(2))]
    else:choices=[(mode,0,0,0)]
    for tile,qr,ql,u in choices:
        expanded.add(tile)
        v=label(tile);assert 0<=v<T
        word=M-1-v;assert word//T==3 and word%2==1 and (word>>21)&1
        n=coeff[idx]+aux(qr,ql,u)+H*word
        assert n&mask==0
        for j in range(42):
            changed=word^(1<<j)
            if j==0: changed-=T
            assert (coeff[idx]+aux(qr,ql,u)+H*changed)&mask
            mutations+=1
        assert (n-H*T)&mask
        mutations+=2;occupied+=1
assert (occupied,mutations)==(1479,65076)
assert len(expanded)==1479
edge_sets=[{t[j] for t in expanded} for j in range(4)]
viable={t for t in expanded if all(t[j] in edge_sets[(j+2)%4] for j in range(4))}
expected=tiles-{right,left,forbidden}
right_states={a[4] for a in actions if a[3]==1}
left_states={a[4] for a in actions if a[3]==-1}
for q,u in itertools.product(right_states,[0,1]):expected.add((256+q,u,0,512+2*q+u))
for q,u in itertools.product(left_states,[0,1]):expected.add((0,u,512+q,512+2*q+u))
assert viable==expected and len(viable)==942
assert len(expanded-viable)==537
empty=0
for qr,ql,u in itertools.product(range(256),range(256),range(2)):
    v=2*qr+(u<<11)+(2*ql<<21)+((2*qr+2*ql+u)<<32)
    assert 0<=v<T and v%2==0
    candidate=(-v)%M
    # If west parity is zero, the two remaining anchors can contribute at most 2T.
    possible=candidate//T<=2
    assert possible==(qr==ql==u==0)
    assert (aux(qr,ql,u)+H*candidate)&mask==0
    empty+=1
prime=106261
for n in [89,4831,prime]:assert all(n%k for k in range(2,math.isqrt(n)+1))
order=26565
assert pow(B,order,d)==1
for p in [3,5,7,11,23]:
    if order%p==0:assert pow(B,order//p,d)!=1
assert (prime-1)%order==0
assert pow(B,prime-1,prime)==1
assert pow(B,prime-1,prime*prime)==8376873414!=1
unit_rows={}
for p in [89,4831,prime]:
    row=[B%p,(B*B-1)%p,(1+B*DC+B*B*(DR+1))%p]
    assert row[1] and row[2];unit_rows[p]=row
out={'status':'PASS','scope':'Independent finite reimplementation from declarative formulas and inert transition/payload data. No upstream programs executed. Does not prove unbounded compiler/calibration or consistency.', 'mode_count':len(modes),'support':len(support),'basis_identities':identities,'occupied_decodings':occupied,'single_bit_mutations':mutations,'empty_payloads':empty,'expanded_modes':len(expanded),'unmatched_tiles_including_forbidden':len(expanded-viable),'literal_admissible_tiles':len(viable),'radix_bits':b,'cell_length':L,'native_base_exponent':d,'mass':str(mass),'ports':ports,'unit_rows':unit_rows}
(ROOT/'SEPARATED_TUPLE_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ('ports','unit_rows')},indent=2))
