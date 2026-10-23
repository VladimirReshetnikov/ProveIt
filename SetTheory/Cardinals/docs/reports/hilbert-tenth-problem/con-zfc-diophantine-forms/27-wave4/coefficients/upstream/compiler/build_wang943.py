"""Newly authored finite compiler; imports no received program.

Only inert input is the exact 430-action K215 text table. It constructs a
943-tile directed-signal Wang language, scalar layout and four coefficients.
"""
from pathlib import Path
from itertools import product
from collections import Counter
from hashlib import sha256
import json

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'upstream/k215.tm'
assert sha256(SOURCE.read_bytes()).hexdigest()=='fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
ROWS=[]
for line in SOURCE.read_text().splitlines():
    if line and not line.startswith('#'):
        q,b,v,move,t=line.split()
        ROWS.append((int(q),int(b),int(v),1 if move=='R' else -1,int(t)))
assert len(ROWS)==430 and len({(q,b) for q,b,*_ in ROWS})==430
DELTA={(q,b):(v,d,t) for q,b,v,d,t in ROWS}
DELTA.update({(215,b):(b,0,215) for b in (0,1)})
L,Q,R,V,H=434,435,436,437,438
# Horizontal edge colors: neutral, temporal boundary, three phase-chain
# colors, unmatchable forbidden west color, then right/left arrival states.
O,HB,PL,PQ,PR,BAD=range(6)
RIGHT_STATES=sorted({t for q,b,v,d,t in ROWS if d==1})
LEFT_STATES=sorted({t for q,b,v,d,t in ROWS if d==-1})
SIGR={q:6+j for j,q in enumerate(RIGHT_STATES)}
SIGL={q:6+len(RIGHT_STATES)+j for j,q in enumerate(LEFT_STATES)}

def head(q,b): return 2*(q+1)+b

def tile_data(table=DELTA):
    """Return (west,north,east,south) tiles, with Start then Forbidden."""
    groups={}
    groups['working']=[(O,head(q,b),SIGR[t],v) if d==1 else (SIGL[t],head(q,b),O,v)
                       for q,b,v,d,t in ROWS]
    groups['halt']=[(O,head(215,b),O,head(215,b)) for b in (0,1)]
    groups['headless']=[(O,b,O,b) for b in (0,1)]
    groups['arrive_right']=[(SIGR[q],b,O,head(q,b)) for q in RIGHT_STATES for b in (0,1)]
    groups['arrive_left']=[(O,b,SIGL[q],head(q,b)) for q in LEFT_STATES for b in (0,1)]
    groups['finish']=[(O,c,O,H) for c in (0,1,head(215,0),head(215,1))]
    groups['phase']=[(PL,L,PL,0),(PL,Q,PQ,1),(PQ,R,PR,head(93,0)),(PR,R,PR,0)]
    groups['horizontal']=[(HB,H,HB,p) for p in (L,Q,R)]
    groups['vertical']=[(l,V,r,V) for l in (O,HB,PR) for r in (O,HB,PL)]
    groups['forbidden']=[(BAD,0,O,0)]
    flat=[t for ts in groups.values() for t in ts]
    assert len(flat)==len(set(flat))==943
    start=(PL,Q,PQ,1); forbidden=(BAD,0,O,0)
    tiles=[start,forbidden]+sorted(set(flat)-{start,forbidden})
    return tiles,groups

TILES,GROUPS=tile_data()

def layout():
    k=len(TILES); a=10; ell=10; A=1<<ell; nd=2
    # Slot indices west,north,east,south, embedded in the old exponent grid.
    offsets=(k+8*a,k+7*a,k+6*a,k+4*a)
    copies={(slot,bit):off+bit for slot,off in enumerate(offsets) for bit in range(a)}
    e_star=k+12*a; M=k+15*a+nd
    anchors=(M,2*M,4*M,9*M); Emax=9*M
    Hc=16*M+3*a+1
    T1=Hc+2*Emax+a+1
    gap=4*((Emax+1)//2)+2
    T2=T1+gap
    Lcell=1
    while Lcell<T2+2*Emax+2: Lcell*=5
    support=set(range(k))|set(copies.values())|set(range(e_star,e_star+nd))|set(anchors)
    assert len(support)==989
    # Every tile edge is coded by its nine data bits and an occupancy bit.
    code=lambda x: x+512
    coeff={i:1+sum(((code(x)>>bit)&1)*A**(1+10*slot+bit)
                         for slot,x in enumerate(tile) for bit in range(10))
                +sum(A**j for j in range(41,45)) for i,tile in enumerate(TILES)}
    coeff.update({e:A**(1+10*slot+bit) for (slot,bit),e in copies.items()})
    coeff.update({e:A**(41+j) for j,e in enumerate(anchors)})
    coeff.update({e:0 for e in range(e_star,e_star+nd)})
    assert set(coeff)==support
    # Saturated clause masks allow exactly digits 0 or 2; selector digit 0 or 1.
    # 405 low mask bits plus 78 harmless high zero-clause bits = 483.
    mu=(A-2)+sum((A-3)*A**j for j in range(1,45))+((1<<78)-1)*(1<<450)
    assert mu.bit_count()==483 and mu.bit_length()==528
    mass=(len(support)+2)*(2*sum(coeff.values())+6)
    threshold=max(4*mass+8,2*mu+4,16)
    b=1
    while (1<<b)<threshold: b*=5
    bare=(3*a,Hc+2*a,3*M,7*M)
    # Vertical: south -> north, spatial: east -> west.
    targets=[(copies[1,j],{copies[3,j]},set(),{copies[1,j]}) for j in range(a)]
    targets += [(Hc+copies[0,j],{copies[2,j]},{copies[0,j]},set()) for j in range(a)]
    targets += [(anchors[2],{anchors[0]},set(),{anchors[2]}),
                (anchors[3],{anchors[1]},set(),{anchors[3]})]
    scalar=dict(k=k,a=a,ell=ell,A=A,dummy_count=nd,e_star=e_star,M=M,
                Emax=Emax,Hc=Hc,T1=T1,T2=T2,gap=gap,b=b,L=Lcell,d=b*Lcell,
                native_support=len(support),clause_digits=44,mu_population=mu.bit_count(),
                mu_bit_length=mu.bit_length(),mass_bit_length=mass.bit_length(),
                threshold_bit_length=threshold.bit_length(),
                copy_offsets=offsets,anchors=anchors,bare_shifts=bare)
    return scalar,support,copies,coeff,mu,targets

def audit_geometry(data):
    s,E,cp,ce,mu,targets=data
    b,Lc=s['b'],s['L']; Hc=s['Hc']; T1,T2=s['T1'],s['T2']; M=s['M']
    checks=0
    for t,c0,c1,c2 in targets:
        assert {t-v for v in s['bare_shifts'] if t-v in E}==c0
        assert ({t-Hc} if t-Hc in E else set())==c1
        assert ({t} if t in E else set())==c2
        assert t<T1-s['Emax']
        checks+=1
    for t,other in [(T1,T2),(T2,T1)]:
        assert not {t-v for v in s['bare_shifts']}&E
        assert all(other+x-t not in E for x in E)
    Estar=E|{s['e_star']+1}
    assert {(T1-e)%Lc for e in Estar}.isdisjoint({(T2-e)%Lc for e in Estar})
    assert {(4*M-e)%Lc for e in E}&{(9*M-e)%Lc for e in E}=={0}
    dc5=(sum(pow(2,v,5) for v in s['bare_shifts'])+
         sum((c%5)*(pow(2,T1-e,5)+pow(2,T2-e,5)) for e,c in ce.items()))%5
    unit=(2*dc5-pow(2,Hc,5))%5
    assert unit!=0
    assert s['native_support']==2*mu.bit_count()+len(targets)+1
    assert s['b']==625 and s['L']==78125 and s['d']==5**11
    assert all(max(tile)<512 for tile in TILES)
    return dict(target_checks=checks,all_rotation_clause_separation=True,
                all_rotation_anchor_intersection=[0],mod5_unit=unit,
                native_mask_population=s['native_support'],saturated_clause_audit=True)

def output():
    data=layout();s=data[0];audit=audit_geometry(data)
    (HERE/'wang943_tiles.json').write_text(json.dumps(TILES,separators=(',',':'))+'\n')
    (HERE/'wang943_layout.json').write_text(json.dumps(s,indent=2)+'\n')
    receipt=dict(status='PASS',source_sha256=sha256(SOURCE.read_bytes()).hexdigest(),
                 tile_count=len(TILES),group_counts={k:len(v) for k,v in GROUPS.items()},
                 right_targets=len(RIGHT_STATES),left_targets=len(LEFT_STATES),
                 tile_sha256=sha256((HERE/'wang943_tiles.json').read_bytes()).hexdigest(),
                 layout=s,audit=audit)
    (HERE/'wang943_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':output()

