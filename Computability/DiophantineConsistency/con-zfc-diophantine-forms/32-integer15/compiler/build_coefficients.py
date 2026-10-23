#!/usr/bin/env python3
"""Exact Wang943 mixed-radix/fixed-factor coefficient synthesis.

New composition of ProveIt packages 24 and 25. All dependencies are the
Python standard library and the included literal K215 table and tile list.
This program checks finite arithmetic; it does not decide consistency.
"""
from pathlib import Path
from hashlib import sha256
from math import gcd, isqrt, lcm
import gzip
import json

ROOT = Path(__file__).resolve().parent
PIN = '8c6eec9d19ef80538c8e61ff6e0180040583446a'
MACHINE_SHA = 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
B_BITS, CELL, D_BITS = 121, 8801, 1064921
T1, T2, SHIFT = 4393, 5495, 42
PADDING_PRIME, STEP = 2341, 2340
ANCHORS = (1095,1096,2195,3296)
OFFSETS = (1023,1013,1003,983)
BARE = (30,62,1100,2200)

def require(ok, message):
    if not ok:
        raise ValueError(message)

def factor(n):
    factors = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            factors[p] = factors.get(p,0)+1
            n //= p
        p += 1
    if n>1:
        factors[n] = factors.get(n,0)+1
    return factors

def prime(n):
    return n>=2 and all(n % p for p in range(2,isqrt(n)+1))

def order(a, modulus):
    phi = modulus
    for p in factor(modulus):
        phi = phi//p*(p-1)
    result = phi
    for p in factor(phi):
        while result % p == 0 and pow(a,result//p,modulus)==1:
            result //= p
    require(pow(a,result,modulus)==1, 'invalid order')
    require(all(pow(a,result//p,modulus)!=1 for p in factor(result)),
            'order not minimal')
    return result

def machine_and_tiles():
    raw = (ROOT/'machine/k215.tm').read_bytes()
    require(sha256(raw).hexdigest()==MACHINE_SHA, 'literal K215 bytes changed')
    rows=[]
    for line in raw.decode().splitlines():
        if line and not line.startswith('#'):
            q,b,v,m,t = line.split()
            rows.append((int(q),int(b),int(v),m,int(t)))
    require(len(rows)==430 and len({(q,b) for q,b,*_ in rows})==430,
            'working action table has wrong size')
    require(rows[0]==(0,0,1,'R',93), 'wrong initial K215 action')
    sr=sorted({t for _,_,_,m,t in rows if m=='R'})
    sl=sorted({t for _,_,_,m,t in rows if m=='L'})
    rr={q:j+6 for j,q in enumerate(sr)}
    ll={q:j+6+len(sr) for j,q in enumerate(sl)}
    hd=lambda q,b:2*(q+1)+b
    groups={
        'actions':[(0,hd(q,b),rr[t],v) if m=='R' else (ll[t],hd(q,b),0,v)
                   for q,b,v,m,t in rows],
        'halt':[(0,hd(215,b),0,hd(215,b)) for b in (0,1)],
        'stay':[(0,b,0,b) for b in (0,1)],
        'right_receiver':[(rr[q],b,0,hd(q,b)) for q in sr for b in (0,1)],
        'left_receiver':[(0,b,ll[q],hd(q,b)) for q in sl for b in (0,1)],
        'finish':[(0,c,0,438) for c in (0,1,hd(215,0),hd(215,1))],
        'initialization':[(2,434,2,0),(2,435,3,1),(3,436,4,hd(93,0)),(4,436,4,0)],
        'reset':[(1,438,1,c) for c in (434,435,436)],
        'seam':[(a,437,b,437) for a in (0,1,4) for b in (0,1,2)],
        'forbidden':[(5,0,0,0)]}
    flat=[t for group in groups.values() for t in group]
    require(len(flat)==len(set(flat))==943, 'wrong tile language')
    start,forbidden=(2,435,3,1),(5,0,0,0)
    tiles=[start,forbidden]+sorted(set(flat)-{start,forbidden})
    expected=json.loads((ROOT/'upstream/wang943_tiles.json').read_text())
    require([list(t) for t in tiles]==expected,'changed tile order')
    return tiles,{k:len(v) for k,v in groups.items()}

def recipe():
    tiles,groups=machine_and_tiles()
    weights=[1<<(10+2*j) for j in range(44)]
    ce={i:1+sum(weights[10*s+j] for s,x in enumerate(tile)
                for j in range(10) if (x+512)>>j&1)+sum(weights[40:])
        for i,tile in enumerate(tiles)}
    ce.update({OFFSETS[s]+j:weights[10*s+j] for s in range(4) for j in range(10)})
    ce.update({e:weights[40+j] for j,e in enumerate(ANCHORS)})
    ce.update({1063:0,1064:0})
    mu=1022+sum(weights)
    dc={e:1 for e in BARE}
    for e,c in ce.items():
        for T in (T1,T2):
            dc[T-e]=dc.get(T-e,0)+c
    dc={e:c for e,c in dc.items() if c}
    targets=[(1013+j,{983+j},set(),{1013+j}) for j in range(10)]
    targets += [(1065+j,{1003+j},{1023+j},set()) for j in range(10)]
    targets += [(2195,{1095},set(),{2195}),(3296,{1096},set(),{3296})]
    filler={e:(1<<119)-1 for e in range(8792,8799)}
    filler[8799]=(1<<27)-1
    return tiles,groups,ce,mu,dc,targets,filler

def check_geometry(data):
    tiles,groups,ce,mu,dc,targets,filler=data
    support=set(ce)
    checks=0
    for target,at0,at1,at2 in targets:
        for e in support:
            require(dc.get(target-e,0)==int(e in at0),'contaminated DC field')
            require(int(e+SHIFT==target)==int(e in at1),'contaminated DR field')
            require(int(e==target)==int(e in at2),'contaminated temporal field')
            checks+=3
    for target in (T1,T2):
        for e in support:
            require(dc.get(target-e,0)==ce[e],'contaminated clause band')
            require(e+SHIFT!=target,'DR reaches clause band')
            checks+=2
    require({(T1-e)%CELL for e in support}.isdisjoint({(T2-e)%CELL for e in support}),
            'clean clause bands fail')
    intersection={(2195-e)%CELL for e in support}&{(3296-e)%CELL for e in support}
    require(intersection=={0},'unique anchor synchronization fails')
    mass=(len(support)+2)*(2*sum(ce.values())+6)
    threshold=max(4*mass+8,2*mu+4,16)
    require(threshold < 1<<B_BITS,'insufficient rho carry margin')
    require(2*max(filler.values())+4 < 1<<B_BITS,'insufficient mask carry margin')
    maximum=max(max(dc)+max(support),SHIFT+max(support),max(support))
    require(maximum==8791 and min(filler)>maximum,'filler enters computation support')
    require(max(filler)<CELL and min(dc)>0,'cell exponent range failed')
    filler_count=sum(x.bit_count() for x in filler.values())
    require(filler_count==860,'wrong filler population')
    require(2*mu.bit_count()+len(targets)+1+filler_count==len(support)==989,
            'native population balance failed')
    require(B_BITS*CELL==D_BITS and D_BITS%2==1,'wrong or even native width')
    # Every selector count is checked independently of upper-field carries.
    require([n for n in range(944) if n&1022==0]==[0,1],'mixed low count decoder failed')
    for n in(0,1):
        for bit in(0,1):
            for copy in(0,1):
                require(((n*bit+copy)&1==0)==(copy==n*bit), 'bit parity decoder failed')
    return dict(status='PASS',basis_convolution_checks=checks,tile_count=len(tiles),
                tile_group_counts=groups,support_size=len(support),
                clause_population=mu.bit_count(),filler_population=filler_count,
                mass_bits=mass.bit_length(),carry_threshold_bits=threshold.bit_length(),
                mask_threshold_bits=(2*max(filler.values())+4).bit_length(),
                combined_threshold_bits=max(threshold,2*max(filler.values())+4).bit_length(),
                radix_bits=B_BITS,max_unshifted_exponent=maximum,filler_first=min(filler),
                filler_last=max(filler),clean_band_intersection=[],anchor_intersection=[0])

def check_controller(dc):
    factors=factor(D_BITS)
    require(factors=={11:2,13:1,677:1},'wrong factorization')
    require(prime(PADDING_PRIME) and gcd(PADDING_PRIME,D_BITS)==1,'invalid controller prime')
    ord_d=order(pow(2,D_BITS,D_BITS),D_BITS)
    require(ord_d==780 and STEP==PADDING_PRIME-1 and STEP%ord_d==0,
            'controller order conditions failed')
    value=pow(2,D_BITS*STEP,PADDING_PRIME**2)
    require(value==2556373 and value%PADDING_PRIME==1 and value!=1,
            'controller valuation must equal one')
    units=[]
    for p in list(factors)+[PADDING_PRIME]:
        rho,B=pow(2,B_BITS,p),pow(2,D_BITS,p)
        DC=sum(c*pow(rho,e,p) for e,c in dc.items())%p
        DR=pow(rho,SHIFT,p)
        qfactor=(B*B-1)%p
        bracket=(1+B*DC+B*B*(DR+1))%p
        require(qfactor and bracket,'dummy controller is not a unit')
        units.append(dict(prime=p,B=B,DC=DC,DR=DR,q_squared_minus_one=qfactor,bracket=bracket))
    orders={str(p):order(pow(2,D_BITS,p),p) for p in(121,13,677,PADDING_PRIME)}
    return dict(status='PASS',d_factorization=factors,order_mod_d=ord_d,
                order_prime_factors=list(factor(ord_d)),multiplicative_orders=orders,
                padding_prime=PADDING_PRIME,step=STEP,valuation=1,
                B_power_step_mod_prime_squared=value,unit_residues=units)

def materialize(data):
    _,_,ce,mu,dc,targets,filler=data
    B=1<<D_BITS
    DC=sum(c<<(B_BITS*e) for e,c in dc.items())
    DR=1<<(B_BITS*SHIFT)
    MC=B-1-sum(1<<(B_BITS*e) for e in ce if e!=1)-(2<<(B_BITS*1063))
    MF_native=4+(mu<<(B_BITS*T1))+(mu<<(B_BITS*T2))
    MF_native += sum(1<<(B_BITS*t) for t,*_ in targets)
    MF_native += sum(c<<(B_BITS*e) for e,c in filler.items())
    require(0<DC<B and 0<MC<B-1 and 0<MF_native<B-1,'native coefficient range failed')
    require(MC%4==2 and MF_native%8==4,'low native congruences failed')
    require(MC.bit_count()+MF_native.bit_count()==D_BITS and MF_native.bit_count()==989,
            'materialized mask balance failed')
    values={'beta':B-1,'K':DC+B*DR,'MC':MC,'MF_source':MF_native+B-1}
    out=ROOT/'coefficients';out.mkdir(exist_ok=True)
    files=[]
    for port,value in values.items():
        raw=value.to_bytes((value.bit_length()+7)//8,'little')
        compressed=gzip.compress(raw,mtime=0)
        (out/(port+'.bin.gz')).write_bytes(compressed)
        require(int.from_bytes(gzip.decompress(compressed),'little')==value,'payload round-trip failed')
        files.append(dict(port=port,file=port+'.bin.gz',bit_length=value.bit_length(),
                          bytes=len(raw),gzip_bytes=len(compressed),population=value.bit_count(),
                          sha256=sha256(raw).hexdigest(),gzip_sha256=sha256(compressed).hexdigest()))
    return files

def main():
    data=recipe()
    geometry=check_geometry(data)
    controller=check_controller(data[4])
    files=materialize(data)
    result=dict(instance='wang943-mixed121-fixed-factor-8801',source_commit=PIN,
                machine_sha256=MACHINE_SHA,B='2^1064921',rho='2^121',d=D_BITS,
                radix_bits=B_BITS,cell_length=CELL,clause_bands=[T1,T2],spatial_shift=SHIFT,
                filler={'8792..8798':'2^119-1','8799':'2^27-1'},
                encoding='gzip of minimal unsigned little-endian integers',
                ports={'beta':'B-1','K':'DC+B*DR','MC':'native low mask',
                       'MF_source':'native high mask+B-1'},
                aliases={'Bm1':'beta','Kconstant':'K','K0':'K','MF':'MF_source'},
                warning='Replace all four ports together; MF is already shifted.',
                files=files,total_raw_bytes=sum(x['bytes'] for x in files),
                total_gzip_bytes=sum(x['gzip_bytes'] for x in files),geometry=geometry,
                controller=controller,end_to_end_formal_certificate=False,
                scope='Exact finite recipe and ordinary compiler adapter; no consistency decision.')
    (ROOT/'coefficients/COEFFICIENT_BINDING.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
