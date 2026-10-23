#!/usr/bin/env python3
"""Complemented whole-label Wang943 compiler, B = 2^678139.

The native geometry and rank-controller method come from ProveIt package 36.
The new local clause encoding replaces 38 radix-four bit comparisons by
four complemented whole-label fields; all arithmetic is exact and finite.
Inherited notices and source hashes are retained beside this file.
"""
from pathlib import Path
from hashlib import sha256
from collections import Counter
from math import gcd, isqrt, lcm
import gzip
import json

HERE = Path(__file__).resolve().parent
PIN = '22e75dd6b87b1b199bb08c778d7cf075ae5aae08'
B_BITS, CELL = 77, 8807
D_BITS = B_BITS * CELL
PAD_PRIME, STEP = 56611, 56610
WIDTHS = (9, 10, 9, 10)
OFFSETS = (1023, 1013, 1003, 983)
FIELD_STARTS = (16, 47, 37, 26)
ANCHORS = (1095, 2195, 3296)
ANCHOR_FIELDS = (10, 12, 14)
T1, T2, SHIFT = 4393, 5495, 42
BARE = (30, 62, 1100, 2201)

def require(ok, message):
    if not ok:
        raise ValueError(message)

def factors(n):
    result = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        result[n] = 1
    return result

def is_prime(n):
    return n >= 2 and all(n % p for p in range(2, isqrt(n)+1))

def order(a, modulus):
    phi = modulus
    for p in factors(modulus):
        phi = phi//p*(p-1)
    n = phi
    for p in factors(phi):
        while n % p == 0 and pow(a, n//p, modulus) == 1:
            n //= p
    require(pow(a,n,modulus)==1, 'order failure')
    require(all(pow(a,n//p,modulus)!=1 for p in factors(n)), 'order not minimal')
    return n

def language():
    source = (HERE/'k215_transitions.json').read_bytes()
    rows = json.loads(source)['transitions']
    require(len(rows)==430 and len({(q,b) for q,b,_,_,_ in rows})==430,
            'literal K215 action count')
    right = sorted({t for q,b,v,m,t in rows if m==1})
    left = sorted({t for q,b,v,m,t in rows if m==-1})
    rr = {q:j+6 for j,q in enumerate(right)}
    ll = {q:j+6+len(right) for j,q in enumerate(left)}
    hd = lambda q,b: 2*(q+1)+b
    ts = set((0,hd(q,b),rr[t],v) if m==1 else (ll[t],hd(q,b),0,v)
             for q,b,v,m,t in rows)
    ts.update((0,hd(215,b),0,hd(215,b)) for b in (0,1))
    ts.update((0,b,0,b) for b in (0,1))
    ts.update((rr[q],b,0,hd(q,b)) for q in right for b in (0,1))
    ts.update((0,b,ll[q],hd(q,b)) for q in left for b in (0,1))
    ts.update((0,c,0,438) for c in (0,1,hd(215,0),hd(215,1)))
    ts.update([(2,434,2,0),(2,435,3,1),(3,436,4,hd(93,0)),(4,436,4,0)])
    ts.update((1,438,1,c) for c in (434,435,436))
    ts.update((a,437,b,437) for a in (0,1,4) for b in (0,1,2))
    start, forbidden = (2,435,3,1), (5,0,0,0)
    ts.add(forbidden)
    tiles = [start,forbidden]+sorted(ts-{start,forbidden})
    require(len(tiles)==943 and (len(right),len(left))==(199,45),'Wang language size')
    payload = json.dumps(tiles,separators=(',',':')).encode()+b'\n'
    require(payload==(HERE/'wang943_tiles.json').read_bytes(), 'literal tile reconstruction')
    require(sha256(payload).hexdigest()==
            '66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f',
            'literal Wang943 hash')
    return tiles, sha256(source).hexdigest()

def recipe():
    tiles, source_hash = language()
    ce = {i:1+sum((x+1)<<s for x,s in zip(tile,FIELD_STARTS))
          +sum(1<<s for s in ANCHOR_FIELDS) for i,tile in enumerate(tiles)}
    ce.update({o+j:1<<(s+j) for o,l,s in zip(OFFSETS,WIDTHS,FIELD_STARTS)
               for j in range(l)})
    ce.update({e:1<<s for e,s in zip(ANCHORS,ANCHOR_FIELDS)})
    ce.update({1063:0,1064:0})
    mu = 1022+sum(((1<<l)-1)<<s for l,s in zip(WIDTHS,FIELD_STARTS))
    mu += sum(1<<s for s in ANCHOR_FIELDS)
    dc = Counter({e:1 for e in BARE})
    for e,c in ce.items():
        if c:
            for T in (T1,T2):
                dc[T-e] += c
    targets = [(1013+j,{983+j},set(),{1013+j}) for j in range(10)]
    targets += [(1065+j,{1003+j},{1023+j},set()) for j in range(9)]
    targets += [(2195,{1095},set(),{2195}),(3296,{1095},set(),{3296})]
    padding = {e:(1<<75)-1 for e in range(8792,8803)}
    padding[8803] = (1<<39)-1
    return dict(tiles=tiles,source_hash=source_hash,ce=ce,E=set(ce),mu=mu,
                dc=dict(dc),targets=targets,padding=padding)

def finite_audit(data):
    E,ce,mu,dc,targets,padding = [data[k] for k in ('E','ce','mu','dc','targets','padding')]
    checks = 0
    for t,a,c,y in targets:
        for e in E:
            require(dc.get(t-e,0)==int(e in a),'DC overlap contamination')
            require(int(e+SHIFT==t)==int(e in c),'DR overlap contamination')
            require(int(e==t)==int(e in y),'temporal overlap contamination')
            checks += 3
    for T in (T1,T2):
        for e in E:
            require(dc.get(T-e,0)==ce[e],'clause contamination')
            require(e+SHIFT!=T,'DR clause contamination')
            checks += 2
    require({(T1-e)%CELL for e in E}.isdisjoint({(T2-e)%CELL for e in E}),
            'simultaneously dirty clause bands')
    require({(2195-e)%CELL for e in E}&{(3296-e)%CELL for e in E}=={0},
            'nonunique anchor synchronization')
    require(min(dc)>0 and max(dc)+max(E)==8791<min(padding),'zero padding contaminated')
    require(SHIFT+max(E)<min(padding) and max(E)<min(padding),'DR/temporal padding')
    require(max(padding)<CELL and 2*max(E)<CELL,'cell circumference')
    require(len(E)==986 and mu.bit_count()==50,'mask counts')
    require(sum(c.bit_count() for c in padding.values())==864,'padding count')
    mass=(len(E)+2)*(2*sum(ce.values())+6)
    threshold=max(4*mass+8,2*mu+4,2*max(padding.values())+4,16)
    require(threshold < 1<<B_BITS,'carry bound')
    require([n for n in range(944) if (n&1022)==0]==[0,1],'selector decoding')
    decoder_checks = 0
    for slot,l in enumerate(WIDTHS):
        mask=(1<<l)-1
        labels=sorted({t[slot] for t in data['tiles']})
        require(max(labels)<1<<(l-1),'occupied high bit')
        for v in range(1<<l):
            require(((v&mask)==0)==(v==0),'empty field')
            decoder_checks += 1
        for x in labels:
            code=mask-x
            for v in range(1<<l):
                value=x+1+v
                require(0<value<1<<(l+1),'field carry bound')
                require(((value&mask)==0)==(v==code),'complemented label decoding')
                decoder_checks += 1
    return dict(status='PASS',basis_convolution_checks=checks,
                complemented_field_checks=decoder_checks,support_size=len(E),
                clause_mask_population=mu.bit_count(),padding_population=864,
                padding_first=min(padding),padding_last=max(padding),
                maximum_unshifted_exponent=8791,mass_bits=mass.bit_length(),
                carry_threshold_bits=threshold.bit_length(),radix_bits=B_BITS,
                rotation_hit_sets_disjoint=True,anchor_intersection=[0])

def padding_certificate(data):
    require(factors(D_BITS)=={7:1,11:1,8807:1},'d factorization')
    require(is_prime(PAD_PRIME),'padding primality')
    moduli=[7,11,8807,PAD_PRIME]
    orders={str(m):order(pow(2,D_BITS,m),m) for m in moduli}
    period=lcm(*(orders[str(m)] for m in moduli[:-1]))
    require(period==18870 and STEP%period==0,'period modulo d')
    require(STEP%orders[str(PAD_PRIME)]==0,'period modulo lambda')
    require(pow(2,D_BITS*STEP,D_BITS)==1,'B^step modulo d')
    lift=pow(2,D_BITS*STEP,PAD_PRIME**2)
    require(lift==1810929280 and lift%PAD_PRIME==1 and lift!=1,'lifting certificate')
    rows=[]
    for p in moduli:
        rho,B=pow(2,B_BITS,p),pow(2,D_BITS,p)
        DC=sum((c%p)*pow(rho,e,p) for e,c in data['dc'].items())%p
        DR=pow(rho,SHIFT,p)
        qfactor=(B*B-1)%p
        bracket=(1+B*DC+B*B*(DR+1))%p
        require(qfactor!=0 and bracket!=0,'nonunit control multiplier')
        rows.append(dict(prime=p,B=B,DC=DC,DR=DR,
                         B_squared_minus_one=qfactor,bracket=bracket))
    return dict(status='PASS',d_factorization={7:1,11:1,8807:1},
                multiplicative_orders=orders,order_mod_d=period,padding_prime=PAD_PRIME,
                step=STEP,B_power_step_mod_lambda_squared=lift,lifting_valuation=1,
                unit_residues=rows)

def materialize(data):
    B=1<<D_BITS
    DC=sum(c<<(B_BITS*e) for e,c in data['dc'].items())
    DR=1<<(B_BITS*SHIFT)
    MF=4+sum(data['mu']<<(B_BITS*T) for T in (T1,T2))
    MF+=sum(1<<(B_BITS*t) for t,*_ in data['targets'])
    MF+=sum(c<<(B_BITS*e) for e,c in data['padding'].items())
    MC=B-1-sum(1<<(B_BITS*e) for e in data['E'] if e!=1)-(2<<(B_BITS*1063))
    require(0<DC<B and 0<MC<B-1 and 0<MF<B-1,'coefficient bounds')
    require(MC.bit_count()==D_BITS-986 and MF.bit_count()==986,'population balance')
    require(MC%4==2 and MF%8==4,'native congruences')
    ports={'beta':B-1,'K':DC+B*DR,'MC':MC,'MF_source':MF+B-1}
    out=HERE/'coefficients';out.mkdir(exist_ok=True)
    entries=[]
    for port,value in ports.items():
        raw=value.to_bytes((value.bit_length()+7)//8,'little')
        compressed=gzip.compress(raw,mtime=0)
        (out/(port+'.bin.gz')).write_bytes(compressed)
        require(int.from_bytes(gzip.decompress(compressed),'little')==value,'round trip')
        entries.append(dict(port=port,file='coefficients/'+port+'.bin.gz',
                            bits=value.bit_length(),raw_bytes=len(raw),gzip_bytes=len(compressed),
                            sha256=sha256(raw).hexdigest(),gzip_sha256=sha256(compressed).hexdigest()))
    return dict(files=entries,total_raw_bytes=sum(x['raw_bytes'] for x in entries),
                total_gzip_bytes=sum(x['gzip_bytes'] for x in entries),
                native_low_population=MC.bit_count(),native_high_population=MF.bit_count())

def main():
    data=recipe()
    geometry=finite_audit(data)
    controller=padding_certificate(data)
    payload=materialize(data)
    binding=dict(instance='wang943-complemented77-length8807-prime56611',source_commit=PIN,
                 b=B_BITS,L=CELL,d=D_BITS,B=f'2^{D_BITS}',T1=T1,T2=T2,DR_exponent=SHIFT,
                 port_widths=WIDTHS,occupied_code='2^width - 1 - original_label',
                 field_starts=FIELD_STARTS,anchor_field_starts=ANCHOR_FIELDS,
                 anchors=ANCHORS,bare_shifts=BARE,
                 ports={'Bm1':'beta','Kconstant':'K','MC':'MC','MF':'MF_source'},
                 warning='MF_source = MF_native + B - 1. Replace all four ports together.',
                 transition_json_sha256=data['source_hash'],geometry=geometry,
                 padding_controller=controller,materialization=payload,
                 proof_status='Ordinary mathematical compiler adapter; no new end-to-end formal certificate.')
    (HERE/'COEFFICIENT_BINDING.json').write_text(json.dumps(binding,indent=2)+'\n')
    print(json.dumps(binding,indent=2))

if __name__=='__main__':
    main()
