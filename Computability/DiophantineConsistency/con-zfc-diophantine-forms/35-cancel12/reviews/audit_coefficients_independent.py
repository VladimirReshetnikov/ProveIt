#!/usr/bin/env python3
"""Independent literal-data audit of the mixed121 coefficient tuple.

Does not import or execute either coefficient generator. Uses only Python's
standard library. Mathematical infinitary transfer is reviewed separately.
"""
from pathlib import Path
from collections import defaultdict
from math import gcd, isqrt, lcm
import gzip, hashlib, json

HERE=Path(__file__).resolve().parent
NEW=HERE.parent/'coefficients'
OLD=NEW/'upstream'

def check(ok,msg):
    if not ok: raise ValueError(msg)

def divisors_prime(n):
    answer=[]
    p=2
    while p*p<=n:
        if n%p==0:
            answer.append(p)
            while n%p==0: n//=p
        p+=1
    if n>1: answer.append(n)
    return answer

def isprime(n):
    return n>1 and all(n%p for p in range(2,isqrt(n)+1))

def order_by_cycle(a,m,bound):
    value=1
    for i in range(1,bound+1):
        value=value*a%m
        if value==1: return i
    raise ValueError('order search bound insufficient')

def main():
    actual=json.loads((NEW/'COEFFICIENT_BINDING.json').read_text())
    tiles=json.loads((OLD/'wang943_tiles.json').read_text())
    if isinstance(tiles,dict):
        tiles=tiles.get('tiles',tiles.get('ordered_tiles'))
    check(tiles==json.loads((NEW/'wang943_tiles.json').read_text()),'Frozen tile list differs')
    check(hashlib.sha256((NEW/'k215.tm').read_bytes()).hexdigest()=='fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090','machine mismatch')
    check(len(tiles)==943 and len(set(tuple(x) for x in tiles))==943,'tile count')
    b,L,H,T1,T2=121,8801,42,4393,5495
    d=b*L
    copies=[[offset+j for j in range(10)] for offset in [1023,1013,1003,983]]
    anchors=[1095,1096,2195,3296]
    support=set(range(943))|set(sum(copies,[]))|{1063,1064}|set(anchors)
    check(len(support)==989,'support count')
    weight=[4**j*1024 for j in range(44)]
    clause={}
    for i,tile in enumerate(tiles):
        value=1+sum(weight[40:44])
        for t,edge in enumerate(tile):
            bits=edge+512
            for j in range(10):
                value+=((bits>>j)&1)*weight[10*t+j]
        clause[i]=value
    for t in range(4):
        for j in range(10): clause[copies[t][j]]=weight[10*t+j]
    for j,position in enumerate(anchors): clause[position]=weight[40+j]
    clause.update({1063:0,1064:0})
    mu=1022+sum(weight)
    coeff=defaultdict(int)
    for position in [30,62,1100,2200]: coeff[position]+=1
    for e,c in clause.items():
        if c:
            coeff[T1-e]+=c
            coeff[T2-e]+=c
    basis_count=0
    for j in range(10):
        for target,current,spatial,temporal in [
            (1013+j,983+j,None,1013+j),
            (1065+j,1003+j,1023+j,None)]:
            for e in support:
                check(coeff[target-e]==int(e==current),'copy current')
                check(int(e+H==target)==int(e==spatial),'copy spatial')
                check(int(e==target)==int(e==temporal),'copy temporal')
                basis_count+=3
    for target,current in [(2195,1095),(3296,1096)]:
        for e in support:
            check(coeff[target-e]==int(e==current),'anchor current')
            check(e+H!=target,'anchor spatial')
            check(int(e==target)==int(e==target),'anchor temporal')
            basis_count+=3
    for target in [T1,T2]:
        for e in support:
            check(coeff[target-e]==clause[e],'clause coefficient')
            check(e+H!=target,'clause spatial pollution')
            basis_count+=2
    coeff={e:c for e,c in coeff.items() if c}
    check(basis_count==69230,'basis count')
    diff={(x-y)%L for x in support for y in support}
    check((T2-T1)%L not in diff,'bands collide')
    anchor_intersection={(2195-e)%L for e in support}&{(3296-e)%L for e in support}
    check(anchor_intersection=={0},'anchor synchronization')
    product_support={x+y for x in support for y in coeff}
    computation_support=product_support|{x+H for x in support}|support
    zero_padding={e:(1<<119)-1 for e in range(8792,8799)}
    zero_padding[8799]=(1<<27)-1
    check(set(zero_padding).isdisjoint(computation_support),'padding nonzero')
    check(max(computation_support)==8791<min(zero_padding),'padding boundary')
    check(max(zero_padding)<L,'padding spills')
    mass=991*(2*sum(clause.values())+6)
    threshold=max(4*mass+8,2*mu+4,2*max(zero_padding.values())+4,16)
    check(threshold < 2**b,'carry threshold')
    check([n for n in range(944) if n&1022==0]==[0,1],'selector decoder')
    check([(a,c) for a in [0,1] for c in [0,1] if (a+c)%2==0]==[(0,0),(1,1)],'copy decoder')
    beta=(1<<d)-1
    DC=sum(c<<(b*e) for e,c in coeff.items())
    DR=1<<(b*H)
    MC=beta-sum(1<<(b*e) for e in support-{1})-(2<<(b*1063))
    MF=4+(mu<<(b*T1))+(mu<<(b*T2))
    for target in list(range(1013,1023))+list(range(1065,1075))+[2195,3296]: MF+=1<<(b*target)
    MF+=sum(c<<(b*e) for e,c in zero_padding.items())
    values={'beta':beta,'K':DC+(1<<d)*DR,'MC':MC,'MF_source':MF+beta}
    check(MC.bit_count()+MF.bit_count()==d,'population balance')
    check(MC.bit_count()==d-989 and MF.bit_count()==989,'individual populations')
    check(MC%4==2 and MF%8==4,'low residues')
    check(0<DC<1<<d and 0<MC<beta and 0<MF<beta,'magnitude')
    bytes_checked=0
    ports=[]
    for name,value in values.items():
        raw=(NEW/(name+'.bin')).read_bytes()
        compressed=(NEW/(name+'.bin.gz')).read_bytes()
        check(raw==gzip.decompress(compressed),'gzip mismatch')
        check(int.from_bytes(raw,'little')==value,'literal coefficient mismatch')
        check(len(raw)==(value.bit_length()+7)//8,'not minimal unsigned')
        bytes_checked+=len(raw)
        ports.append({'name':name,'bit_length':value.bit_length(),'sha256':hashlib.sha256(raw).hexdigest()})
    lam=2341
    step=2340
    check(d==11**2*13*677 and all(isprime(p) for p in [11,13,677,lam]),'primes')
    mods=[121,13,677,lam]
    orders={str(m):order_by_cycle(pow(2,d,m),m,m) for m in mods}
    check(orders=={'121':10,'13':12,'677':52,'2341':60},'orders')
    check(lcm(*[orders[str(m)] for m in [121,13,677]])==780,'order d')
    check(all(step%o==0 for o in orders.values()),'order divides step')
    check(pow(2,d*step,d)==1,'mod d period')
    lift=pow(2,d*step,lam*lam)
    check(lift%lam==1 and lift!=1,'valuation is not one')
    residues=[]
    for p in [11,13,677,lam]:
        Bmod=pow(2,d,p)
        DCmod=sum((c%p)*pow(2,b*e,p) for e,c in coeff.items())%p
        DRmod=pow(2,b*H,p)
        qf=(Bmod*Bmod-1)%p
        bracket=(1+Bmod*DCmod+Bmod*Bmod*(DRmod+1))%p
        check(qf!=0 and bracket!=0,'Gamma not a unit')
        residues.append({'prime':p,'B':Bmod,'DC':DCmod,'DR':DRmod,'q_squared_minus_one':qf,'bracket':bracket})
    check(residues==actual['padding_controller']['unit_residues'],'reported unit table mismatch')
    receipt={'status':'PASS','new_generator_executed_or_imported':False,
        'new_generator_sha256':hashlib.sha256((NEW/'build_coefficients.py').read_bytes()).hexdigest(),
        'frozen_tile_list_matches':True,'native_basis_checks':basis_count,
        'band_gap_not_in_cyclic_difference_set':True,'anchor_intersection':[0],
        'all_added_padding_cells_structurally_zero':True,'max_computation_exponent':8791,
        'mass':mass,'carry_threshold':threshold,'radix':2**b,
        'mask_populations':[MC.bit_count(),MF.bit_count()],
        'literal_ports_match_independent_recipe':ports,'raw_bytes_checked':bytes_checked,
        'orders_by_direct_cycle':orders,'valuation_witness':lift,
        'valuation_quotient':(lift-1)//lam,'unit_residues':residues,
        'mathematical_review':'General Boolean controller and signed canonical interface reviewed in COEFFICIENTS_INDEPENDENT_REVIEW.md; finite checks do not replace the inherited compiler/Pell proofs.'}
    (HERE/'COEFFICIENTS_INDEPENDENT_AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__': main()
