#!/usr/bin/env python3
"""Read and reconstruct the new integer ports without importing their builder."""
from pathlib import Path
from hashlib import sha256
from math import isqrt
import gzip
import json

P=Path(__file__).resolve().parent
def check(ok,label):
    if not ok:
        raise ValueError(label)

def run():
    manifest=json.loads((P/'COEFFICIENT_BINDING.json').read_text())
    decoded={}
    for item in manifest['materialization']['files']:
        packed=(P/item['file']).read_bytes()
        check(sha256(packed).hexdigest()==item['gzip_sha256'],'compressed payload hash')
        raw=gzip.decompress(packed)
        check(sha256(raw).hexdigest()==item['sha256'],'payload hash')
        value=int.from_bytes(raw,'little')
        check(len(raw)==item['raw_bytes'] and value.bit_length()==item['bits'],'payload dimensions')
        decoded[item['port']]=value
    b,L,d=77,8807,678139
    rho=1<<b; B=decoded['beta']+1
    check(B==1<<d and d==b*L,'base definition')
    DR,DC=divmod(decoded['K'],B)
    check(DR==1<<(77*42),'transport')
    native=decoded['MF_source']-decoded['beta']
    check(0<native<B-1 and 0<decoded['MC']<B-1,'native range')
    check(native.bit_count()==986,'high population')
    check(decoded['MC'].bit_count()==d-986,'low population')
    check(native%8==4 and decoded['MC']%4==2,'native residues')
    tilebytes=(P/'wang943_tiles.json').read_bytes()
    check(sha256(tilebytes).hexdigest()==
          '66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f','tile source hash')
    tiles=json.loads(tilebytes)
    widths=(9,10,9,10);starts=(16,47,37,26)
    check(all(max(t[s] for t in tiles)<1<<(widths[s]-1) for s in range(4)),
          'occupied label high bit')
    coefficients={}
    for i,tile in enumerate(tiles):
        coefficients[i]=1+sum((x+1)*2**starts[s] for s,x in enumerate(tile))
        coefficients[i]+=2**10+2**12+2**14
    for s,offset in enumerate((1023,1013,1003,983)):
        for j in range(widths[s]):
            coefficients[offset+j]=2**(starts[s]+j)
    for j,e in enumerate((1095,2195,3296)):
        coefficients[e]=2**(10+2*j)
    coefficients[1063]=coefficients[1064]=0
    support=set(coefficients)
    mu=1022+2**10+2**12+2**14
    mu+=sum((2**l-1)*2**s for l,s in zip(widths,starts))
    desired_dc=sum(1<<(77*s) for s in (30,62,1100,2201))
    for e,c in coefficients.items():
        desired_dc+=c*((1<<(77*(4393-e)))+(1<<(77*(5495-e))))
    check(DC==desired_dc,'full DC reconstruction')
    desired_mc=B-1-sum(1<<(77*e) for e in support-{1})-(2<<(77*1063))
    check(decoded['MC']==desired_mc,'full MC reconstruction')
    targets=list(range(1013,1023))+list(range(1065,1074))+[2195,3296]
    desired_high=4+mu*((1<<(77*4393))+(1<<(77*5495)))
    desired_high+=sum(1<<(77*t) for t in targets)
    desired_high+=((1<<75)-1)*sum(1<<(77*e) for e in range(8792,8803))
    desired_high+=((1<<39)-1)<<(77*8803)
    check(native==desired_high,'full high mask reconstruction')
    dc_digits={e:(DC>>(77*e))&(rho-1) for e in range(5496)}
    expected=[]
    for j in range(10):
        expected.append((1013+j,983+j,None,1013+j))
        if j<9: expected.append((1065+j,1003+j,1023+j,None))
    expected.extend([(2195,1095,None,2195),(3296,1095,None,3296)])
    nchecks=0
    for t,current,spatial,temporal in expected:
        for e in support:
            check(dc_digits.get(t-e,0)==(e==current),'decoded DC native identity')
            check((e+42==t)==(e==spatial),'decoded DR native identity')
            check((e==t)==(e==temporal),'temporal native identity')
            nchecks+=3
    for t in (4393,5495):
        for e in support:
            check(dc_digits.get(t-e,0)==coefficients[e],'decoded clause identity')
            check(e+42!=t,'decoded DR clause identity')
            nchecks+=2
    check({(4393-e)%L for e in support}.isdisjoint({(5495-e)%L for e in support}),
          'rotation separation')
    check({(2195-e)%L for e in support}&{(3296-e)%L for e in support}=={0},
          'anchor intersection')
    mass=988*(2*sum(coefficients.values())+6)
    check(max(4*mass+8,2*mu+4,2*((1<<75)-1)+4,16)<rho,'carry bound')
    check(max(e for e,c in dc_digits.items() if c)+max(support)==8791,
          'zero-padding separation')
    ell=56611;k=56610
    for prime in (7,11,8807,ell):
        check(all(prime%p for p in range(2,isqrt(prime)+1)),'prime certificate')
    check(d==7*11*8807 and k==3*18870,'factorization and period')
    order_certificates=[(7,3,[3]),(11,10,[2,5]),(8807,629,[17,37]),
                        (56611,6290,[2,5,17,37])]
    for modulus,order,prime_factors in order_certificates:
        check(pow(2,d*order,modulus)==1,'order upper bound')
        check(all(pow(2,d*(order//p),modulus)!=1 for p in prime_factors),
              'exact multiplicative order')
    lift=pow(2,d*k,ell*ell)
    check(lift==1810929280 and lift%ell==1 and lift!=1,'valuation certificate')
    rows=[]
    for p in (7,11,8807,ell):
        bp=B%p
        a=(bp*bp-1)%p
        c=(1+bp*(DC%p)+bp*bp*(DR%p+1))%p
        check(a!=0 and c!=0,'actual numerical coefficient unit')
        rows.append({'p':p,'B_squared_minus_one':a,'bracket':c})
    result=dict(status='PASS',payloads=4,full_integer_reconstructions=4,
                native_basis_identities=nchecks,exact_prime_and_order_certificates=True,
                actual_coefficient_unit_checks=rows,
                semantic_scope='Finite interface checks only; universal argument in PROOF.md.')
    (P/'INDEPENDENT_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    run()
