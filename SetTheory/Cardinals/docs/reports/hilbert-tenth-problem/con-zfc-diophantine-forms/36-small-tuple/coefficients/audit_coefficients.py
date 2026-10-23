#!/usr/bin/env python3
"""Independent coefficient reader; deliberately does not import the builder."""
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
        raw=gzip.decompress((P/item['file']).read_bytes())
        check(sha256(raw).hexdigest()==item['sha256'],'payload hash')
        value=int.from_bytes(raw,'little')
        check(len(raw)==item['raw_bytes'] and value.bit_length()==item['bits'],'payload dimensions')
        decoded[item['port']]=value
    b,L,d=115,8801,1012115
    rho=1<<b; B=decoded['beta']+1
    check(B==1<<d and d==b*L,'base definition')
    DR,DC=divmod(decoded['K'],B)
    check(DR==1<<(115*42),'transport')
    native=decoded['MF_source']-decoded['beta']
    check(0<native<B-1 and 0<decoded['MC']<B-1,'native range')
    check(native.bit_count()==986,'high population')
    check(decoded['MC'].bit_count()==d-986,'low population')
    check(native%8==4 and decoded['MC']%4==2,'native residues')
    tilebytes=(P/'wang943_tiles.json').read_bytes()
    check(sha256(tilebytes).hexdigest()==
          '66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f','tile source hash')
    tiles=json.loads(tilebytes)
    weights=[1024*4**j for j in range(41)]
    widths=(9,10,9,10);occupancy=(256,512,256,512);starts=(0,9,19,28)
    check(all(max(t[s] for t in tiles)<occupancy[s] for s in range(4)),'label capacity')
    coefficients={}
    for i,tile in enumerate(tiles):
        payload=sum(((x+occupancy[s])//(1<<j)%2)*weights[starts[s]+j]
                    for s,x in enumerate(tile) for j in range(widths[s]))
        coefficients[i]=1+payload+sum(weights[38:])
    for s,offset in enumerate((1023,1013,1003,983)):
        for j in range(widths[s]):
            coefficients[offset+j]=weights[starts[s]+j]
    for j,e in enumerate((1095,2195,3296)):
        coefficients[e]=weights[38+j]
    coefficients[1063]=coefficients[1064]=0
    support=set(coefficients)
    mu=1022+sum(weights)
    desired_dc=sum(rho**s for s in (30,62,1100,2201))
    for e,c in coefficients.items():
        desired_dc+=c*(rho**(4393-e)+rho**(5495-e))
    check(DC==desired_dc,'full DC reconstruction')
    desired_mc=B-1-sum(rho**e for e in support-{1})-2*rho**1063
    check(decoded['MC']==desired_mc,'full MC reconstruction')
    targets=list(range(1013,1023))+list(range(1065,1074))+[2195,3296]
    desired_high=4+mu*(rho**4393+rho**5495)+sum(rho**t for t in targets)
    desired_high+=((1<<113)-1)*sum(rho**e for e in range(8792,8799))
    desired_high+=((1<<73)-1)*rho**8799
    check(native==desired_high,'full high mask reconstruction')
    dc_digits={}
    n=DC;e=0
    while n:
        n,r=divmod(n,rho)
        if r:dc_digits[e]=r
        e+=1
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
    check(max(4*mass+8,2*mu+4,2*((1<<113)-1)+4,16)<rho,'carry bound')
    check(max(dc_digits)+max(support)==8791,'zero-padding separation')
    ell=3433;k=3432
    check(all(ell%p for p in range(2,isqrt(ell)+1)),'padding prime')
    check(d==5*13*23*677 and k%1716==0,'factorization and period')
    order_certificates=[(5,4,[2]),(13,12,[2,3]),(23,11,[11]),(677,52,[2,13]),(3433,132,[2,3,11])]
    for modulus,order,prime_factors in order_certificates:
        check(pow(2,d*order,modulus)==1,'order upper bound')
        check(all(pow(2,d*(order//p),modulus)!=1 for p in prime_factors),
              'exact multiplicative order')
    lift=pow(2,d*k,ell*ell)
    check(lift==1973976 and lift%ell==1 and lift!=1,'valuation certificate')
    rows=[]
    for p in (5,13,23,677,ell):
        bp=B%p
        a=(bp*bp-1)%p
        c=(1+bp*(DC%p)+bp*bp*(DR%p+1))%p
        check(a!=0 and c!=0,'actual numerical coefficient unit')
        rows.append({'p':p,'B_squared_minus_one':a,'bracket':c})
    result=dict(status='PASS',payloads=4,full_integer_reconstructions=4,
                native_basis_identities=nchecks,exact_prime_and_order_certificates=True,
                actual_coefficient_unit_checks=rows,semantic_scope='Finite interface checks only; see PROOF.md.')
    (P/'INDEPENDENT_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    run()
