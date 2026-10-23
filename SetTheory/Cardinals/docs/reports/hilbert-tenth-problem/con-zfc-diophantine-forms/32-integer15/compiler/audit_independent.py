#!/usr/bin/env python3
"""Read-only independent reconstruction of the new four fixed integers.

Does not import or execute build_coefficients.py. Only inert JSON and binary
payloads are read. The universal compiler proof remains a mathematical
dependency; finite arithmetic checks cannot decide Con(ZFC).
"""
from pathlib import Path
import gzip
import hashlib
import json
import math

P=Path(__file__).resolve().parent

def require(ok,message):
    if not ok:
        raise ValueError(message)

def main():
    table=json.loads((P/'upstream/wang943_tiles.json').read_text())
    receipt=json.loads((P/'coefficients/COEFFICIENT_BINDING.json').read_text())
    require(len(table)==943 and len({tuple(t) for t in table})==943,'bad tile table')
    b,L,d=121,8801,1064921
    B=1<<d
    support=set(range(943))|set(range(983,993))|set(range(1003,1033))|{1063,1064,1095,1096,2195,3296}
    weights=[4**j*1024 for j in range(44)]
    clause={}
    for i,tile in enumerate(table):
        payload=0
        for s,label in enumerate(tile):
            for j in range(10):
                if (label+512)//(2**j)%2:
                    payload+=weights[10*s+j]
        clause[i]=1+payload+sum(weights[40:])
    for s,offset in enumerate((1023,1013,1003,983)):
        for j in range(10):
            clause[offset+j]=weights[10*s+j]
    for j,e in enumerate((1095,1096,2195,3296)):
        clause[e]=weights[40+j]
    clause[1063]=clause[1064]=0
    require(set(clause)==support,'native support changed')
    mu=1022+sum(weights)
    dc={30:1,62:1,1100:1,2200:1}
    for t in(4393,5495):
        for e in support:
            dc[t-e]=dc.get(t-e,0)+clause[e]
    dc={e:c for e,c in dc.items() if c}
    DC=sum(c*(1<<(b*e)) for e,c in dc.items())
    DR=1<<(b*42)
    output_bits=[2]+[b*(1013+j) for j in range(10)]+[b*(1065+j) for j in range(10)]+[b*2195,b*3296]
    output_bits += [b*t+j for t in(4393,5495) for j in range(mu.bit_length()) if mu>>j&1]
    output_bits += [b*t+j for t in range(8792,8799) for j in range(119)]
    output_bits += [b*8799+j for j in range(27)]
    require(len(output_bits)==len(set(output_bits))==989,'mask positions collide')
    MF_native=sum(1<<j for j in output_bits)
    input_removed=[b*e for e in support if e!=1]+[b*1063+1]
    require(len(input_removed)==len(set(input_removed))==989,'input exclusions collide')
    MC=(B-1)^sum(1<<j for j in input_removed)
    expected={'beta':B-1,'K':DC+B*DR,'MC':MC,'MF_source':MF_native+B-1}
    require(DC<B and 0<MC<B-1 and 0<MF_native<B-1,'native ranges invalid')
    require(MC%4==2 and MF_native%8==4,'wrong native low bits')
    require(MC.bit_count()+MF_native.bit_count()==d,'wrong native populations')
    outputs=[]
    for f in receipt['files']:
        zipped=(P/'coefficients'/f['file']).read_bytes()
        raw=gzip.decompress(zipped)
        value=int.from_bytes(raw,'little')
        require(value==expected[f['port']],'independent recipe differs from payload')
        require(raw[-1]!=0 and len(raw)==f['bytes'],'nonminimal payload encoding')
        require(hashlib.sha256(raw).hexdigest()==f['sha256'],'raw hash changed')
        require(hashlib.sha256(zipped).hexdigest()==f['gzip_sha256'],'gzip hash changed')
        require(value.bit_length()==f['bit_length'],'wrong bit length')
        outputs.append({'port':f['port'],'bits':value.bit_length(),'bytes':len(raw),'sha256':f['sha256']})
    targets={1013+j:({983+j},set(),{1013+j}) for j in range(10)}
    targets.update({1065+j:({1003+j},{1023+j},set()) for j in range(10)})
    targets[2195]=({1095},set(),{2195});targets[3296]=({1096},set(),{3296})
    checks=0
    for t,(a,c,y) in targets.items():
        for e in support:
            require(dc.get(t-e,0)==int(e in a),'DC basis identity failed')
            require((e+42==t)==(e in c),'DR basis identity failed')
            require((e==t)==(e in y),'temporal basis identity failed')
            checks+=3
    for t in(4393,5495):
        for e in support:
            require(dc.get(t-e,0)==clause[e] and e+42!=t,'clause identity failed')
            checks+=2
    require({(4393-e)%L for e in support}.isdisjoint({(5495-e)%L for e in support}),'rotation bands overlap')
    require({(2195-e)%L for e in support}&{(3296-e)%L for e in support}=={0},'anchor intersection failed')
    mass=991*(2*sum(clause.values())+6)
    require(4*mass+8<1<<b and 2*mu+4<1<<b,'insufficient computation carry bound')
    require(2*((1<<119)-1)+4<1<<b,'insufficient filler bound')
    require(max(dc)+max(support)==8791<8792 and 8799<L,'invalid filler separation')
    ell,k=2341,2340
    require(d==11**2*13*677 and all(all(p%q for q in range(2,math.isqrt(p)+1)) for p in(11,13,677,ell)), 'factor or prime certificate failed')
    require(math.gcd(d,ell)==1 and k==ell-1,'controller shape failed')
    require(pow(2,d*780,d)==1 and all(pow(2,d*(780//p),d)!=1 for p in(2,3,5,13)), 'order certificate failed')
    require(k%780==0,'controller step does not preserve fixed factor')
    residue=pow(2,d*k,ell**2)
    require(residue==2556373 and residue%ell==1 and residue!=1,'valuation certificate failed')
    units=[]
    for p in(11,13,677,ell):
        br=B%p;dcr=DC%p;drr=DR%p
        a=(br*br-1)%p;h=(1+br*dcr+br*br*(drr+1))%p
        require(a and h,'control multiplier fails to be a unit')
        units.append({'prime':p,'B':br,'DC':dcr,'DR':drr,'qfactor':a,'bracket':h})
    result=dict(status='PASS',imports_builder=False,read_only=True,d=d,
                literal_payloads_match_independent_recipe=True,files=outputs,
                total_raw_bytes=sum(x['bytes'] for x in outputs),native_population=989,
                basis_checks=checks,controller_prime=ell,controller_step=k,order_mod_d=780,
                valuation_residue=residue,unit_residues=units,
                scope='Exact finite arithmetic; semantic proof and K215 endpoint remain inherited.')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
