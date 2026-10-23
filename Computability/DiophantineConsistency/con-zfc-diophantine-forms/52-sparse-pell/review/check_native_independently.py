#!/usr/bin/env python3
"""Independent round-7 check of published 39/44 finite coefficient data.

Reads inert JSON only. No upstream program is imported or executed.
This is a finite interface/data check, not a new unbounded compiler proof.
"""
from pathlib import Path
from hashlib import sha1, sha256
from math import isqrt, lcm
import json
import gzip

HERE = Path(__file__).resolve().parent
SRC = HERE / 'sources'
def require(condition, message):
    if not condition:
        raise ValueError(message)

def factor(n):
    ans = []
    p = 2
    while p*p <= n:
        if n % p == 0:
            ans.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        ans.append(n)
    return ans

def order(a, p):
    n = p-1
    for q in factor(n):
        while n % q == 0 and pow(a, n//q, p) == 1:
            n //= q
    require(pow(a,n,p)==1, 'order value')
    return n

def main():
    pins = json.loads((HERE/'SOURCE_PINS.json').read_text())
    for item in pins['files']:
        raw = (HERE/item['local_path']).read_bytes()
        gh = sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        require(gh == item['blob_sha'], 'source bytes: '+item['local_path'])

    tile_raw=(SRC/'35-cancel12/coefficients/wang943_tiles.json').read_bytes()
    require(sha256(tile_raw).hexdigest()=='66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f','tile hash')
    tiles=json.loads(tile_raw)
    require(len(tiles)==len(set(map(tuple,tiles)))==943,'distinct tiles')
    b,L=67,8807
    d=b*L
    rho=1<<b
    B=1<<d
    c={}
    for i,(w,n,e,s) in enumerate(tiles):
        v=w+(n<<8)+(e<<17)+(s<<25)+(127<<34)
        require((127<<34)<=v<(1<<41),'word interval')
        c[i]=1+1024*((1<<41)-v)
    for off,bit0,width,occ in [(1023,0,8,34),(1013,8,9,35),(1003,17,8,36),(983,25,9,37)]:
        for j in range(width):
            c[off+j]=1<<(10+bit0+j)
        c[off+width]=1<<(10+occ)
    for pos,bit in [(1095,38),(2195,39),(3296,40)]:
        c[pos]=1<<(10+bit)
    c[1063]=c[1064]=0
    E=set(c)
    require(len(E)==986,'support cardinality')
    mu=(1<<51)-2
    require([n for n in range(944) if n&1022==0]==[0,1],'selector count')
    mutations=0
    for i,tile in enumerate(tiles):
        v=((1<<51)+1-c[i])//1024
        require((c[i]+1024*v)&mu==0,'valid word')
        for bit in range(41):
            require((c[i]+1024*(v^(1<<bit)))&mu!=0,'one-bit invalid word')
            mutations+=1
    dc={e:1 for e in (30,62,1100,2201)}
    for e,k in c.items():
        for t in (4393,5495):
            dc[t-e]=dc.get(t-e,0)+k
    targets=[(1013+j,983+j,None,1013+j) for j in range(10)]
    targets += [(1065+j,1003+j,1023+j,None) for j in range(9)]
    targets += [(2195,1095,None,2195),(3296,1095,None,3296)]
    identities=0
    for t,cur,spatial,temporal in targets:
        for e in E:
            require(dc.get(t-e,0)==int(e==cur),'current basis')
            require(int(e+42==t)==int(e==spatial),'spatial basis')
            require(int(e==t)==int(e==temporal),'temporal basis')
            identities+=3
    for t in (4393,5495):
        for e in E:
            require(dc.get(t-e,0)==c[e],'clause basis')
            require(e+42!=t,'clause spatial')
            identities+=2
    require({(4393-e)%L for e in E}.isdisjoint({(5495-e)%L for e in E}),'clean band intersection')
    require({(2195-e)%L for e in E}&{(3296-e)%L for e in E}=={0},'anchor intersection')
    positive_dc={e:k for e,k in dc.items() if k}
    require(max(positive_dc)+max(E)==8791,'unshifted support end')
    mass=(len(E)+2)*(2*sum(c.values())+6)
    require(mass==29613572795083482608,'mass')
    require(4*mass+8<rho and 2*mu+4<rho,'carry inequalities')
    pad={e:(1<<65)-1 for e in range(8792,8805)}
    pad[8805]=(1<<19)-1
    require(sum(v.bit_count() for v in pad.values())==864,'pad population')
    require(2*max(pad.values())+4<rho,'padding carry')
    DC=sum(k<<(b*e) for e,k in positive_dc.items())
    DR=1<<(42*b)
    MC=B-1-sum(1<<(b*e) for e in E if e!=1)-(2<<(1063*b))
    MF=4+(mu<<(4393*b))+(mu<<(5495*b))
    MF+=sum(1<<(t*b) for t,*_ in targets)+sum(k<<(b*e) for e,k in pad.items())
    require(MC.bit_count()==d-986 and MF.bit_count()==986,'balance')
    require(MC%4==2 and MF%8==4,'low congruences')
    require(0<DC<B and 0<MC<B-1 and 0<MF<B-1,'range bounds')
    ports={'beta':B-1,'K':DC+B*DR,'MC':MC,'MF_source':MF+B-1}
    rows=[]
    out=HERE.parent/'coefficients'
    out.mkdir(exist_ok=True)
    for name,value in ports.items():
        raw=value.to_bytes((value.bit_length()+7)//8,'little')
        compressed=gzip.compress(raw,mtime=0)
        (out/(name+'.bin')).write_bytes(raw)
        (out/(name+'.bin.gz')).write_bytes(compressed)
        rows.append({'port':name,'bits':value.bit_length(),'bytes':len(raw),'sha256':sha256(raw).hexdigest(),'gzip_sha256':sha256(compressed).hexdigest(),'gzip_bytes':len(compressed),'file':name+'.bin','gzip_file':name+'.bin.gz'})
    for binding_file in ['44-b4-sparse/native/COEFFICIENT_BINDING.json','39-direct10/optional_compact/coefficients/COEFFICIENT_BINDING.json']:
        bind=json.loads((SRC/binding_file).read_text())
        indexed={r['port']:r for r in bind['materialization']['files']}
        for row in rows:
            require(row['sha256']==indexed[row['port']]['sha256'],'raw tuple hash '+binding_file)
            require(row['bits']==indexed[row['port']]['bits'],'raw tuple bits')
    lam=581197
    require(all(lam%p for p in range(2,isqrt(lam)+1)),'lambda prime')
    ords={p:order(B%p,p) for p in (67,8807,lam)}
    require(ords=={67:66,8807:4403,lam:581196},'orders')
    require((lam-1)%lcm(ords[67],ords[8807])==0,'controller period')
    lift=pow(2,d*(lam-1),lam*lam)
    require(lift==182964883980 and lift%lam==1 and lift!=1,'controller lift')
    units=[]
    for p in (67,8807,lam):
        H0=(1+B*DC+B*B*(DR+1))%p
        require((B*B-1)%p!=0 and H0!=0,'controller unit')
        units.append({'prime':p,'B':B%p,'B_squared_minus_one':(B*B-1)%p,'H0':H0})
    receipt={'status':'PASS','scope':'Independent finite checks only; no upstream scripts executed; no unbounded compiler proof checked','source_files_verified':len(pins['files']),'tuple_39_and_44_identical':True,'d':d,'basis_identities':identities,'single_bit_mutations':mutations,'mass':mass,'ports':rows,'raw_bytes':sum(r['bytes'] for r in rows),'orders':ords,'unit_residues':units}
    manifest={'schema':'proveit-round7-coherent-native-tuple-v1','instance':'wang943-complement67-shared-anchor-length8807-prime581197','source_pin':pins['pin'],'definition_source':'review/sources/44-b4-sparse/native/PROOF.md','matching_source':'review/sources/39-direct10/optional_compact/coefficients/PROOF.md','builder':'../review/check_native_independently.py','ports_path_base':'directory containing this JSON','encoding':'minimal unsigned little-endian bytes, optionally gzip compressed','base':'2^590069','radix':'2^67','cell_length':8807,'port_aliases':{'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'},'warning':'The entire four-port tuple is mandatory. MF_source is already shifted by B-1. The source compiler and calibration remain inherited mathematical dependencies.','ports':rows,'parent_file':'../review/sources/31-sun10/quartic31/quartic31_system60.json','parent_sha256':sha256((SRC/'31-sun10/quartic31/quartic31_system60.json').read_bytes()).hexdigest(),'parent_domain':'31 strictly positive integers','transport_convention':'z_old=z+1, justified on zeros by canonical compiler bounds, not arbitrary positive-coordinate surjectivity','finite_check_receipt':'../review/NATIVE_INDEPENDENT_CHECKS.json'}
    (out/'COEFFICIENT_BINDING.json').write_text(json.dumps(manifest,indent=2)+'\n')
    (HERE/'NATIVE_INDEPENDENT_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':
    main()
