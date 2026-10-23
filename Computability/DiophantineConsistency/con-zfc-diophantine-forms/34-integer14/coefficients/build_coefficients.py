#!/usr/bin/env python3
"""Round5 mixed/parity/unrounded coefficient construction, newly authored.
Uses Python standard library. Never simulates the blank machine.
"""
import argparse, gzip, hashlib, json, math
from pathlib import Path
from collections import defaultdict
HERE=Path(__file__).resolve().parent
PIN='8c6eec9d19ef80538c8e61ff6e0180040583446a'
def require(condition, message):
    if not condition: raise ValueError(message)
def sha(data): return hashlib.sha256(data).hexdigest()
def prime(n):
    return n>=2 and all(n%i for i in range(2,math.isqrt(n)+1))
def ordered_tiles():
    raw=(HERE/'k215.tm').read_bytes()
    require(sha(raw)=='fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090','machine hash')
    rows=[line.split() for line in raw.decode().splitlines() if line and not line.startswith('#')]
    actions=[(int(q),int(b),int(w),mv,int(t)) for q,b,w,mv,t in rows]
    require(len(actions)==430 and len({(a[0],a[1]) for a in actions})==430,'actions')
    right=sorted({a[4] for a in actions if a[3]=='R'});left=sorted({a[4] for a in actions if a[3]=='L'})
    require((len(right),len(left))==(199,45),'signals')
    signalr={q:i+6 for i,q in enumerate(right)};signall={q:i+205 for i,q in enumerate(left)}
    hd=lambda q,b:2*q+2+b
    ts=set()
    for q,b,w,mv,t in actions:
        ts.add((0,hd(q,b),signalr[t],w) if mv=='R' else (signall[t],hd(q,b),0,w))
    for bit in (0,1):
        ts.update([(0,hd(215,bit),0,hd(215,bit)),(0,bit,0,bit)])
        for q in right:ts.add((signalr[q],bit,0,hd(q,bit)))
        for q in left:ts.add((0,bit,signall[q],hd(q,bit)))
    ts.update((0,n,0,438) for n in (0,1,432,433))
    ts.update([(2,434,2,0),(2,435,3,1),(3,436,4,188),(4,436,4,0)])
    ts.update((1,438,1,n) for n in (434,435,436))
    ts.update((a,437,b,437) for a in (0,1,4) for b in (0,1,2))
    start=(2,435,3,1);bad=(5,0,0,0);ts.add(bad)
    result=[start,bad]+sorted(ts-{start,bad})
    literal=json.loads((HERE/'wang943_tiles.json').read_text())
    require(len(result)==943 and [list(t) for t in result]==literal,'full tile equality')
    return result

def construct():
    tiles=ordered_tiles(); offsets=(1020,1000,980,960); anchors=(1095,1096,2195,3296)
    weight=lambda j:2**(10+2*j)
    c={}
    for i,tile in enumerate(tiles):
        c[i]=1+sum(weight(10*t+j) for t,label in enumerate(tile) for j in range(10) if ((label+512)>>j)&1)+sum(weight(j) for j in range(40,44))
    for t,offset in enumerate(offsets):
        for j in range(10): c[offset+2*j]=weight(t*10+j)
    c.update({a:weight(40+j) for j,a in enumerate(anchors)});c.update({1063:0,1064:0})
    E=set(c);require(len(E)==989,'support')
    dc=defaultdict(int)
    for shift in (40,41,1100,2200): dc[shift]+=1
    for e,v in c.items():
        if v:
            for target in (4393,5495):dc[target-e]+=v
    mu=1022+sum(weight(j) for j in range(44))
    b,L=121,8801;d=b*L;rho=2**b;B=2**d
    padding={e:2**119-1 for e in range(8792,8799)};padding[8799]=2**27-1
    checks=0
    targetrows=[(1000+2*j,960+2*j,None,1000+2*j) for j in range(10)]+[(1021+2*j,980+2*j,1020+2*j,None) for j in range(10)]+[(2195,1095,None,2195),(3296,1096,None,3296)]
    for target,a,r,t in targetrows:
        for e in E:
            require(dc.get(target-e,0)==int(e==a),'DC basis');require(int(e+1==target)==int(e==r),'DR basis');require(int(e==target)==int(e==t),'temporal basis');checks+=3
    for target in (4393,5495):
        for e in E:
            require(dc.get(target-e,0)==c[e],'clause basis');require(e+1!=target,'clause DR');checks+=2
    require(not ({(4393-e)%L for e in E}&{(5495-e)%L for e in E}),'clean bands')
    require({(2195-e)%L for e in E}&{(3296-e)%L for e in E}=={0},'anchor pair')
    mass=991*(2*sum(c.values())+6)
    require(max(dc)+max(E)==8791<min(padding) and max(padding)<L,'zero padding geometry')
    require(max(4*mass+8,2*mu+4,2*max(padding.values())+4,16)<rho,'carry bound')
    require(3*rho//4+mass<=rho-2 and rho//2+1+mass<=rho-2,'strict slack')
    require([n for n in range(944) if n&1022==0]==[0,1],'selector decoding')
    require([(a,b) for a in(0,1) for b in(0,1) if (a+b)&1==0]==[(0,0),(1,1)],'copy decoding')
    DC=sum(v<<(b*e) for e,v in dc.items());DR=rho
    MC=B-1-sum(1<<(b*e) for e in E if e!=1)-(2<<(b*1063))
    MF=4+(mu<<(b*4393))+(mu<<(b*5495))
    MF+=sum(1<<(b*(1000+2*j)) for j in range(10))+sum(1<<(b*(1021+2*j)) for j in range(10))
    MF+=(1<<(b*2195))+(1<<(b*3296))+sum(v<<(b*e) for e,v in padding.items())
    require(0<MC<B-1 and 0<MF<B-1,'mask bounds')
    require((MC%4,MF%8,MC.bit_count(),MF.bit_count())==(2,4,d-989,989),'mask populations')
    ports={'beta':B-1,'K':DC+B*DR,'MC':MC,'MF_source':MF+B-1}
    lam,k=2341,2340;factors={11:2,13:1,677:1};orders={121:10,13:12,677:52}
    require(math.prod(p**a for p,a in factors.items())==d and all(prime(p) for p in factors),'d factorization')
    require(prime(lam),'controller prime')
    for m,o in orders.items():
        require(pow(B,o,m)==1 and all(pow(B,j,m)!=1 for j in range(1,o)),'exact order')
    require(k%math.lcm(*orders.values())==0 and k==lam-1,'order controller')
    lifting=pow(B,k,lam*lam);require(lifting==2556373 and lifting%lam==1 and lifting!=1,'non-Wieferich')
    units={}
    for p in [11,13,677,lam]:
        vals=[B%p,(B*B-1)%p,(1+B*DC+B*B*(DR+1))%p]
        require(vals[1]!=0 and vals[2]!=0,'rank unit');units[str(p)]=vals
    return ports,{'basis_convolution_checks':checks,'b':b,'L':L,'d':d,'mass_bits':mass.bit_length(),'threshold_bits':max(4*mass+8,2*mu+4,2*max(padding.values())+4,16).bit_length(),'max_product_exponent':8791,'padding_exponents':list(padding),'padding_popcount':sum(v.bit_count() for v in padding.values()),'d_factorization':factors,'orders':orders,'lambda':lam,'k':k,'non_Wieferich_residue':lifting,'unit_rows':units}

def emit(out):
    ports,audit=construct();out.mkdir(parents=True,exist_ok=True);manifest={}
    for name,val in ports.items():
        raw=val.to_bytes((val.bit_length()+7)//8,'little');compressed=gzip.compress(raw,mtime=0)
        (out/(name+'.bin')).write_bytes(raw);(out/(name+'.bin.gz')).write_bytes(compressed)
        manifest[name]={'bits':val.bit_length(),'bytes':len(raw),'sha256':sha(raw),'gzip_bytes':len(compressed),'gzip_sha256':sha(compressed)}
    receipt={'status':'PASS','source_pin':PIN,'variant':'mixed-parity-unrounded-1064921','B':'2^1064921','ports':{'Bm1':'beta','Kconstant':'K','MC':'MC','MF':'MF_source'},'warning':'Replace the complete tuple. MF is shifted MF_native+B-1.','ordinary_mathematical_adapter':True,'new_kernel_certificate':False,'audit':audit,'payloads':manifest,'raw_bytes':sum(v['bytes'] for v in manifest.values()),'gzip_bytes':sum(v['gzip_bytes'] for v in manifest.values())}
    (out/'COEFFICIENT_BINDING.json').write_text(json.dumps(receipt,indent=2)+'\n');return receipt
if __name__=='__main__':
    require(__debug__,'run without -O/-OO')
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=HERE/'payloads');args=ap.parse_args();print(json.dumps(emit(args.output),indent=2))
