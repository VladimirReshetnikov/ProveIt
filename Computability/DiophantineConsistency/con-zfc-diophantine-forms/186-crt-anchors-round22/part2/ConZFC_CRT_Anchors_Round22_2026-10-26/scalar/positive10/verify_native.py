#!/usr/bin/env python3
"""Independent finite checks of the Start-only coefficient redesign.

This checker imports no producer.  It reconstructs the four integers from
the closed sums and reads the old weights only as fixed source data.
"""
from pathlib import Path
import json, hashlib, math, sys

ROOT = Path(__file__).resolve().parent
CONFIG = {
    '4159': dict(folder='compact66/intermediate4159',flag=1042,left=2053,right=3096,padding=4139,length=4159,order=2079,factors=[3,7,11],units=[13,1090,348345],lam=478171),
    '4127': dict(folder='native4127',flag=1031,left=2042,right=3074,padding=4106,length=4127,order=2063,factors=[2063],units=[9,3487,153928],lam=474491),
}

def require(test, message):
    if not test:
        raise ValueError(message)

def prime(n):
    return n >= 2 and all(n % k for k in range(2, math.isqrt(n) + 1))

ALPHABET="0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
SEED=(
"BxEnhvy6NipzkWmROo0GsA3uK3twWLxscLq20UTumy5Cdu461LwD6g7RDNzF8Y"
"iYDFTpB8ehAypd7d6OsOL4APamnJeNXQypUezCmW9n4oXP6XfgmiWuAWZ8ZJ7U"
"OP7gu4kVdlGZqZHULQMar1dXNeJW4i7oNVI8usp8BlovjjZbwPCovZI328fRUq"
"4q92R81s5GjWQaQfGhkq9UYMK3rRMaBmsOIBkJqc2cj2VRIZ6mjzkBIOkW9SjZ"
"FzeA6J5u4j3sBL3SdgwXzM9mHvQivu8EJ1TBTpRhHDqZIbmYgwQ8VqTAFotl6F"
"We1YC554GKrVHsA8oUGKSA6F6k5KREBSD0Tgd7bFALY84LLbpw574BQyvdoHrl"
"0Oe35uwDf15DpT6VJWZBjSbHPpPAINYTte0eUxnTFTKBlGj8Am6sb1gLldh8WZ"
"8P")

def need_decoder(x,msg):
    if not x:raise ValueError(msg)

def decoded_tiles():
    need_decoder(len(SEED)==436,"seed length")
    a=0
    for ch in SEED:a=62*a+ALPHABET.index(ch)
    N=a%(1<<636);T0=(a>>636)%(1<<1675);E0=a>>2311
    sigma=0;tau=0;actions=[]
    for q in range(215):
        m=(N>>(430+q))&1
        Fq=14*(1-m)+m*((E0>>(4*tau))&15)
        tau+=m
        for b in (0,1):
            j=2*q+b;nu=(N>>j)&1
            target=nu*(1+sigma)+(1-nu)*((T0//(216**(j-sigma)))%216)
            v=(Fq>>(2*b))&1;d=(Fq>>(2*b+1))&1
            actions.append((target,v,d));sigma+=nu
    need_decoder(len(actions)==430 and actions[0]==(1,1,1),"actions")
    R=sorted({u for u,v,d in actions if d==1})
    L=sorted({u for u,v,d in actions if d==0})
    rr={q:6+j for j,q in enumerate(R)}
    ll={q:205+j for j,q in enumerate(L)}
    out={}
    def put(i,t):
        need_decoder(i not in out,"duplicate tile "+str(i));out[i]=t
    def h(q,b):return 2*(q+1)+b
    put(0,(2,435,3,1));put(1,(5,0,0,0))
    for j,(u,v,d) in enumerate(actions):
        q,b=divmod(j,2)
        put(j+2,((1-d)*ll.get(u,0),h(q,b),d*rr.get(u,0),v))
    for b in (0,1):
        put(432+b,(0,h(215,b),0,h(215,b)))
        put(434+b,(0,b,0,b))
    for q in R:
        for b in (0,1):put(424+2*rr[q]+b,(rr[q],b,0,h(q,b)))
    for q in L:
        for b in (0,1):put(424+2*ll[q]+b,(0,b,ll[q],h(q,b)))
    for j in range(4):put(924+j,(0,j+430*(j//2),0,438))
    put(928,(2,434,2,0));put(929,(3,436,4,4));put(930,(4,436,4,0))
    for t in (434,435,436):put(497+t,(1,438,1,t))
    for a in (0,1,4):
        for b in (0,1,2):put(934+3*a+b-6*(a//4),(a,437,b,437))
    need_decoder(set(out)==set(range(943)),"incomplete tile table")
    return [out[i] for i in range(943)]


def run(which='4127'):
    cfg=CONFIG[which]
    P=ROOT/cfg['folder']
    rho = 2**47
    m = 2**44
    length = cfg['length']
    flag,left,right,padding=[cfg[k] for k in ['flag','left','right','padding']]
    bitlength = 47*length
    E = set(range(952)) | set(range(973,982)) | set(range(992,1000)) | set(range(1002,1010)) | {990,991,flag}
    c = json.loads((P/'inherited/coefficients.json').read_text())
    decoded=decoded_tiles()
    reconstructed=[0]*3297
    for j,(w,n,e,s) in enumerate(decoded):reconstructed[j]=1+1024*(1+w+256*n+131072*e+33554432*s)
    for j in range(8):reconstructed[1002+j]=1<<(10+j);reconstructed[992+j]=1<<(27+j)
    for j in range(9):reconstructed[973+j]=1<<(18+j);reconstructed[943+j]=1<<(35+j)
    require(reconstructed==c,'All weights independently decoded from complete436-character seed')
    require(len(E) == 980 and c[flag] == 0, 'Physical support including zero coefficient')
    require(all(v == 0 for v in c[1010:]), 'No hidden high weights')
    tiles = json.loads((P/'start_only_tiles.json').read_text())
    if isinstance(tiles, dict):
        tiles = tiles.get('tiles', tiles)
    require(len(tiles) == 943 and [tuple(t) for t in tiles]==decoded, 'Full independently decoded finite language')
    for j, (w,n,p,s) in enumerate(tiles):
        require(c[j] == 1+1024*(1+w+256*n+131072*p+33554432*s), 'Whole tile weight')
    def power(e): return 1 << (47*e)
    def gs(start, count): return sum(power(start+j) for j in range(count))
    B = power(length)
    beta = B-1
    psi1 = gs(1002,8)+gs(992,8)+gs(973,9)+gs(943,9)+power(flag)
    MC = beta+rho-(rho+3)*power(990)-gs(0,943)-psi1
    MF = B+3+(m-2)*(power(left)+power(right))+gs(973,9)+gs(1012,8)+power(flag)+(1<<29)*power(padding+18)-power(padding)
    K = power(20)+power(30)+power(flag)+power(length+10)
    K += sum(v*(power(left-e)+power(right-e)) for e,v in enumerate(c) if v)
    ports = dict(beta=beta, K0=K, MC=MC, MF=MF)
    for name,value in ports.items():
        actual = (P/'start_only_ports'/f'{name}.bin').read_bytes()
        require(int.from_bytes(actual,'big') == value, f'Independent actual bytes {name}')
    require(0<MC<beta<MF<2*beta and MC%4==2 and (MF-beta)%8==4, 'Masks and residues')
    require(MC.bit_count()==bitlength-980 and (MF-beta).bit_count()==980, 'Complementary populations')
    # Exact coefficient-by-coefficient convolution, different from the builder's
    # list-of-hits representation.
    kernel = {20:1, 30:1, flag:1}
    for e,v in enumerate(c):
        if v:
            for a in (left-e,right-e):
                require(a not in kernel,'Separated kernel')
                kernel[a]=v
    require(len(kernel)==1957, 'Kernel support')
    envelope = [0]*length
    for e in E:
        for k,v in kernel.items():
            envelope[k+e] += (3 if e==990 else 1)*v
    peak=max(envelope)
    require(peak+3+3*rho//4+29 < 30*rho, 'Cyclic carry box')
    require(all(x==0 for x in envelope[padding:]), 'Whole zero padding and final reset')
    require(envelope[padding-1]==c[0] and c[0]+29<rho, 'Last nonzero field resets')
    for target in (left,right):
        actual = {e:kernel.get(target-e,0) for e in E}
        require(all(actual[e]==c[e] for e in E),'Exact full clause')
    for target in (left-1,right-1):
        actual = {e:kernel.get(target-e,0) for e in E}
        expected = {e:c[e+1]+(c[0] if target==right-1 and e==flag else 0) for e in E}
        require(actual==expected, 'Whole predecessor, including foreign flag term')
    target = list(range(974,982))+[flag]
    offsets=[]
    for r in range(length):
        pre=[divmod(a-r,length) for a in target]
        if not all(v in E for _,v in pre): continue
        selectors={}
        for cell,v in pre:
            if v<943: selectors[cell]=selectors.get(cell,0)+1
        if max(selectors.values(),default=0)<=1: offsets.append(r)
    require(offsets==([0] if which=='4159' else [0,32]), 'All support-only cyclic offsets')
    semantic=[]
    def bit_value(tile,e):
        w,n,p,s=tile
        if 943<=e<=951: return ((511-s)>>(e-943))&1
        if 973<=e<=981: return ((511-n)>>(e-973))&1
        if 992<=e<=999: return ((255-p)>>(e-992))&1
        if 1002<=e<=1009: return ((255-w)>>(e-1002))&1
        return 1
    for r in offsets:
        cells={}
        for a in target:
            cell,pos=divmod(a-r,length)
            cells.setdefault(cell,[]).append(pos)
        feasible=True
        for positions in cells.values():
            required=[e for e in positions if e<943]
            candidates=required if required else range(943)
            if not any(j!=1 and all(bit_value(tiles[j],e) for e in positions if e>=943) for j in candidates):
                feasible=False
        if feasible:semantic.append(r)
    require(semantic==[0], 'All decoded-tile cyclic offsets')
    require(tiles[942]==[4,437,2,437] or tiles[942]==(4,437,2,437), 'Critical final tile')
    require(prime(47) and prime(length) and prime(cfg['lam']), 'All controller primes')
    records=[]
    for p,order,fac,expected in [(47,23,[23],cfg['units'][0]),(length,cfg['order'],cfg['factors'],cfg['units'][1])]:
        b=B%p
        require(pow(b,order,p)==1 and all(pow(b,order//a,p)!=1 for a in fac),'Exact controller order')
        require(math.gcd(order,bitlength)==1 and b*b%p!=1,'Order and nontrivial square')
        h=(1+b*(K%p)+b*b)%p
        require(h==expected,'Whole controller unit')
        records.append(dict(prime=p,order=order,B=b,K=K%p,H=h))
    lam=cfg['lam']
    require(lam>bitlength and (lam-1)%math.lcm(23,cfg['order'])==0,'Auxiliary prime conditions')
    lift=pow(B,lam-1,lam*lam)
    require(lift%lam==1 and lift!=1,'Exact valuation-one lift')
    H0=(1+(B%lam)*(K%lam)+(B%lam)**2)%lam
    require(H0==cfg['units'][2] and B*B%lam!=1, 'Auxiliary units')
    return {'status':'PASS','scope':'Independent finite coefficient and geometry review; ordinary semantic proof is separate.',
            'raw_bytes':sum((v.bit_length()+7)//8 for v in ports.values()),
            'd':bitlength,'L':length,'kernel_terms':len(kernel),'carry_peak':peak,
            'support_alignment_offsets':offsets,'decoded_alignment_offsets':semantic,'controller':records,
            'lambda':lam,'lambda_lift':lift,'lambda_H0':H0,
            'port_sha256':{k:hashlib.sha256((P/'start_only_ports'/f'{k}.bin').read_bytes()).hexdigest() for k in ports}}

if __name__ == '__main__':
    print(json.dumps(run(sys.argv[1] if len(sys.argv)>1 else '4127'),indent=2,sort_keys=True))
