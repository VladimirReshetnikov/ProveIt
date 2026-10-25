"""Independent, bounded modular controller probe for the pinned radix49/51 adapters."""
from pathlib import Path
import json, math, hashlib

ROOT=Path(__file__).resolve().parent
L=8807
MARKERS=[992,1011,1022,1031,1095,2195,3296]

def require(p, message):
    if not p: raise ValueError(message)

def decode_tiles():
    alphabet='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
    seed=(ROOT/'sources/research/indexed-tile-enumeration/SEED.txt').read_text().strip()
    require(len(seed)==436,'seed length')
    A=0
    for char in seed: A=62*A+alphabet.index(char)
    N=A%(1<<636); T=(A>>636)%(1<<1675); E=A>>2311
    actions=[];sigma=tau=0
    for q in range(215):
        mq=(N>>(430+q))&1
        F=14+mq*((E>>(4*tau))%16-14)
        tau+=mq
        for b in range(2):
            j=2*q+b;nu=(N>>j)&1
            u=nu*(1+sigma)+(1-nu)*(T//(216**(j-sigma))%216)
            sigma+=nu
            v=(F>>(2*b))&1;d=(F>>(2*b+1))&1
            actions.append((u,v,d))
    S=[sorted({u for u,v,d in actions if d==dd}) for dd in range(2)]
    def r(d,q): return 205-199*d+sum(x<q for x in S[d])
    def h(q,b): return 2*q+b+2
    tiles=[None]*943
    def put(i,t):
        require(tiles[i] is None,'duplicate tile index')
        tiles[i]=list(t)
    put(0,(2,435,3,1));put(1,(5,0,0,0))
    for j,(u,v,d) in enumerate(actions): put(j+2,((1-d)*r(0,u),j+2,d*r(1,u),v))
    for a in range(2):
        for b in range(2): put(434-2*a+b,(0,432*a+b,0,432*a+b))
    for d in range(2):
        for q in S[d]:
            for b in range(2): put(424+2*r(d,q)+b,(d*r(d,q),b,(1-d)*r(d,q),h(q,b)))
    for a in range(2):
        for b in range(2): put(924+2*a+b,(0,432*a+b,0,438))
    put(928,(2,434,2,0));put(929,(3,436,4,4));put(930,(4,436,4,0))
    for t in [434,435,436]: put(497+t,(1,438,1,t))
    for a in range(3):
        for b in range(3): put(934+3*a+b,(a*a,437,b,437))
    require(all(x is not None for x in tiles),'missing tile')
    expected=json.loads((ROOT/'sources/research/indexed-tile-enumeration/TILES.json').read_text())
    require(tiles==expected,'decoder vs complete published table')
    return tiles

def coefficients(tiles,shared):
    c=[0]*3297
    for i,(w,n,p,s) in enumerate(tiles): c[i]=1+(1<<44)-(w<<10)-(n<<18)-(p<<27)-(s<<35)
    for j in range(8): c[1023+j]=1<<(10+j);c[1003+j]=1<<(27+j)
    for j in range(9): c[1013+j]=1<<(18+j);c[983+j]=1<<(35+j)
    for e,k in zip(MARKERS,[47,46,45,44,48,49,50]): c[e]=1<<(44 if shared else k)
    require(sum(x!=0 for x in c)==984,'support size')
    return c

def residues(b,c,mod):
    rho=pow(2,b,mod);B=pow(2,b*L,mod)
    K=sum(pow(rho,e,mod) for e in [30,62,1100,2201,8849])
    for e,ce in enumerate(c):
        K+=ce*(pow(rho,4393-e,mod)+pow(rho,5495-e,mod))
    K%=mod
    # Independent reversal-Horner of the same complete coefficient array.
    phi=0
    for ce in c: phi=(rho*phi+ce)%mod
    Kh=(sum(pow(rho,e,mod) for e in [30,62,1100,2201,8849])
        +(pow(rho,1097,mod)+pow(rho,2199,mod))*phi)%mod
    require(K==Kh,'modular K routes')
    return {'modulus':mod,'rho':rho,'B':B,'K':K,'Hctrl':(1+B*K+B*B)%mod}

def factors(n):
    ans=[];p=2
    while p*p<=n:
        if n%p==0:
            a=0
            while n%p==0:n//=p;a+=1
            ans.append([p,a])
        p+=1
    if n>1:ans.append([n,1])
    return ans

def prime(n): return n>=2 and all(n%k for k in range(2,math.isqrt(n)+1))

def order(a,p):
    n=p-1
    for q,e in factors(n):
        while n%q==0 and pow(a,n//q,p)==1:n//=q
    return n

def probe(b,shared,spacing,lo,hi):
    c=coefficients(decode_tiles(),shared)
    fixed=[residues(b,c,p) for p in ([7,49,8807] if b==49 else [17,8807])]
    report={'radix_bits':b,'d':b*L,'shared_markers':shared,'spacing':spacing,'range':[lo,hi],
        'coefficient_sha256':hashlib.sha256(json.dumps(c,separators=(',',':')).encode()).hexdigest(),'fixed':fixed,'search':[]}
    if any(x['Hctrl']==0 for x in fixed):
        report['outcome']='fixed-unit-obstruction';return report
    for m in range(lo,hi+1):
        p=spacing*m+1
        r={'index':m,'candidate':p}
        if not prime(p): r['result']='composite'
        else:
            r.update(residues(b,c,p));r['order']=order(r['B'],p);r['order_factors']=factors(r['order'])
            r['lambda_minus_one_factors']=factors(p-1)
            r['lift_residue']=pow(2,b*L*(p-1),p*p)
            r['lift_quotient']=(r['lift_residue']-1)//p
            if pow(r['B'],2,p)==1:r['result']='square-unit-obstruction'
            elif r['lift_residue']==1:r['result']='lift-obstruction'
            elif r['Hctrl']==0:r['result']='bracket-obstruction'
            else:r['result']='found'
        report['search'].append(r)
        if r['result']=='found': report['outcome']='found';report['selected']=r;return report
    report['outcome']='bounded-exhaustion';return report

if __name__=='__main__':
    reports=[probe(49,True,1887,230,430),probe(51,False,2072,217,417)]
    (ROOT/'radix_probe_result.json').write_text(json.dumps(reports,indent=2)+'\n')
    print(json.dumps(reports,indent=2))
