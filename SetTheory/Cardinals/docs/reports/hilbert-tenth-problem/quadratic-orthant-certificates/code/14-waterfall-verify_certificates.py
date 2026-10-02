"""Independent integer replay for history-free Waterfall certificates and ledgers."""
from itertools import product
from pathlib import Path
import json, random, hashlib

ROOT=Path(__file__).resolve().parents[1]

def timestamp_run(a,M,h,limit=10000):
    n=len(a); d=list(a); p=[0]*n; trace=[]
    assert all(type(v) is int and v>0 for v in a)
    assert all(type(v) is int and v>=0 for row in M for v in row)
    assert all(M[i][i]>0 for i in range(n) if i!=h)
    assert all(M[i][h]==0 for i in range(n))
    for _ in range(limit):
        t=min(d); ids=[i for i,v in enumerate(d) if v==t]
        if len(ids)!=1:return dict(status='tie',time=t,counts=p,trace=trace,deadlines=d)
        i=ids[0]
        if i==h:return dict(status='halt',time=t,counts=p,trace=trace,deadlines=d)
        trace.append((i,t));p[i]+=1
        d=[v+M[j][i] for j,v in enumerate(d)]
        assert d==[a[j]+sum(M[j][k]*p[k] for k in range(n)) for j in range(n)]
    return dict(status='cutoff',counts=p,trace=trace,deadlines=d)

def physical_run(a,M,h,limit=10000):
    v=list(a);p=[0]*len(a);trace=[];t=0
    for _ in range(limit):
        wait=min(v);ids=[i for i,x in enumerate(v) if x==wait]
        t+=wait;v=[x-wait for x in v]
        if len(ids)!=1:return dict(status='tie',time=t,counts=p,trace=trace)
        i=ids[0]
        if i==h:return dict(status='halt',time=t,counts=p,trace=trace)
        trace.append((i,t));p[i]+=1;v=[x+M[j][i] for j,x in enumerate(v)]
    return dict(status='cutoff',counts=p,trace=trace)

def family(x,H,k,b):
    n=len(x);N=n+1
    a=[N*x[i]+i+1 for i in range(n)]+[N*(H+1)]
    M=[[b[i]+(N*k[i] if i==j else 0) for i in range(n)]+[0] for j in range(N)]
    return a,M,n

def witnesses(x,H,k):
    out=[]
    for X,K in zip(x,k):
        z=(H+1-X+K-1)//K
        p=max(0,z);s=max(0,-z);r=X+K*(p-s)-H-1;u=K-1-r
        assert min(p,s,r,u)>=0
        out.append((p,s,r,u))
    return out

def general_energy(x,H,k,b,T,w):
    W=H+1;E=T-(len(x)+1)*W-sum(bi*wi[0] for bi,wi in zip(b,w))
    return E*E+sum((X+K*(p-s)-W-r)**2+(r+u-(K-1))**2+p*s
                   for X,K,(p,s,r,u) in zip(x,k,w))

def unit_energy(x,y,H,T,p,q,r,s):
    return (p-r-H-1+x)**2+p*r+(q-s-H-1+y)**2+q*s+(T-3*(H+1)-2*p-3*q)**2

class Circuit:
    def __init__(self,positive=False):self.rows=[];self.positive=positive
    def gate(self,op,a,b,name):self.rows.append([name,op,a,b]);return name
    def eval(self,env):
        env=dict(env)
        for name,op,a,b in self.rows:
            a=env[a] if isinstance(a,str) else a;b=env[b] if isinstance(b,str) else b
            env[name]=a+b if op=='+' else a-b if op=='-' else a*b
        return env[self.rows[-1][0]]
    def counts(self):
        m=sum(row[1]=='*' for row in self.rows);return dict(multiplications=m,additions=len(self.rows)-m,total=len(self.rows))

def make_unit_circuit(positive=False):
    c=Circuit(positive);g=c.gate
    if positive:
        for v in 'pqrs':g('-',v.upper(),1,v)
    W=g('+','H',1,'W')
    U=g('-','p','r','U0');U=g('-',U,W,'U1');U=g('+',U,'x','U')
    V=g('-','q','s','V0');V=g('-',V,W,'V1');V=g('+',V,'y','V')
    terms=[g('*',U,U,'U2'),g('*','p','r','pr'),g('*',V,V,'V2'),g('*','q','s','qs')]
    A=g('*',3,W,'A');B=g('*',2,'p','B');C=g('*',3,'q','C')
    E=g('-','T',A,'E0');E=g('-',E,B,'E1');E=g('-',E,C,'E')
    terms.append(g('*',E,E,'E2'))
    z=terms[0]
    for i,t in enumerate(terms[1:]):z=g('+',z,t,f'F{i}')
    return c

def crt_first(a,d,b,e):
    from math import gcd,lcm
    g=gcd(d,e)
    if (b-a)%g:return None
    mod=e//g
    k=0 if mod==1 else ((b-a)//g*pow(d//g,-1,mod))%mod
    t=a+d*k;L=lcm(d,e)
    if t<b:t+=((b-t+L-1)//L)*L
    return t

def main():
    tests={};runs=0
    for x,y,H,k1,k2 in product(range(6),range(6),range(6),range(1,4),range(1,4)):
        xs=[x,y];ks=[k1,k2];bs=[2,3]
        a,M,h=family(xs,H,ks,bs);r=timestamp_run(a,M,h);v=physical_run(a,M,h)
        w=witnesses(xs,H,ks);counts=[z[0] for z in w]
        T=3*(H+1)+sum(b*p for b,p in zip(bs,counts))
        assert r['status']=='halt' and r['counts']==counts+[0] and r['time']==T
        assert all(r[z]==v[z] for z in ['status','counts','time','trace'])
        assert general_energy(xs,H,ks,bs,T,w)==0
        for dt in [-1,1]:assert general_energy(xs,H,ks,bs,T+dt,w)>0
        runs+=1
    tests['whole_run_family_cases']=runs
    local=0
    for X,H,K in product(range(5),range(5),range(1,5)):
        target=witnesses([X],H,[K])[0];found=[]
        for p,s,r,u in product(range(7),range(7),range(K),range(K)):
            E=(X+K*(p-s)-H-1-r)**2+(r+u-(K-1))**2+p*s
            if E==0:found.append((p,s,r,u))
            local+=1
        assert found==[target],(X,H,K,found,target)
    tests['exhaustive_local_natural_assignments']=local
    natural,positive=make_unit_circuit(),make_unit_circuit(True)
    assert natural.counts()==dict(multiplications=8,additions=14,total=22)
    assert positive.counts()==dict(multiplications=8,additions=18,total=26)
    ledger=0
    rng=random.Random(81791)
    for _ in range(10000):
        vals={k:rng.randrange(20) for k in ['x','y','H','T','p','q','r','s']}
        e=unit_energy(**vals);assert natural.eval(vals)==e
        pos={k:v for k,v in vals.items() if k not in 'pqrs'}
        pos.update({k.upper():vals[k]+1 for k in 'pqrs'})
        assert positive.eval(pos)==e;ledger+=2
    tests['arbitrary_assignment_ledger_replays']=ledger
    a=[1,2,6];M=[[5,3,0],[3,6,0],[2,3,0]];ob=timestamp_run(a,M,2)
    assert ob['trace']==[(0,1),(1,5),(0,9)] and ob['time']==13 and ob['counts']==[2,1,0]
    fake=[2,2,0];d=[a[j]+sum(M[j][i]*fake[i] for i in range(3)) for j in range(3)]
    assert d==[17,20,16]
    assert all(d[i]-M[i][i]<d[2]<d[i] for i in range(2))
    signed=dict(x=0,y=0,H=0,T=6,p=0,q=1,r=-1,s=0)
    assert unit_energy(**signed)==0
    huge=10**100;w=witnesses([0,huge+5],huge,[7,11]);T=3*(huge+1)+2*w[0][0]+3*w[1][0]
    assert general_energy([0,huge+5],huge,[7,11],[2,3],T,w)==0
    crt=0
    for a,b,d,e in product(range(1,10),range(1,10),range(1,8),range(1,8)):
        t=crt_first(a,d,b,e); brute=next((x for x in range(max(a,b),max(a,b)+d*e+1) if (x-a)%d==0 and (x-b)%e==0),None)
        assert t==brute;(crt:=crt+1)
    tests['CRT_first_intersection_checks']=crt
    # A tie before halt is undefined even when neither progression hits the halt value.
    tie=timestamp_run([1,3,20],[[2,0,0],[0,4,0],[0,0,0]],2)
    assert tie['status']=='tie' and tie['time']==3
    # d_1=0 and -1 both lock despite strictly positive physical resets.
    locks=[]
    for d0,b0 in [(0,2),(-1,2)]:
        lock=timestamp_run([1,3,20],[[b0+d0,0,0],[b0,4,0],[b0,0,0]],2,100)
        assert lock['status']=='cutoff' and lock['counts']==[100,0,0]
        locks.append(dict(d=d0,b=b0,first_ten=lock['trace'][:10]))
    receipt=dict(status='PASS',tests=tests,natural_ledger=natural.counts(),positive_witness_ledger=positive.counts(),
                 endpoint_obstruction=dict(actual=ob,spurious_counts=fake,spurious_deadlines=d),
                 signed_domain_counterexample=signed,earlier_tie=tie,nonpositive_diagonal_locks=locks,
                 large_input=dict(H=str(huge),counts=[str(wi[0]) for wi in w],halt_time=str(T)),
                 assurance='Exact finite tests plus separate mathematical proof; not Lean/Rocq verification or a universal polynomial.')
    (ROOT/'replay/certificate-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (ROOT/'replay/unit-ledgers.json').write_text(json.dumps(dict(natural=natural.rows,positive_witnesses=positive.rows),indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k in ['status','tests','natural_ledger','positive_witness_ledger']},indent=2))

if __name__=='__main__':main()
