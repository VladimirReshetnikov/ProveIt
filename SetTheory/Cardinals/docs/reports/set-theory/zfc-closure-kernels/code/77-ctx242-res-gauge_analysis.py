r"""Exact finite-support tape conjugacies, without reachability assumptions.

At a control q, complement the cells h+k for k in F_q.  For every original
edge q --(b,w,d)--> t require F_q\{0}=(d+F_t)\{0}.  Then the conjugated
transition reads b xor [0 in F_q], writes w xor [-d in F_t], and moves d.
This script computes every allowable flip variable by equality propagation.
"""
from pathlib import Path
import json
import argparse

def read(path):
    tab={}
    for line in Path(path).read_text().splitlines():
        if not line or line.startswith('#'): continue
        q,b,w,d,t=line.split()
        tab[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(t))
    return tab

class UF:
    def __init__(self):self.p={}
    def find(self,a):
        if a not in self.p:self.p[a]=a
        if self.p[a]!=a:self.p[a]=self.find(self.p[a])
        return self.p[a]
    def union(self,a,b):
        a,b=self.find(a),self.find(b)
        if a!=b:self.p[a]=b

def compute(tab,radius):
    states=sorted({q for q,b in tab}|{t for w,d,t in tab.values()})
    uf=UF(); z=(-1,0)
    for q in states:
        for k in range(-radius,radius+1):uf.find((q,k))
    for (q,b),(w,d,t) in tab.items():
        for k in range(-radius-1,radius+2):
            if k==0:continue
            a=(q,k) if abs(k)<=radius else z
            j=k-d
            c=(t,j) if abs(j)<=radius else z
            uf.union(a,c)
    groups={}
    zero=uf.find(z)
    for q in states:
        for k in range(-radius,radius+1):
            g=uf.find((q,k))
            if g!=zero:groups.setdefault(g,[]).append((q,k))
    return sorted(groups.values(),key=lambda g:(len(g),g))

def quotient(tab):
    states=sorted({q for q,b in tab})
    group={q:0 for q in states};group[254]=-1
    while True:
        sig={};new={254:-1}
        for q in states:
            key=tuple((tab[q,b][0],tab[q,b][1],group[tab[q,b][2]]) for b in (0,1))
            new[q]=sig.setdefault(key,len(sig))
        if all((new[a]==new[b])==(group[a]==group[b]) for a in states for b in states):break
        group=new
    cls={}
    for q in states:cls.setdefault(new[q],[]).append(q)
    return [c for c in cls.values() if len(c)>1]

def transformed(tab,groups,mask):
    flips=set()
    for i,g in enumerate(groups):
        if (mask>>i)&1:flips.update(g)
    out={}
    for (q,b),(w,d,t) in tab.items():
        out[q,b^((q,0) in flips)]=(w^((t,-d) in flips),d,t)
    return out

def main():
    a=argparse.ArgumentParser();a.add_argument('table');a.add_argument('--radius',type=int,default=6)
    args=a.parse_args();tab=read(args.table);groups=compute(tab,args.radius)
    result={'radius':args.radius,'free_groups':groups,'num_free_groups':len(groups),'plain_quotients':quotient(tab)}
    print(json.dumps(result,indent=2))
    Path(__file__).with_name('gauge-classes.json').write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
