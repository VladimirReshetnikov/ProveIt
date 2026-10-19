"""Heuristic semantic signatures of closed program fragments, not a proof."""
from pathlib import Path
import json,random,sys,time
from functools import lru_cache
HERE=Path(__file__).resolve().parent
D=json.loads((HERE.parent/'source_encoding/mapping.json').read_text())
S=D['structures']
@lru_cache(None)
def leaves(n):
    x=S[n]
    if isinstance(x[0],str):return (('',x[0],x[1]),)
    return tuple((str(b)+p,o,r) for b in (0,1) for p,o,r in leaves(x[b]))
def closed(n):
    for p,o,r in leaves(n):
        if o=='CH':return False
        if o=='CD' and '0' not in p:return False
        if o=='CB' and p.count('0')<r:return False
        if o=='CC' and p.count('1')<r:return False
    return True
def advance(pc):
    j=pc.rfind('0')
    return None if j<0 else pc[:j]+'1'+'0'*(len(pc)-j-1)
def strip(pc,b,r):
    for j in range(len(pc)-1,-1,-1):
        if pc[j]==b:
            r-=1
            if r==0:return pc[:j]
    raise ValueError(('escape',pc,b,r))
@lru_cache(None)
def run(n,regs,bound=10000):
    regs=list(regs);pc=''
    for t in range(bound):
        pc=pc.rstrip('0')
        q=n;path='';i=0
        while isinstance(S[q][0],int):
            b=int(pc[i]) if i<len(pc) else 0
            path+=str(b);q=S[q][b];i+=1
        assert i>=len(pc)
        op,r=S[q]
        if op=='CI':regs[r]+=1;pc=advance(path)
        elif op=='CD' and regs[r]:regs[r]-=1;pc=advance(path)
        elif op in ('CD','CB'):pc=advance(strip(path,'0',1 if op=='CD' else r))
        elif op=='CC':pc=strip(path,'1',r)
        else:return None
        if pc is None:return tuple(regs),t+1
    return None
def main():
    rng=random.Random(1234567)
    fixtures=[(0,)*9]+[tuple(int(i==j)*v for i in range(9)) for j in range(9) for v in (1,2,4)]+[tuple(rng.randrange(4) for i in range(9)) for _ in range(16)]
    sigs={};invalid=[];start=time.monotonic()
    for n in range(len(S)):
        if not closed(n):continue
        vals=[]
        for inp in fixtures:
            ans=run(n,inp)
            if ans is None:break
            vals.append(ans[0])
        if len(vals)!=len(fixtures):invalid.append(n);continue
        sigs.setdefault(tuple(vals),[]).append(n)
    matches=[]
    for sig,ns in sigs.items():
        if len(ns)>1:
            matches.append({'nodes':ns,'leaf_counts':[len(leaves(n)) for n in ns],
                'controls':{str(n):[q for q,nn in D['qnodes'].items() if nn==[n]] for n in ns}})
    out={'status':'HEURISTIC_ONLY','fixtures':fixtures,'signature_groups':len(sigs),'matches':matches,'cutoffs':invalid,'seconds':time.monotonic()-start}
    (HERE/'signatures.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='fixtures'},indent=2))
if __name__=='__main__':main()
