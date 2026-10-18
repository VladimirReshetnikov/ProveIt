#!/usr/bin/env python3
"""Compile and audit the single closed-sequence rebracketing discovered here.

This is a candidate generator. A returned failure is not a machine theorem.
The macro induction package is unchanged and must be replayed separately.
"""
from pathlib import Path
from functools import cache
from collections import Counter, deque
import argparse, importlib.util, json, sys, time

HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'sources/context246/zfc-context246'
OLD=HERE.parent/'sources/beyond252/beyond252/negation/data/optimized_original203.json'

def module(path):
    spec=importlib.util.spec_from_file_location(path.stem,path)
    m=importlib.util.module_from_spec(spec);sys.modules[path.stem]=m;spec.loader.exec_module(m);return m

def load():
    d=json.loads(OLD.read_text());n={int(k):tuple(map(tuple,v)) for k,v in d['nodes'].items()}
    t={}
    for l in (BASE/'machine/zfc_prefix246_old.tm').read_text().splitlines():
        if l and not l.startswith('#'):
            q,b,w,m,s=l.split();t[q,int(b)]=int(w),m,s
    return n,d['root'],t

def mutate(n,r):
    n=n.copy()
    assert n[74]==(('N',39),('N',73))
    assert n[73]==(('N',47),('N',63))
    assert n[48]==(('N',39),('N',47))
    n[74]=(('N',48),('N',63))
    del n[73]
    return n,r

def sites(n,r):
    work=[(('N',r),'')]
    while work:
        e,p=work.pop()
        if e[0]=='N':work.extend(((n[e[1]][1],p+'1'),(n[e[1]][0],p+'0')))
        else:yield (p,'C'+e[0],None if len(e)==1 else e[1])

class Tracking(dict):
    def __init__(self,t):super().__init__(t);self.used=set();self.last=deque(maxlen=70)
    def __getitem__(self,k):self.used.add(k);self.last.append(k);return super().__getitem__(k)

def check(t,n,r):
    review=module(BASE/'code/review_affine_source.py')
    affine=module(BASE/'sources/prior/prefix_affine.py')
    t=Tracking(t);count=0;minliteral=10**9
    for p,op,x in sites(n,r):
        v=review.PHYSICAL[x] if op in ('CI','CD') else x
        for zero in ((True,False) if op=='CD' else (None,)):
            branch=(v,zero) if op=='CD' else None
            extra=0;effect=None;overflow=False
            if op=='CI':nxt,overflow=review.full_inc(p);effect=('inc',v)
            elif op=='CD' and not zero:nxt,overflow=review.full_inc(p);effect=('dec',v);extra=1
            elif op=='CD':nxt,overflow=review.full_inc(review.full_strip(p,'0',1))
            elif op=='CB':nxt,overflow=review.full_inc(review.full_strip(p,'0',v))
            elif op=='CC':nxt=review.full_strip(p,'1',v)
            else:nxt=''
            right=[('b',int(c)) for c in nxt]+[('r',0,1,40+extra+int(overflow)-len(nxt)),('b',1),('box',('plain',effect))]
            try:
                rules,literal=affine.run(t,p,branch,affine.canon([('b',1)],right),halt=op=='CH',fuel=1500)
                assert literal>0
            except (KeyError,AssertionError) as ex:
                return dict(status='FAIL',case=count,path=p,op=op,register=v,zero=zero,exception=str(ex),used_pairs=len(t.used),last_rows=list(t.last))
            count+=1;minliteral=min(minliteral,literal)
    return dict(status='PASS',cases=count,minimum_literal_steps=minliteral,used_pairs=len(t.used))

def main():
    n,r,t=load();n,r=mutate(n,r)
    t['178',0]=(0,'R','16');t['178',1]=(1,'R','206')
    t={k:v for k,v in t.items() if k[0]!='208'}
    start=time.monotonic();result=check(t,n,r);result['seconds']=time.monotonic()-start
    print(json.dumps(result,indent=2))
    (HERE/'rebracket_first_result.json').write_text(json.dumps(result,indent=2)+'\n')
    (HERE/'rebracket202_minimal.json').write_text(json.dumps(dict(root=r,nodes=n),indent=2)+'\n')
    (HERE/'rebracket245_first.tm').write_text('#! start 95\n'+''.join(f'{q} {b} {w} {m} {s}\n' for (q,b),(w,m,s) in sorted(t.items(),key=lambda kv:(int(kv[0][0]),kv[0][1]))))

if __name__=='__main__':main()
