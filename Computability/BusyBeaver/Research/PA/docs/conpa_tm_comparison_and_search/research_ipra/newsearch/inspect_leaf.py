from pathlib import Path
import sys,collections,json
BASE=Path('support')
sys.path.insert(0,str(BASE/'work/optimize196'))
from core import *
from grammar import raw_nodes
rows,labels=machine();sites,ins=program();nodes=raw_nodes()
def eff(q,b,prev):
    seen=set()
    while True:
        a=rows[q,b]
        if prev is not None and a[:2]==(b,False):
            h=a[2];a2=rows[h,prev]
            if a2[:2]==(prev,True) and a2[2]!=q and (h,a2[2]) not in seen:
                seen.add((h,a2[2]));q=a2[2];continue
        return a
cat=collections.defaultdict(set);prefixmap=collections.defaultdict(set)
internals={p[:i] for p,_,_ in sites for i in range(len(p))}
selectors={84}
for p in internals:
    q=84;h=0
    for _ in range(500):
        if h==len(p):selectors.add(q);prefixmap[p].add(q);break
        assert 0<=h<len(p),(p,h,q)
        selectors.add(q);b=p[h];w,d,q=rows[q,b]
        assert w==b,(p,h,w)
        h+=1 if d else -1
    else:raise AssertionError(p)
for p,op,arg in sites:
    q=84;h=0
    for _ in range(1000):
        b=p[h];a=rows[q,b]
        if a[2] not in selectors or (a[1] and h==len(p)-1) or a[0]!=b:
            assert h==len(p)-1,(p,h,q,a)
            cat[op,arg,b].add(a);break
        assert a[0]==b,(p,h,q,a)
        q=a[2];h+=1 if a[1] else -1
    else:raise AssertionError(p)
print('selectors',len(selectors),sorted(selectors))
print('engine',len(rows)//2-len(selectors))
for k,v in sorted(cat.items(),key=repr):print(k,v)
Path(__file__).with_name('leaf_actions.json').write_text(json.dumps([[list(k),list(v)] for k,v in cat.items()],indent=2))
