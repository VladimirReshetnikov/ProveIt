from pathlib import Path
import sys,json,time,collections,random,math
BASE=Path('support')
sys.path.insert(0,str(BASE/'work/optimize196'))
from core import *
from grammar import raw_nodes
from layout import opportunities_fast,max_matching,fold
ns=raw_nodes()
def expand(x):
    if isinstance(x,str):return tuple(map(expand,ns[x]))
    return x
INITIAL=expand('node172')
def leaf(t):return len(t)==3 and t[0]=='leaf'
def nodes(t,p=()):
    if leaf(t):return
    yield p,t
    yield from nodes(t[0],p+(0,))
    yield from nodes(t[1],p+(1,))
def replace(t,p,r):
    if not p:return r
    return (replace(t[0],p[1:],r),t[1]) if p[0]==0 else (t[0],replace(t[1],p[1:],r))
def interfaces(rows,t):
    paths=collections.defaultdict(list);byq=collections.defaultdict(set)
    for p,node in nodes(t):
        q=84;h=0
        for _ in range(500):
            if h==len(p):paths[q].append(p);byq[q].add(node);break
            if not 0<=h<len(p):break
            b=p[h];w,d,z=rows[q,b]
            if w!=b:break
            q=z;h+=1 if d else -1
    return paths,byq
def cfg(t,repair=False):
    sites=[];ranges={}
    def visit(t,p):
        l=len(sites)
        if leaf(t):sites.append((p,t))
        else:visit(t[0],p+(0,));visit(t[1],p+(1,))
        ranges[p]=(l,len(sites))
    visit(t,())
    out=[]
    for i,(p,(_,op,arg)) in enumerate(sites):
        zero=[p[:j] for j in range(len(p)-1,-1,-1) if p[j]==0]
        one=[p[:j] for j in range(len(p)-1,-1,-1) if p[j]==1]
        nxt=i+1 if i+1<len(sites) else 0
        if op=='inc':ins=('inc',arg,nxt)
        elif op=='dec':
            if not zero:return None
            ins=('dec',arg,ranges[zero[0]][1]%len(sites),nxt)
        elif op=='breakTo':
            if len(zero)<arg:return None
            ins=('jump',ranges[zero[arg-1]][1]%len(sites))
        elif op=='continueTo':
            if len(one)<arg:return None
            ins=('jump',ranges[one[arg-1]][0])
        elif op=='halt':ins=('halt',)
        else:raise ValueError(op)
        out.append(ins)
    return out
def cands(rows,t):
    paths,byq=interfaces(rows,t);incoming=collections.defaultdict(list)
    for k,v in rows.items():incoming[v[2]].append((k,v))
    pure={q for q,b in rows if all(rows[q,c][:2]==(c,True) for c in (0,1))}
    out=[]
    for q in pure:
        if len(byq[q])!=1 or any(not v[1] for k,v in incoming[q]):continue
        node=next(iter(byq[q]))
        for b in (0,1):
            r=rows[q,b][2]
            if r not in pure or incoming[r]!=[((q,b),(b,True,r))]:continue
            if len(byq[r])!=1 or leaf(node[b]):continue
            out.append((q,r,b,paths[q]))
    return out
def rotate(rows,t,c):
    q,r,b,paths=c;rows=dict(rows)
    for p in paths:
        node=t
        for v in p:node=node[v]
        if b==0:a,c=node[0];e=node[1];new=(a,(c,e))
        else:a=node[0];c,e=node[1];new=((a,c),e)
        t=replace(t,p,new)
    if b==0:
        a,c,e=rows[r,0][2],rows[r,1][2],rows[q,1][2]
        rows.update({(q,0):(0,True,a),(q,1):(1,True,r),(r,0):(0,True,c),(r,1):(1,True,e)})
    else:
        a,c,e=rows[q,0][2],rows[r,0][2],rows[r,1][2],rows[r,1][2]
    return rows,t
def rotate(rows,t,c):
    q,r,b,paths=c;out=dict(rows)
    for p in paths:
        node=t
        for v in p:node=node[v]
        if b==0:a,m=node[0];e=node[1];new=(a,(m,e))
        else:a=node[0];m,e=node[1];new=((a,m),e)
        t=replace(t,p,new)
    if b==0:
        a,m,e=rows[r,0][2],rows[r,1][2],rows[q,1][2]
        out.update({(q,0):(0,True,a),(q,1):(1,True,r),(r,0):(0,True,m),(r,1):(1,True,e)})
    else:
        a,m,e=rows[q,0][2],rows[r,0][2],rows[r,1][2]
        out.update({(q,0):(0,True,r),(q,1):(1,True,e),(r,0):(0,True,a),(r,1):(1,True,m)})
    return out,t
def duplicates(rows):
    groups=collections.defaultdict(list)
    for q,b in rows:
        if b==0:groups[rows[q,0],rows[q,1]].append(q)
    return [qs for qs in groups.values() if len(qs)>1]
def merge(rows,groups):
    mapping={q:g[0] for g in groups for q in g}
    return {(mapping.get(q,q),b):(w,d,mapping.get(n,n)) for (q,b),(w,d,n) in rows.items()}
def contract_list(t):
    sites=[]
    def visit(t,p):
        if leaf(t):sites.append((p,t[1],t[2]));return
        visit(t[0],p+(0,));visit(t[1],p+(1,))
    visit(t,());ins=cfg(t);cs=[]
    for i,code in enumerate(ins):
        st=frame(sites[i][0])
        if code[0]=='inc':
            _,r,n=code;cs.append((i,None,st,canonical(frame(sites[n][0],0,('x','inc',PHYSICAL[r])))))
        elif code[0]=='dec':
            _,r,z,p=code
            cs.append((i,(PHYSICAL[r],True),st,canonical(frame(sites[z][0]))))
            cs.append((i,(PHYSICAL[r],False),st,canonical(frame(sites[p][0],1,('x','dec',PHYSICAL[r])))))
        elif code[0]=='jump':cs.append((i,None,st,canonical(frame(sites[code[1]][0]))))
        else:cs.append((i,None,st,None))
    return sites,cs
if __name__=='__main__':
    rows,_=machine();basecfg=cfg(INITIAL);assert basecfg==program()[1]
    cs=cands(rows,INITIAL);print('candidates',len(cs),[c[:3] for c in cs],flush=True)
    kept=[]
    for j,c in enumerate(cs):
        r,t=rotate(rows,INITIAL,c)
        if cfg(t)!=basecfg:continue
        ds=duplicates(r);print('CFG same',c[:3],'dups',ds,flush=True)
        if ds:r=merge(r,ds)
        paths,byq=interfaces(r,t)
        ops=opportunities_fast(r,byq)
        print('folds',len(ops),max_matching(ops),flush=True)
        if len(r)<len(rows) or ops:
            sites,contracts=contract_list(t)
            ans=validate(r,contracts);print('validate',ans,flush=True)
            if ans['ok']:
                kept.append((c[:3],len(r)//2,len(ops)))
                for a,b,opts in ops:
                    for acts in itertools.product(*opts):
                        rr=fold(r,a,b,acts);check=validate(rr,contracts)
                        if check['ok']:
                            print('SUCCESS',len(rr)//2,c[:3],a,b,acts,flush=True)
                            Path(__file__).with_name('candidate.json').write_text(json.dumps({'rows':[[q,bit,*v] for (q,bit),v in sorted(rr.items())],'sites':sites,'rotation':c[:3],'fold':[a,b,acts],'validation':check},indent=2));raise SystemExit()
        else:kept.append((c[:3],len(r)//2,0))
    print('kept',kept,flush=True)
