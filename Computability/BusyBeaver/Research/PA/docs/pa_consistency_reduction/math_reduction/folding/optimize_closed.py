#!/usr/bin/env python3
"""Physical-cost annealing after exposing all sequential closed source chunks."""
from pathlib import Path
import sys,json,collections,functools,random,math,time,re
W=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(W/'verification'))
sys.path.insert(0,str(W/'math_reduction/grammar'))
import symbolic as S
import compile_grammar as C
import compatible_folds as F
from macro_splits import closed
from rotate_search import nodes,paths,replace,replace_one,expand
ROOT,RAW=S.source_tree()
NM=json.loads((W/'verification/node_map.json').read_text())
ORIGINAL=S.load_machine()
BASE={k:v for k,v in ORIGINAL.items() if k[0]<134}
CONTEXT=collections.defaultdict(set)
def context_walk(t,p=()):
    if t[0]=='leaf':return
    CONTEXT[t].add(p[-1] if p else 1)
    context_walk(t[0],p+(0,));context_walk(t[1],p+(1,))
context_walk(ROOT)
NAME={t:n for n,t in RAW.items() if n.startswith('node') and int(n[4:])<=150}
ATOMS={};ATOM_RAW={}
@functools.lru_cache(None)
def opening(t):
    if t[0]=='leaf':
        if t[1]==('inc',1):return 'i'
        if t[1]==('breakTo',1):return 'B'
        raise ValueError(('unhandled isolated leaf',t))
    if all(closed(x) for x in t):return tuple(map(opening,t))
    # This is an indivisible closed command chunk, or the closing guarded block.
    n=NAME[t];ATOMS[n]=NM[n][0];ATOM_RAW[n]=t
    return n
# x67 contains a final break leaf; open all its sequential nodes regardless of
# that enclosing break, and stop only at irreducible fixed macro chunks.
def openax(t):
    if t in NAME and closed(t):return opening(t)
    if t[0]=='leaf':return opening(t)
    return tuple(map(openax,t))
START=openax(RAW['x67'])
ATOMS['i']=58;ATOM_RAW['i']=('leaf',('inc',1))
FREE={};TAGS={}
for name,t in RAW.items():
    if not name.startswith('node') or int(name[4:])>150 or not closed(t):continue
    if len(NM[name])!=1:continue
    try:expr=opening(t)
    except ValueError:continue
    q=NM[name][0]
    FREE[expr]=q
    pure=ORIGINAL[q,0][:2]==(0,1) and ORIGINAL[q,1][:2]==(1,1)
    TAGS[expr]={0,1} if pure else CONTEXT[t]
LEAD={};MAXRUN={}
for a,t in ATOM_RAW.items():
    pp=[''.join(map(str,p)) for p,op in S.flatten(t)]
    LEAD[a]=max([0]+[len(x)-len(x.lstrip('0')) for x in pp])
    MAXRUN[a]=max([0]+[len(z) for x in pp for z in re.findall('0+',x)])
LEAD['B']=MAXRUN['B']=0
@functools.lru_cache(maxsize=100000)
def zero_shape(t):
    if isinstance(t,str):return LEAD[t],MAXRUN[t]
    la,ma=zero_shape(t[0]);lb,mb=zero_shape(t[1])
    return 1+la,max(1+la,ma,mb)
def prune(m):
    reached={0};todo=[0]
    while todo:
        q=todo.pop()
        for b in (0,1):
            if (q,b) not in m:continue
            z=m[q,b][2]
            if z not in reached:reached.add(z);todo.append(z)
    return {k:v for k,v in m.items() if k[0] in reached}
def make(t,pruned=True):
    m=BASE.copy();new={}
    def emit(x,bit):
        if x in FREE and bit in TAGS[x]:return FREE[x]
        if isinstance(x,str):
            if x in TAGS and bit not in TAGS[x]:raise ValueError(('wrong atom context',x,bit))
            return ATOMS[x]
        if x in new:return new[x]
        def row(y,b):
            return (0,-1,131 if b else 5) if y=='B' else (b,1,emit(y,b))
        a,b=x;r0=row(a,0);r1=row(b,1)
        q=1000+len(new);new[x]=q;m[q,0]=r0;m[q,1]=r1
        return q
    entry=emit(t,1);m[89,1]=(1,1,entry)
    return (prune(m) if pruned else m),new,entry
@functools.lru_cache(maxsize=10000)
def evaluate(t):
    if zero_shape(t)[1]>6:return 1000,0,0,()
    try:m,new,entry=make(t)
    except ValueError:return 1000,0,0,()
    protected={q for q,b in S.ENGINE_ROWS}|{m[k][2] for k in S.ENGINE_ROWS if k in m}|{0,S.ROOT}
    opts=F.candidates(m,{q for q,b in m if q not in protected})
    selected,tested=F.best_subset(m,opts)
    return len(m)//2-len(selected),len(m)//2,len(selected),tuple(selected)
def raw(t):
    if isinstance(t,str):return ('leaf',('breakTo',1)) if t=='B' else ATOM_RAW[t]
    return tuple(map(raw,t))
def output(t,path):
    rules={};rev={}
    def go(q):
        if isinstance(q,str):return q
        if q in rev:return rev[q]
        a,b=map(go,q);n=f'r{len(rules)}';rev[q]=n;rules[n]=(a,b)
        return n
    r=go(t)
    data={'nodes':len(rules),'root':r,'rules':rules,'tokens':{n:n for n in ATOMS if n!='i'},'word':expand(t),'evaluation':evaluate(t)}
    path.write_text(json.dumps(data,indent=2))
def validate(t,path):
    m,new,entry=make(t);score,n,c,sel=evaluate(t);mm,mu=F.fold(m,sel)
    newtree=C.replace(ROOT,RAW['x67'],raw(t))
    result=C.check(mm,newtree,True)
    path.with_suffix('.tm').write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for (q,b),(w,d,z) in sorted(mm.items())))
    path.with_suffix('.check.json').write_text(json.dumps(result,indent=2))
    return result

def main():
    budget=int(sys.argv[1]) if len(sys.argv)>1 else 200000
    seed=int(sys.argv[2]) if len(sys.argv)>2 else 281126
    rng=random.Random(seed);start=time.monotonic();base=START
    t=base;bestt=base;score=best=evaluate(base)[0];ties=[base];ties_seen=0;seen={base}
    print('BASE',evaluate(base),'nodes',len(nodes(base)),'tokens',len(expand(base)),'atoms',len(ATOMS),flush=True)
    output(base,Path(__file__).with_name('closed_base.json'))
    for it in range(budget):
        if it%3000==0:
            t=rng.choice([base,bestt]+ties);score=evaluate(t)[0]
        cand=t
        for _ in range(2 if rng.random()<.16 else 1):
            ps=paths(cand);p,q=rng.choice(ps);a,b=q
            if rng.randrange(2):
                if not isinstance(a,tuple):continue
                u,v=a;alt=(u,(v,b))
            else:
                if not isinstance(b,tuple):continue
                u,v=b;alt=((a,u),v)
            cand=replace(cand,q,alt) if rng.random()<.72 else replace_one(cand,p,alt)
        if cand in seen:continue
        seen.add(cand)
        if zero_shape(cand)[1]>6:continue
        s,n,c,ds=evaluate(cand)
        temp=.5*(1-(it%3000)/3000)+.05
        if s<1000 and (s<=score or rng.random()<math.exp((score-s)/temp)):t=cand;score=s
        if s<=best:
            if s<best:
                best=s;bestt=cand;ties=[];ties_seen=0
                print('BEST',best,n,c,'iteration',it,'seconds',round(time.monotonic()-start,1),flush=True)
            ties_seen+=1
            if len(ties)<150:ties.append(cand)
            elif rng.randrange(ties_seen)<150:ties[rng.randrange(150)]=cand
            if s<196:
                p=Path(__file__).with_name(f'closed_{s}_{seed}_{it}.json');output(cand,p)
                print('TARGET',p.name,ds,flush=True)
                result=validate(cand,p);print('VALIDATE',result,flush=True)
                if not result['failures']:break
        if it%10000==0:print('progress',it,'best',best,'current',score,'seconds',round(time.monotonic()-start,1),flush=True)
    output(bestt,Path(__file__).with_name(f'closed_best_{seed}.json'))
    print('DONE','best',best,'visited',len(seen),'seconds',round(time.monotonic()-start,1),flush=True)
if __name__=='__main__':main()
