#!/usr/bin/env python3
"""Fold equality witness into the pointed gate's inner falsity occurrence.

X=forall b not E(a,b); replace U_c(S -> (P -> 1)) by
U_c(S -> (P -> X)), and omit the separate head5=N X stack push.
"""
from pathlib import Path
import sys,json,itertools,random,math,time,functools,hashlib
import optimize_closed as O
sys.path[:0]=[str(O.W/'reduction196'),str(O.W/'math_reduction/grammar')]
from optimize_antecedents import expression,code
from permute_heads import PREFIX,HEADS,SUFFIX,ORIG
import search_grammar as SG
from rotate_search import tree as opaque_tree
TOKEN_RAW={v:O.RAW[k]for k,v in SG.TOKENS.items()}

def unwrap(t):
    tag,v,one=t;assert tag==0 and one==1;return v
oldgate=expression(SUFFIX[:-3]);x=unwrap(expression(HEADS[4]))
chain=unwrap(oldgate);_,eq,rest=chain;_,mem,q=rest
qtag,inner,c=q;itag,sep,np=inner;nptag,point,one=np
assert(qtag,itag,nptag,one)==(2,0,0,1)
newq=(qtag,(itag,sep,(nptag,point,x)),c)
newgate=(0,(0,eq,(0,mem,newq)),1)
GATE_WORD=code(newgate)
assert code(oldgate)==SUFFIX[:-3]
WORD=PREFIX+sum((h for i,h in enumerate(HEADS)if i!=4),[])+GATE_WORD+SUFFIX[-3:]
assert len(WORD)==196,(len(WORD),len(GATE_WORD))
assert WORD==ORIG[:86]+ORIG[102:185]+HEADS[4][:-3]+ORIG[187:]

@functools.lru_cache(maxsize=2048)
def length(t):return 1 if isinstance(t,str) else length(t[0])+length(t[1])
def join(a,b):return b if a is None else a if b is None else(a,b)
def sub(t,lo,hi):
    if lo==0 and hi==length(t):return t
    if lo==hi:return None
    a,b=t;n=length(a)
    if hi<=n:return sub(a,lo,hi)
    if lo>=n:return sub(b,lo-n,hi-n)
    return join(sub(a,lo,n),sub(b,0,hi-n))
def patch(t,lo,hi,repl):
    if lo==0 and hi==length(t):return repl
    a,b=t;n=length(a)
    if hi<=n:return join(patch(a,lo,hi,repl),b)
    if lo>=n:return join(a,patch(b,lo-n,hi-n,repl))
    return join(patch(a,lo,n,repl),patch(b,0,hi-n,None))
def opened(t):
    if isinstance(t,str):return O.openax(TOKEN_RAW[t])if t in TOKEN_RAW else t
    return tuple(map(opened,t))
opaque=opaque_tree('x67');x_tree=sub(opaque,86,99)
assert O.expand(x_tree)==HEADS[4][:-3]
initial=patch(patch(opaque,185,187,x_tree),86,102,None)
assert O.expand(initial)==WORD
START=opened(initial)
OLD_MAX=O.zero_shape
# Keep a bounded cache and hash-only search history.
O.zero_shape=functools.lru_cache(maxsize=8192)(OLD_MAX.__wrapped__)
O.evaluate=functools.lru_cache(maxsize=512)(O.evaluate.__wrapped__)

def decode(rules,root):
    return tuple(decode(rules,z)for z in rules[root])if root in rules else root

def output(t,path):
    O.output(t,path)
    d=json.loads(path.read_text());d.update(design='integrated equality witness gate',dropped_stack_heads=[5],generated_stack_heads=7,opaque_word=WORD,new_gate_expression=newgate)
    path.write_text(json.dumps(d,indent=2))
def check(t,path):
    m,new,entry=O.make(t);score,n,c,sel=O.evaluate(t);mm,mu=O.F.fold(m,sel)
    tr=O.C.replace(O.ROOT,O.RAW['x67'],O.raw(t));sites=O.S.flatten(tr)
    original=O.S.all_sites;O.S.all_sites=lambda:sites;failures=[];lens=[]
    try:
        assert O.S.check_engine(mm)
        for i,b,br,s,tar in O.S.contracts():
            v=O.S.execute(mm,br,s,tar)
            if v is None:failures.append((i,b))
            else:lens.append(v[0])
    finally:O.S.all_sites=original
    result=dict(states=len(mm)//2,sites=len(sites),max_path=max(len(p)for p,op in sites),passed=len(lens),failures=failures,max_symbolic=max(lens,default=0))
    path.with_suffix('.tm').write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(mm.items())))
    path.with_suffix('.check.json').write_text(json.dumps(result,indent=2));path.with_suffix('.sites.json').write_text(json.dumps(sites))
    return result

def main():
    budget=int(sys.argv[1])if len(sys.argv)>1 else 200000
    seed=int(sys.argv[2])if len(sys.argv)>2 else 815731
    rng=random.Random(seed);start=time.monotonic();bestt=START;best=O.evaluate(START)[0];ties=[START]
    print('START',O.evaluate(START),'shape',O.zero_shape(START),'rawnodes',len(O.nodes(initial)),flush=True)
    output(START,Path(__file__).with_name('integrated_start.json'))
    print('START CHECK',check(START,Path(__file__).with_name('integrated_start.json')),flush=True)
    # A small independent grammar seed pool.
    SG.WORD=WORD
    for rs in range(150):
        rules,root=SG.repaire(rs,0 if rs%3 else 1.2);t=opened(decode(rules,root));s=O.evaluate(t)[0]
        if s<best:best=s;bestt=t;ties=[t];print('REPAIR BEST',s,rs,len(rules),flush=True)
        elif s==best and len(ties)<30:ties.append(t)
    t=bestt;score=best;seen={hash(t)};nties=len(ties)
    for it in range(budget):
        if it%3000==0:t=rng.choice([START,bestt]+ties);score=O.evaluate(t)[0]
        cand=t
        for _ in range(2 if rng.random()<.15 else 1):
            p,q=rng.choice(O.paths(cand));a,b=q
            if rng.randrange(2):
                if not isinstance(a,tuple):continue
                u,v=a;alt=u,(v,b)
            else:
                if not isinstance(b,tuple):continue
                u,v=b;alt=(a,u),v
            cand=O.replace(cand,q,alt)if rng.random()<.72 else O.replace_one(cand,p,alt)
        if it%10000==0:print('progress',it,'best',best,'current',score,'seconds',round(time.monotonic()-start,1),flush=True)
        h=hash(cand)
        if h in seen:continue
        seen.add(h)
        s,n,c,ds=O.evaluate(cand);temp=.55*(1-(it%3000)/3000)+.05
        if s<1000 and(s<=score or rng.random()<math.exp((score-s)/temp)):t=cand;score=s
        if s<=best:
            if s<best:best=s;bestt=cand;ties=[];nties=0;print('BEST',s,n,c,it,flush=True)
            nties+=1
            if len(ties)<100:ties.append(cand)
            elif rng.randrange(nties)<100:ties[rng.randrange(100)]=cand
            if s<196:
                path=Path(__file__).with_name(f'integrated_{s}_{seed}_{it}.json');output(cand,path);result=check(cand,path);print('TARGET CHECK',result,flush=True)
                if not result['failures']:break
    output(bestt,Path(__file__).with_name(f'integrated_best_{seed}.json'))
    print('DONE',best,len(seen),'seconds',round(time.monotonic()-start,1),flush=True)
if __name__=='__main__':main()
