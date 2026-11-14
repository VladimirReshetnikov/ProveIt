from pathlib import Path
import sys,json,time,random
import search_generic as G
from site_contexts import contexts
from engine_folds import filebits
S=G.S

def fixture_inputs(files):
    tests=[]
    for vs in files:
        for r in range(9):
            l=[1,0,1];base={-(i+1)for i,b in enumerate(l)if b}
            mark=set(base)|{i for i,b in enumerate(filebits(vs,r))if b}
            plain=set(base)|{i for i,b in enumerate(filebits(vs))if b}
            q=list(S.SKIPS)[r];target=S.LITERAL[1 if r==0 else 3]
            tests.append((f'mark{r}',(q,0,plain),(target,-1,mark)))
            vv=vs.copy();vv[r]+=1
            end=set(base)|{i for i,b in enumerate(filebits(vv+[1]))if b}
            tests.append((f'inc{r}',(S.LITERAL[64],0,mark),(S.LITERAL[40],-1,end)))
            if vs[r]==0:tests.append((f'dec0{r}',(S.LITERAL[0],0,mark),(S.LITERAL[97],-1,plain)))
            else:
                vv=vs.copy();vv[r]-=1
                end=set(base)|{0}|{i+1 for i,b in enumerate(filebits(vv))if b}
                tests.append((f'decp{r}',(S.LITERAL[0],0,mark),(S.LITERAL[40],0,end)))
    return tests

def check(m,test,ctx=None,fold=None,limit=5000):
    name,(q,h,tape),(target,hh,end)=test;tape=tape.copy()
    if fold is not None:
        a,b=fold;q=b if q==a else q;target=b if target==a else target
    for t in range(limit):
        if q==target and h==hh and tape==end:return True
        if ctx is not None:
            ctx[q].add(sum((h+i-4 in tape)<<i for i in range(9)))
        v=int(h in tape)
        if (q,v)not in m:return False
        w,d,q=m[q,v]
        if w:tape.add(h)
        else:tape.discard(h)
        h+=d
    return False

if __name__=='__main__':
    begin=time.time();m=S.load_machine();ctx=contexts(4,True,m)
    rng=random.Random(1762)
    files=[[x]*10 for x in range(10)]+[[rng.randrange(10)for j in range(10)]for _ in range(100)]
    tests=fixture_inputs(files)
    for test in tests:assert check(m,test,ctx),test[0]
    q=0;h=0;tape=set()
    for step in range(58154):
        ctx[q].add(sum((h+i-4 in tape)<<i for i in range(9)))
        w,d,q=m[q,int(h in tape)]
        if w:tape.add(h)
        else:tape.discard(h)
        h+=d
    assert q==75
    tests.append(('startup',(0,0,set()),(q,h,tape)))
    print('context',sum(map(len,ctx.values())),len(tests),'startup',(q,h,len(tape)),flush=True)
    src=Path(G.__file__).read_text().split("if __name__=='__main__':")[0]
    src=src.replace('protected={q for q,b in S.ENGINE_ROWS}|{0,S.ROOT}','protected={0,S.ROOT}')
    ns={'__file__':G.__file__};exec(src,ns)
    result=ns['candidates'](m,ctx)
    print('CANDIDATES',len(result),result,flush=True)
    survivors=[]
    for q,p,a0,a1 in result:
        n=m.copy();n[q,0]=a0;n[q,1]=a1;del n[p,0];del n[p,1]
        n={k:(w,d,q if z==p else z)for k,(w,d,z)in n.items()}
        good=all(check(n,test,None,(p,q),1000000 if test[0]=='startup'else 20000)for test in tests)
        if not good:continue
        print('FINITE_PASS',q,p,a0,a1,flush=True);survivors.append((q,p,a0,a1))
    Path(__file__).with_name('engine_detour_candidates.json').write_text(json.dumps(survivors))
    print('DONE',len(survivors),time.time()-begin,flush=True)
