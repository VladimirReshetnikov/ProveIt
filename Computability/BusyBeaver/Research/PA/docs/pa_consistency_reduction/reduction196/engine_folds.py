from pathlib import Path
import sys,itertools,collections,json,time,random
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'verification'))
import symbolic as S

def filebits(vs,mark=-1):
    bits=[]
    for i,v in enumerate(vs):bits.extend([0,0 if i==mark else 1]+[1]*v)
    return bits

def inputs():
    tests=[];files=[[0]*10,[1]*10,list(range(10)),[2,0,1,0,3,0,1,2,0,1]]
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

def check(m,test,fold=None,record=False):
    name,(q,h,tape),(target,hh,end)=test;tape=tape.copy();seen=set()
    if fold is not None:
        a,b=fold;q=b if q==a else q;target=b if target==a else target
    for t in range(4000):
        if q==target and h==hh and tape==end:return seen
        seen.add(q);v=int(h in tape)
        if (q,v)not in m:return None
        w,d,q=m[q,v]
        if w:tape.add(h)
        else:tape.discard(h)
        h+=d
    return None

def fold(m,q,p):return{(s,b):(w,d,p if n==q else n)for(s,b),(w,d,n)in m.items()if s!=q}

if __name__=='__main__':
    begin=time.time();m=S.load_machine();ts=inputs();usage={q:[]for q in range(196)}
    for t in ts:
        used=check(m,t)
        assert used is not None,t[0]
        for q in used:usage[q].append(t)
    qs=sorted({q for q,b in S.ENGINE_ROWS})
    successes=[]
    for q in qs:
        if not usage[q]:continue
        for p in range(196):
            if p==q:continue
            n=fold(m,q,p)
            if all(check(n,t,(q,p))is not None for t in usage[q]):
                print('PASS',q,p,'tests',len(usage[q]),flush=True);successes.append((q,p))
        print('DONE',q,flush=True)
    print('SUCCESS',successes,'seconds',time.time()-begin)
    Path(__file__).with_name('engine_fold_candidates.json').write_text(json.dumps(successes))
