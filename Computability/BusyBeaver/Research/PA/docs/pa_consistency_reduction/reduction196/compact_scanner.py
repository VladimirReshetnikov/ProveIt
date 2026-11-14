from pathlib import Path
import sys,json,itertools,time,collections
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'verification'))
import symbolic as S
import compile_grammar as C

def setup():
    p=Path(__file__).resolve().parents[1]/'verification/warm_physical_61_8047.json'
    m,t,_,_=C.compile_grammar(json.loads(p.read_text()))
    m[34,0]=(0,-1,2000)
    m[2000,0]=(0,-1,2001);m[2000,1]=(1,-1,3)
    m[2001,0]=(0,1,69);m[2001,1]=(1,-1,3)
    S.all_sites=lambda:S.flatten(t)
    return m,t

def fold(m,q,p):return{(s,b):(w,d,p if n==q else n)for(s,b),(w,d,n)in m.items()if s!=q}

if __name__=='__main__':
    begin=time.time();m,tree=setup();cs=S.contracts();snapshots={};start=[]
    for i,b,br,s,t in cs:
        tr=[];v=S.execute(m,br,s,t,record=tr)
        assert v is not None,(i,b)
        for q in(2000,2001,69):
            here=next((z for k,z,row in tr if z[0]==q),None)
            if here:snapshots.setdefault(q,[]).append((i,b,br,here,t))
    print('baseline ok',len(m)//2,flush=True)
    qs=sorted({q for q,b in m})
    for q in(2000,2001):
        for p in qs:
            if p==q:continue
            n=fold(m,q,p)
            if all(S.execute(n,br,(p,s[1],s[2],s[3]),t)for i,b,br,s,t in snapshots[q]):
                print('DIRECT SUCCESS',q,p,flush=True)
    # Share the final detector with the existing zero-right scan, changing only its one-row.
    q,p=2001,69;n=fold(m,q,p)
    allsnaps={}
    for i,b,br,s,t in cs:
        tr=[];S.execute(m,br,s,t,record=tr)
        here=next((z for k,z,row in tr if z[0]in(q,p)),None)
        if here:allsnaps[i,b]=(i,b,br,here,t)
    for w,d,r in itertools.product((0,1),(-1,1),qs):
        nn=n.copy();nn[69,1]=(w,d,r)
        ok=True
        for i,b,br,s,t in allsnaps.values():
            s=(69 if s[0]==2001 else s[0],s[1],s[2],s[3])
            if S.execute(nn,br,s,t)is None:ok=False;break
        if ok:
            print('MERGE SUCCESS',q,p,nn[69,1],flush=True)
            Path(__file__).with_name('scanner_success.tm').write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {t}\n'for(q,b),(w,d,t)in sorted(nn.items())))
    print('seconds',time.time()-begin)
