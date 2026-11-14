from pathlib import Path
import sys,json,itertools,time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'verification'))
import symbolic as S
import compile_grammar as C
sys.path.insert(0,str(ROOT/'math_reduction/folding'))
import compatible_folds as F

def setup():
    t,defs=S.source_tree()
    htot=(('leaf',('dec',5)),defs['node38'])
    modified=(defs['node37'],(htot,defs['node19']))
    tree=C.replace(t,defs['node168'],modified)
    m=S.load_machine();m[2000,0]=m[30,0];m[2000,1]=(1,1,54)
    m[2001,0]=(0,1,2000);m[2001,1]=(1,1,31);m[37,1]=(1,1,2001)
    return m,tree

if __name__=='__main__':
    m,t=setup();ss=S.flatten(t);S.all_sites=lambda:ss
    failures=[]
    for i,b,br,s,z in S.contracts():
        if S.execute(m,br,s,z)is None:failures.append((i,b))
    print('failures',failures,flush=True)
    protect={q for q,b in S.ENGINE_ROWS}|{m[k][2]for k in S.ENGINE_ROWS}|{0,S.ROOT}
    opt=F.candidates(m,{q for q,b in m if q not in protect});sel,tested=F.best_subset(m,opt)
    print('folds',sel,'count',len(m)//2-len(sel),'tested',tested)
    Path(__file__).with_name('t_only_seed.tm').write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {t}\n'for(q,b),(w,d,t)in sorted(m.items())))
    Path(__file__).with_name('t_only_sites.json').write_text(json.dumps(ss))
