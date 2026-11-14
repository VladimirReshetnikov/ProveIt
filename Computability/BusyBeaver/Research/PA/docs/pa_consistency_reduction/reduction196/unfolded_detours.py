from pathlib import Path
import sys,json,time
from search_generic import S,candidates
from site_contexts import contexts
root=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(root/'math_reduction/folding'))
import compatible_folds as F
import compile_grammar as C
begin=time.time()
m,tree,new,entry=C.compile_grammar()
sites=S.flatten(tree);S.all_sites=lambda:sites
ctx=contexts(4,True,m)
print('contexts',len(m)//2,len(sites),sum(map(len,ctx.values())),flush=True)
result=candidates(m,ctx)
print('candidates',len(result),result[:40],flush=True)
Path(__file__).with_name('unfolded_detours_candidates.json').write_text(json.dumps(result))
protected={q for q,b in S.ENGINE_ROWS}|{0,S.ROOT}
best=196
for idx,(q,p,a0,a1) in enumerate(result):
    n=m.copy();n[q,0]=a0;n[q,1]=a1;del n[p,0];del n[p,1]
    n={k:(w,d,q if s==p else s)for k,(w,d,s)in n.items()}
    opts=F.candidates(n,{r for r,b in n if r not in protected})
    selected,_=F.best_subset(n,opts)
    folded,_=F.fold(n,selected)
    score=len(folded)//2
    if score>=best:continue
    print('SCORE',idx,score,(q,p,a0,a1),'folds',selected,flush=True)
    try:checks,_=S.verify(folded)
    except Exception as e:print('failed',q,p,e,flush=True);continue
    print('SUCCESS',q,p,a0,a1,checks,flush=True);best=score
    Path(__file__).with_name(f'unfolded_detour_success_{score}.json').write_text(json.dumps(dict(detour=(q,p,a0,a1),folds=selected,tree=tree,checks=checks)))
    Path(__file__).with_name(f'unfolded_detour_success_{score}.tm').write_text(''.join(f'{qq} {bb} {w} {"R"if d==1 else"L"} {t}\n'for(qq,bb),(w,d,t)in sorted(folded.items())))
print('seconds',time.time()-begin,'best',best)
