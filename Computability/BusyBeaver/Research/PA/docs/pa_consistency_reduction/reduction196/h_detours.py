from pathlib import Path
import sys,json,time
from search_generic import S,candidates
from site_contexts import contexts
root=Path(__file__).resolve().parents[1]
base=root/'comparison/audit/h_catalan_node170_3_133_37'
m=S.load_machine(str(base)+'.tm')
sites=json.loads(Path(str(base)+'_sites.json').read_text())
sites=[(tuple(p),tuple(op))for p,op in sites]
S.all_sites=lambda:sites
begin=time.time();ctx=contexts(4,True,m)
print('contexts',sum(map(len,ctx.values())),flush=True)
result=candidates(m,ctx)
print('candidates',result,flush=True)
for q,p,a0,a1 in result:
    n=m.copy();n[q,0]=a0;n[q,1]=a1;del n[p,0];del n[p,1]
    n={k:(w,d,q if s==p else s)for k,(w,d,s)in n.items()}
    try:checks,_=S.verify(n)
    except Exception as e:print('failed',q,p,e,flush=True);continue
    print('SUCCESS',q,p,a0,a1,checks,flush=True)
    Path(__file__).with_name('h_detour_success.json').write_text(json.dumps((q,p,a0,a1)))
    Path(__file__).with_name('h_detour_success.tm').write_text(''.join(f'{qq} {bb} {w} {"R"if d==1 else"L"} {t}\n'for(qq,bb),(w,d,t)in sorted(n.items())))
print('seconds',time.time()-begin)
