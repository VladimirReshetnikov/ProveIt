import sys,json,time
from pathlib import Path
import symbolic as S,compile_grammar as C
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'math_reduction/folding'))
import compatible_folds as F

def analyze(path,full=False):
 data=json.loads(Path(path).read_text());C.TOKENS=data['tokens']
 m,t,new,entry=C.compile_grammar(data)
 reached={0};todo=[0]
 while todo:
  q=todo.pop()
  for b in (0,1):
   if(q,b)not in m:continue
   z=m[q,b][2]
   if z not in reached:reached.add(z);todo.append(z)
 removed=sorted({q for q,b in m}-reached)
 m={k:v for k,v in m.items()if k[0]in reached}
 protected={q for q,b in S.ENGINE_ROWS}|{m[k][2] for k in S.ENGINE_ROWS if k in m}|{0,S.ROOT}
 opts=F.candidates(m,{q for q,b in m if q not in protected})
 selected,tested=F.best_subset(m,opts)
 folded,_=F.fold(m,selected)
 result=dict(file=str(path),pure=len(m)//2,folded=len(folded)//2,removed=removed,folds=selected,options=len(opts),tested=tested)
 if full:
  for k,mm in [('pure',m),('folded',folded)]:
   check=C.check(mm,t,True);fail=check.pop('failures');result[k+'_check']=check|dict(failcount=len(fail),firstfail=fail[:20])
  out=Path(__file__).with_name('candidates');stem=Path(path).stem
  (out/(stem+'_safe.tm')).write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(folded.items())))
  (out/(stem+'_safe.json')).write_text(json.dumps(dict(tree=t,certificate=result),indent=2))
 return result
if __name__=='__main__':
 ps=list(Path('verification').glob('open_physical_*.json')) if len(sys.argv)<2 else list(map(Path,sys.argv[1:]))
 best=1000;st=time.time()
 for i,p in enumerate(ps):
  r=analyze(p)
  if r['folded']<best:
   best=r['folded'];print('BEST',json.dumps(r),flush=True)
   if best<196:print('CHECK',json.dumps(analyze(p,True)),flush=True);break
 print('done',len(ps),best,time.time()-st,flush=True)
