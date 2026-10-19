if not __debug__:raise RuntimeError('Assertions required')
import biased_reference_copy19 as C,marked_unary_copy as M
from pathlib import Path
import itertools,json,hashlib
T,s,ret,ids=C.compile_copy(variable_anchor=True);count=0;maxsteps=0
for r,idx,alen,gextra in itertools.product(range(15),range(4),range(1,8),(2,3,8)):
 vals=[0,4,1,3];vals[idx]=r+2;gap=r+gextra;c=-3
 anchor=c+gap+1;p=anchor+alen+1;one={c}|set(range(anchor,anchor+alen));starts=[]
 for v in vals:starts.append(p);one.update(range(p,p+v+1));p+=v+2
 src=starts[idx];one.remove(src);one|={c-3,c-1,p,p+3}
 expected=one|set(range(c,c+r+1))|{src}
 actual,h,steps,window=M.run(T,s,ret,one,src)
 assert actual==expected and h==c+r and window[0]>=c and window[1]<=src+r+3
 count+=1;maxsteps=max(maxsteps,steps)
text=f'#! start {s}\n'+''.join(f'{q} {b} {w} {d} {n}\n'for(q,b),(w,d,n)in sorted(T.items()))
out=Path(__file__).parent;(out/'biased_reference_copy_19_variable_anchor.tm').write_text(text)
result={'status':'PASS','cases':count,'working_states':19,'max_steps':maxsteps,'sha256':hashlib.sha256(text.encode()).hexdigest(),'scope':'Variablepositiveanchor validframes; testedlengths1through7. Generalization follows samefiniteones-scan induction.'}
(out/'variable_anchor_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
