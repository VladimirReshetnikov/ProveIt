"""Price every one-step closed source rotation on the exact 246 runtime.
Source transformations are closed-sequence reassociations or commuting CI pairs.
Affine successes are initialized-runtime claims only; blank bootstrap and
an explicit source simulation remain separate obligations.
"""
from recompile_decoder import *
sys.path.insert(0,str(Path(__file__).resolve().parent))
import rotate_search as rot
results=[];best=246;begin=time.monotonic();counts=Counter()
options=rot.options(NODES);rank=Counter()
print('OPTIONS',len(options),flush=True)
for idx,(n,exp,kind) in enumerate(options):
 nodes,root=rot.mutate(NODES,ROOT,n,exp)
 zero=rot.zero_metrics(nodes,root)
 if zero[1]>7 or zero[2]>40:
  results.append(dict(index=idx,node=n,kind=kind,status='shape_bound',metrics=zero));continue
 C=make_cases(get_sites(nodes,root));passed=False
 for generic in (False,True):
  try:U,meta,entry=emit(nodes,root,generic=generic)
  except Exception as ex:
   result=dict(status='emitter_unsupported',message=str(ex));continue
  table=Track(U);table.used=set();error=None
  for i in sorted(range(len(C)),key=lambda i:-rank[i]):
   p,branch,target,halt=C[i]
   try:A.run(table,p,branch,target,halt=halt,fuel=1000)
   except Exception as ex:rank[i]+=1;error=dict(case=i,pc=p,branch=branch,message=str(ex));break
  if error:result=dict(status='affine_failure',error=error,generic=generic)
  else:
   retained={q for q,b in table.used|PAIRS};size=len(retained)
   result=dict(status='PASS',states=size,generic=generic,retained=sorted(retained,key=int))
   if size<=best:
    best=size;print('CANDIDATE',idx,n,kind,'states',size,'zero',zero,flush=True)
    out=Path(__file__).with_name('rotation-'+str(idx)+'-'+str(size));out.mkdir(exist_ok=True)
    (out/'dag.json').write_text(json.dumps(dict(root=root,nodes=nodes,parent_node=n,operation=kind,expression=exp),indent=2)+'\n')
    # Undefined, uninspected rows can point to95, but no retained state is deleted.
    pruned={e:(w,d,t if t in retained or t=='254' else '95') for e,(w,d,t) in U.items() if e[0] in retained}
    (out/'machine.tm').write_text('#! start 95\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(pruned.items(),key=lambda x:(int(x[0][0]),x[0][1]))))
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
   passed=True;break
 result.update(index=idx,node=n,kind=kind,nodes=len(nodes),metrics=zero)
 results.append(result);counts[result['status']]+=1
 print(idx,kind,len(nodes),result['status'],result.get('states'),round(time.monotonic()-begin,2),flush=True)
 Path(__file__).with_name('rotation-246-results.json').write_text(json.dumps(dict(options=len(options),best_states=best,counts=counts,seconds=time.monotonic()-begin,results=results),indent=2)+'\n')
