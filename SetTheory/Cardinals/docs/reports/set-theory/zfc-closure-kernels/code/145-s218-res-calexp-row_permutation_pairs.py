from row_permutations import *
import time

if __name__=='__main__':
 out=ROOT/'row_permutation_pair_results';out.mkdir(exist_ok=True);rs=[];start=time.time();best=206
 perms={i:[p for p in itertools.permutations(('a','b','c')) if p!=('a','b','c')]for i in range(8)}
 perms[8]=[('b','a','c')]
 for i,j in itertools.combinations(range(9),2):
  for p,q in itertools.product(perms[i],perms[j]):
   t,words,paths=make({i:p,j:q});m=z.s.metrics(t)
   r={'rows':[i,j],'row_names':[NAMES[i],NAMES[j]],'permutations':[p,q],'source_metrics':m}
   if m['dag_nodes']<=206:
    name=NAMES[i]+'_'+''.join(p)+'__'+NAMES[j]+'_'+''.join(q)
    d=out/name;d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(z.s.compact(z.s.sites(t)));r['sites_file']=str(d/'sites.json')
    print(json.dumps(r),flush=True)
   if m['dag_nodes']<best:best=m['dag_nodes']
   rs.append(r)
 (out/'summary.json').write_text(json.dumps(rs,indent=2)+'\n')
 print(json.dumps({'cases':len(rs),'best':best,'seconds':time.time()-start}),flush=True)
