from fixed_k import *

def makeU(first,second,shape):
 A=o.M[first];B=o.M[second];R=o.M['R']
 new=(A,(B,R))if shape=='right'else((A,B),R)
 return splice(z.TREE,161,194,new)

if __name__=='__main__':
 out=ROOT/'rho8_membership_results';out.mkdir(exist_ok=True);rr=[]
 for a,b in itertools.permutations(['a','b','c'],2):
  for shape in['left','right']:
   tree=makeU(a,b,shape);rows=z.s.sites(tree);assert z.s.graph_arithmetic(rows)[0]==z.s.graph_intervals(rows)
   r={'U':[a,b],'shape':shape,'source_metrics':z.s.metrics(tree)}
   d=out/f'{a}{b}_{shape}';d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(z.s.compact(rows))
   try:tt,mm=z.compile_tree(z.T,z.TREE,tree);r['compiler']=mm;(d/'candidate.tm').write_bytes(z.b.table_bytes(tt))
   except Exception as e:r['error']=repr(e)
   rr.append(r);print(json.dumps(r),flush=True)
 (out/'summary.json').write_text(json.dumps(rr,indent=2)+'\n')
