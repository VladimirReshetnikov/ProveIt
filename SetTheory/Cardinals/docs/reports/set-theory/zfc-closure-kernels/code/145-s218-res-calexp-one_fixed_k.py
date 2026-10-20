from fixed_k import *

def onefixed(which,n,shape):
 mapping={**o.M,'p':o.M['a'],'y':o.M['b'],'C':o.M['c']};mapping[which]=pushconst(n,shape)
 i=2650;edits=[]
 for old,new in zip(OLDWORD,NEWWORD):
  j=i+len(z.flat(o.M[old]))
  if mapping[new]!=o.M[old]:edits.append((i,j,mapping[new]))
  i=j
 t=z.TREE
 for a,b,repl in reversed(edits):t=splice(t,a,b,repl)
 return t

if __name__=='__main__':
 out=ROOT/'one_fixed_k_results';out.mkdir(exist_ok=True);rs=[]
 for which,n,shape in itertools.product(['p','y'],[1,8,17],['right','left','balanced']):
  t=onefixed(which,n,shape);rows=z.s.sites(t);assert z.s.graph_arithmetic(rows)[0]==z.s.graph_intervals(rows)
  r={'which':which,'constant':n,'shape':shape,'metrics':z.s.metrics(t)}
  d=out/f'{which}{n}_{shape}';d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(z.s.compact(rows))
  try:
   tt,mm=z.compile_tree(z.T,z.TREE,t);r['compiler']=mm;(d/'candidate.tm').write_bytes(z.b.table_bytes(tt))
  except Exception as e:r['error']=repr(e)
  rs.append(r);print(json.dumps(r),flush=True)
 (out/'summary.json').write_text(json.dumps(rs,indent=2)+'\n')
