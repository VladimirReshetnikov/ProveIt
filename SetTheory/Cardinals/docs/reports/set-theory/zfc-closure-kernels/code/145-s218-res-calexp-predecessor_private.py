from one_fixed_k import *

def makeprev(which,shape):
 mapping={**o.M,'p':o.M['a'],'y':o.M['b'],'C':o.M['c'],'c':(o.M['c'],INC)};mapping[which]=PUSH0
 i=2650;edits=[]
 for old,new in zip(OLDWORD,NEWWORD):
  j=i+len(z.flat(o.M[old]))
  # V must keep its original parameters, including c.
  if i>=2650+sum(len(z.flat(o.M[x]))for x in o.postfix(o.v,set())):
   repl=mapping[new]
   if repl!=o.M[old]:edits.append((i,j,repl))
  i=j
 t=z.TREE
 for a,b,repl in reversed(edits):t=splice(t,a,b,repl)
 return t

if __name__=='__main__':
 out=ROOT/'predecessor_results';out.mkdir(exist_ok=True);rs=[]
 for which in ['p','y']:
  t=makeprev(which,'right');rows=z.s.sites(t);assert z.s.graph_arithmetic(rows)[0]==z.s.graph_intervals(rows)
  r={'which':which,'fixed_public_label':0,'matrix':'c+1','private':'c','metrics':z.s.metrics(t)}
  d=out/which;d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(z.s.compact(rows))
  try:tt,mm=z.compile_tree(z.T,z.TREE,t);r['compiler']=mm;(d/'candidate.tm').write_bytes(z.b.table_bytes(tt))
  except Exception as e:r['error']=repr(e)
  rs.append(r);print(json.dumps(r),flush=True)
 (out/'summary.json').write_text(json.dumps(rs,indent=2)+'\n')
