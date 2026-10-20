from row_permutations import *

if __name__=='__main__':
 out=ROOT/'fused_t_explosion_results';out.mkdir(exist_ok=True);res=[]
 base=z.TREE
 # The original rho6 postfix pieces begin at895. Remove the outer
 # binder push [895,921) and its Q constructor [1049,1078).
 w=o.postfix(o.FORMULAS[2],set());i=895;parts=[]
 for k in w:
  j=i+len(z.flat(o.M[k]));parts.append((k,i,j));i=j
 print(parts,flush=True)
 assert i==1178
 # Original: a a c Q 1 I Q 1 I c I.
 assert w==['a','a','c','Q',1,'I','Q',1,'I','c','I']
 t=base
 for at in [6,0]:
  _,lo,hi=parts[at];t=splice(t,lo,hi,None)
 t,paths=compose(t)
 met=z.s.metrics(t);name='deleted_outer_quantifier';d=out/name;d.mkdir(exist_ok=True);rows=z.s.sites(t)
 assert z.s.graph_arithmetic(rows)[0]==z.s.graph_intervals(rows)
 (d/'sites.json').write_bytes(z.s.compact(rows));r={'name':name,'source_metrics':met,'status':'LOGICAL_CALIBRATION_OPEN','axiom':'N(N(Q_a c)) -> c'};res.append(r);print(json.dumps(r),flush=True)
 # Whole-row serializations with six independent binder/matrix choices.
 for binder,matrix in itertools.permutations(['a','b','c'],2):
  for shape in ['right','left']:
   word=[binder,matrix,'Q',1,'I',1,'I',matrix,'I'];ms=[o.M[k]for k in word]
   q=z.serial(ms)if shape=='right'else ms[0]
   if shape=='left':
    for nxt in ms[1:]:q=(q,nxt)
   tt=splice(base,895,1178,q);tt,paths=compose(tt);met=z.s.metrics(tt)
   name=binder+matrix+'_'+shape;r={'name':name,'source_metrics':met,'status':'LOGICAL_CALIBRATION_OPEN','axiom':f'N(N(Q_{binder} {matrix})) -> {matrix}'}
   if met['dag_nodes']<=206:
    d=out/name;d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(z.s.compact(z.s.sites(tt)));r['sites_file']=str(d/'sites.json')
   res.append(r);print(json.dumps(r),flush=True)
 (out/'summary.json').write_text(json.dumps(res,indent=2)+'\n')
