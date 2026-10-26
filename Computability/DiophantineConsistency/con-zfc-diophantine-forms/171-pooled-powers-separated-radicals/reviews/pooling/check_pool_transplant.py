"""Independent literal checker for the fixed-base pooling transplant.
Reads source/output JSON; imports only this review's sparse arithmetic.
"""
from pathlib import Path
import argparse,hashlib,json
from check_frame import add,scale,mul,terms,check as check_frame

def P(ts):return {tuple(m):c for c,m in ts if c}
def C(n):return {():n} if n else {}
def equal(a,b,label):
 if a!=b:raise ValueError(label)
def main(src,out):
 raw=src.read_bytes();a=json.loads(raw);b=json.loads((out/'equation.json').read_text());cert=json.loads((out/'pool_certificate.json').read_text());ps=[P(r['terms']) for r in a['residuals']];ns={v['name']:i for i,v in enumerate(a['variables'])}
 def V(n):return {(ns[n],):1}
 def shifted(n,k):return add(V(n),C(k))
 def unique(row,label):
  hits=[i for i,p in enumerate(ps) if p==row or p==scale(-1,row)]
  if len(hits)!=1:raise ValueError((label,hits))
  return hits[0]
 if cert['parent_equation_sha256']!=hashlib.sha256(raw).hexdigest():raise ValueError('bad source pin')
 frame=check_frame(src);A=shifted('shared.A',1);q=add(C(1),scale(4,V('radix.odd_square_root_half')))
 plus=[(3,2,'mul.503',0,0),(5,3,'mul.529',-1,0),(7,5,'mul.554',0,0),(8,6,'mul.567',0,0),(9,7,'mul.580',0,0),(10,8,'mul.593',0,0),(12,10,'mul.619',0,0),(13,11,'mul.632',0,0),(15,13,'mul.658',0,0),(16,14,'mul.671',0,0),(17,15,'mul.684',0,0)]
 radix=[(4,0,'mul.460',0,0),(11,9,'mul.606',0,0),(14,12,'mul.645',0,1)]
 removed_rows=set();removed_vars={ns['base3.T']};newrows=[];records=[]
 for gidx,(group,base,requests) in enumerate([('radix_plus_one',add(q,C(1)),plus),('radix',q,radix)]):
  T=add(scale(2,mul(A,base)),scale(-1,mul(base,base)),C(-1));Tcoord=V('base3.T') if not gidx else add(V('base3.T'),scale(-2,A),scale(2,q),C(1))
  mr=unique(add(Tcoord,scale(-1,T)),'modulus graph');removed_rows.add(mr)
  H={};S={};E={};U={};defect={}
  for req,pair,zname,ys,zs in requests:
   m=V('pow'+str(req)+'.output');X=shifted('index'+str(pair)+'.X',1);Y=shifted('index'+str(pair)+'.Y',ys);Z=shifted(zname,zs);quot=V('pow'+str(req)+'.quotient')
   D=add(m,scale(-1,X),Z);err=add(D,scale(-1,mul(base,Y)))
   hits=[i for i,p in enumerate(ps) if p in (add(err,mul(Tcoord,quot)),add(err,scale(-1,mul(Tcoord,quot))),scale(-1,add(err,mul(Tcoord,quot))),scale(-1,add(err,scale(-1,mul(Tcoord,quot)))))]
   if len(hits)!=1:raise ValueError(('power row',req,hits))
   ar=unique(add(Z,scale(-1,mul(A,Y))),'AY graph')
   nr=unique(add(mul(X,X),mul(Y,Y),scale(-1,mul(Z,Z)),C(-1)),'Pell norm')
   removed_rows.add(hits[0]);removed_vars.add(ns['pow'+str(req)+'.quotient'])
   H=add(H,mul(Y,add(m,scale(-1,X))));S=add(S,mul(D,D),scale(-1,mul(Y,Y)));E=add(E,mul(err,err));U=add(U,mul(Y,Y))
   defect=add(defect,scale(-2,mul(mul(base,Y),add(Z,scale(-1,mul(A,Y))))))
   records.append({'request':req,'power_row':hits[0],'AY_row':ar,'norm_row':nr})
  # This is a formal identity even before AY residuals vanish.
  equal(add(E,scale(-1,S),scale(2,mul(base,H)),mul(T,U)),defect,'pooled identity')
  ki=len(a['variables'])+2*gidx;li=ki+1;K={(ki,):1};L={(li,):1}
  newrows += [{'label':group+'.bilinear_aggregate','terms':terms(add(K,scale(-2,H),scale(-1,mul(add(scale(2,A),scale(-1,base)),L))))},{'label':group+'.pooled_norm','terms':terms(add(S,scale(-1,mul(base,K)),L))}]
  g=cert['groups'][gidx]
  for k,val in [('base',base),('A',A),('T',T),('H',H),('S',S),('sumY2',U),('modulus_expression',Tcoord)]:equal(P(g[k]),val,'certificate '+k)
  if g['norm_reduced']:raise ValueError('unexpected norm-reduced experiment')
 if cert['frame_strengthened']:raise ValueError('unexpected strengthened frame')
 for edit in cert['frame_edits']:equal(P(edit['old']),P(edit['new']),'frame changed')
 equal(sorted(removed_rows),cert['removed_rows'],'row deletion manifest');equal(sorted(removed_vars),cert['removed_variables'],'coordinate deletion manifest')
 variables=a['variables']+[{'kind':'pooled_power','name':g+'.'+v} for g in ['radix_plus_one','radix'] for v in ['K','L']]
 keep=[i for i in range(len(variables)) if i not in removed_vars];ren={i:j for j,i in enumerate(keep)}
 equal([[i,j] for i,j in ren.items()],cert['old_to_new'],'renumber map')
 rows=[r for i,r in enumerate(a['residuals']) if i not in removed_rows]+newrows
 final=[]
 for r in rows:
  if any(i in removed_vars for _,m in r['terms'] for i in m):raise ValueError('deleted variable survives')
  final.append({'label':r['label'],'terms':[[c,[ren[i] for i in m]] for c,m in r['terms']]})
 equal(final,b['residuals'],'literal output residuals');equal([variables[i] for i in keep],b['variables'],'literal output variables')
 poly=add(*(mul(P(r['terms']),P(r['terms'])) for r in final))
 equal(poly,P(json.loads((out/'expanded_polynomial.json').read_text())['terms']),'complete SOS expansion')
 metrics={'variables':len(keep),'rows':len(final),'degree':max(map(len,poly)),'monomials':len(poly),'height':max(map(abs,poly.values())),'row_height':max(abs(c) for r in final for c,_ in r['terms'])}
 equal(metrics,json.loads((out/'METRICS.json').read_text()),'all metrics')
 return {'passed':True,'source_sha256':hashlib.sha256(raw).hexdigest(),'output_sha256':hashlib.sha256((out/'equation.json').read_bytes()).hexdigest(),'frame_covered_requests':frame['requests_covered'],'retained_rows_authenticated':records,'metrics':metrics}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('source',type=Path);ap.add_argument('pooled',type=Path);ap.add_argument('--output',type=Path);a=ap.parse_args();r=main(a.source,a.pooled);s=json.dumps(r,sort_keys=True,indent=2)+'\n';print(s)
 if a.output:a.output.write_text(s)
