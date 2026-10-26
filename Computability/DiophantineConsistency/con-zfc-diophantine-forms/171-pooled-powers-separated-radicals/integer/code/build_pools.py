"""Pool fixed-base Pell power congruences using the existing square frame.

This producer authenticates each replaced literal polynomial identity.
Existential soundness of pooled rows depends on the unbounded small-error
lemma and the inherited square-frame bound described in the report.
"""
import argparse,json,hashlib,copy
from pathlib import Path
from collections import defaultdict

def add(*ps):
 d=defaultdict(int)
 for p in ps:
  for m,c in p.items():d[m]+=c
 return {m:c for m,c in d.items() if c}
def scale(k,p):return {m:k*c for m,c in p.items() if k*c}
def sub(p,q):return add(p,scale(-1,q))
def mul(p,q):
 d=defaultdict(int)
 for m,c in p.items():
  for n,b in q.items():d[tuple(sorted(m+n))]+=c*b
 return {m:c for m,c in d.items() if c}
def v(i):return {(i,):1}
def c(i):return {():i} if i else {}
def tp(p):return [[x,list(m)] for m,x in sorted(p.items())]
def write(p,x):p.write_text(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n')

def main(parent_path,out,norm_reduce=False,strong_frame=False):
 raw=parent_path.read_bytes();a=json.loads(raw);rows=[{tuple(m):z for z,m in r['terms']} for r in a['residuals']];names={vv['name']:i for i,vv in enumerate(a['variables'])};variables=copy.deepcopy(a['variables']);n=len(variables)
 def named(s,shift=0):return add(v(names[s]),c(shift))
 A=named('shared.A',1);q=add(scale(4,named('radix.odd_square_root_half')),c(1))
 # (power request, shared principal pair, existing A*Y gate, Y shift, Z shift).
 plus=[(3,2,'mul.503',0,0),(5,3,'mul.529',-1,0),(7,5,'mul.554',0,0),(8,6,'mul.567',0,0),(9,7,'mul.580',0,0),(10,8,'mul.593',0,0),(12,10,'mul.619',0,0),(13,11,'mul.632',0,0),(15,13,'mul.658',0,0),(16,14,'mul.671',0,0),(17,15,'mul.684',0,0)]
 radix=[(4,0,'mul.460',0,0),(11,9,'mul.606',0,0),(14,12,'mul.645',0,1)]
 delete_vars=set();delete_rows=set();add_rows=[];cert=[]
 for label,base,modulusname,requests in [('radix_plus_one',add(q,c(1)),'base3.T',plus),('radix',q,None,radix)]:
  H={};S={};sumY2={};normsum={};request_records=[];modvar=names['base3.T'];modexpr=v(modvar) if modulusname else add(v(modvar),scale(-2,A),scale(2,q),c(1));T=sub(sub(scale(2,mul(A,base)),mul(base,base)),c(1))
  # Existing modulus may have either sign convention; infer it from its row.
  modulus_candidates=[]
  for j,r in enumerate(rows):
   if r==sub(modexpr,T) or r==sub(T,modexpr):modulus_candidates.append(j)
  if len(modulus_candidates)!=1:raise ValueError(('modulus row not found',label,modulus_candidates))
  delete_rows.add(modulus_candidates[0]);delete_vars.add(modvar)
  for pno,ino,zname,yshift,zshift in requests:
   m=named(f'pow{pno}.output');X=named(f'index{ino}.X',1);Y=named(f'index{ino}.Y',yshift);Z=named(zname,zshift);Q=named(f'pow{pno}.quotient');qi=names[f'pow{pno}.quotient']
   # Stored modulus may represent negative T: infer from old power row.
   e=add(m,scale(-1,X),Z,scale(-1,mul(base,Y)))
   candidates=[]
   for j,r in enumerate(rows):
    if r in (add(e,mul(modexpr,Q)),sub(e,mul(modexpr,Q)),scale(-1,add(e,mul(modexpr,Q))),scale(-1,sub(e,mul(modexpr,Q)))):candidates.append(j)
   if len(candidates)!=1:raise ValueError(('power row not found',pno,candidates,tp(e)))
   # Authenticate A*Y relation in retained source.
   relation=sub(Z,mul(A,Y))
   gaterows=[j for j,r in enumerate(rows) if r==relation or r==scale(-1,relation)]
   if len(gaterows)!=1:raise ValueError(('A*Y gate failed',pno,gaterows))
   delete_rows.add(candidates[0]);delete_vars.add(qi)
   H=add(H,mul(Y,sub(m,X)));D=add(sub(m,X),Z);S=add(S,mul(D,D),scale(-1,mul(Y,Y)));sumY2=add(sumY2,mul(Y,Y))
   norm=add(mul(X,X),mul(Y,Y),scale(-1,mul(Z,Z)),c(-1))
   normrows=[j for j,r in enumerate(rows) if r==norm or r==scale(-1,norm)]
   if len(normrows)!=1:raise ValueError(('Pell norm not found',pno,normrows))
   if norm_reduce:S=add(S,norm);normsum=add(normsum,norm)
   request_records.append({'request':pno,'pair':ino,'output':tp(m),'X':tp(X),'Y':tp(Y),'Z':tp(Z),'removed_quotient':qi,'removed_row':candidates[0],'retained_AY_row':gaterows[0],'retained_norm_row':normrows[0]})
  ki=len(variables);li=ki+1;variables += [{'kind':'pooled_power','name':label+'.K'},{'kind':'pooled_power','name':label+'.L'}]
  # K = 2H + (2A-base)L; S-base*K+L=0.
  rK=sub(sub(v(ki),scale(2,H)),mul(sub(scale(2,A),base),v(li)))
  rL=add(S,scale(-1,mul(base,v(ki))),v(li))
  add_rows += [{'label':label+'.bilinear_aggregate','terms':tp(rK)},{'label':label+'.pooled_norm','terms':tp(rL)}]
  # Certificate of algebraic expansion with E=sum(errors^2):
  E={}
  for rec in request_records:
   rr=lambda s:{tuple(m):z for z,m in rec[s]}
   e=add(rr('output'),scale(-1,rr('X')),rr('Z'),scale(-1,mul(base,rr('Y'))))
   E=add(E,mul(e,e))
  # E = S - 2nH - T sumY² modulo Z=AY.
  discrepancy=sub(E,add(S,scale(-2,mul(base,H)),scale(-1,mul(T,sumY2))))
  expected=scale(-1,normsum)
  for rec in request_records:
   rr=lambda s:{tuple(m):z for z,m in rec[s]}
   expected=add(expected,scale(-2,mul(mul(base,rr('Y')),sub(rr('Z'),mul(A,rr('Y'))))))
  if discrepancy!=expected:raise ValueError('pool algebra failed')
  cert.append({'group':label,'base':tp(base),'A':tp(A),'T':tp(T),'requests':request_records,'new_K':ki,'new_L':li,'modulus_expression':tp(modexpr),'modulus_coordinate':modvar,'modulus_row':modulus_candidates[0],'H':tp(H),'S':tp(S),'sumY2':tp(sumY2),'new_rows':add_rows[-2:],'norm_reduced':norm_reduce,'norm_sum':tp(normsum)})
 # Authenticate both original frame rows. An optional research flag can strengthen them; the principal retains them.
 W=named('shared.W');Zseed=named('shared.Zminus1');frameY=named('mul.450');frameZ=named('mul.451')
 old1=add(frameY,W,scale(-2,mul(W,Zseed)));new1=add(frameY,scale(4,W),scale(-8,mul(W,Zseed)))
 old2=sub(frameZ,mul(add(W,c(1)),frameY));new2=sub(frameZ,mul(add(scale(4,W),c(1)),frameY))
 edits={};frame=[]
 for old,new in [(old1,new1),(old2,new2)]:
  hits=[j for j,r in enumerate(rows) if r==old]
  if len(hits)!=1:raise ValueError('frame row not found')
  edits[hits[0]]=new if strong_frame else old;frame.append({'row':hits[0],'old':tp(old),'new':tp(new if strong_frame else old)})
 pre=[];origin=[]
 for j,rr in enumerate(a['residuals']):
  if j in delete_rows:continue
  p=edits.get(j,rows[j])
  if any(i in delete_vars for mon in p for i in mon):raise ValueError(('deleted variable remains',j))
  pre.append({'label':rr['label'],'terms':tp(p)});origin.append(j)
 pre+=add_rows;origin+=[None]*len(add_rows)
 keep=[i for i in range(len(variables)) if i not in delete_vars];ren={i:j for j,i in enumerate(keep)}
 finalrows=[dict(rr,terms=[[z,[ren[i] for i in mon]] for z,mon in rr['terms']]) for rr in pre]
 result={'schema':'conzfc-pooled-powers-v1','domain':'unrestricted integers','polynomial':'sum(square(row) for row in residuals)','variables':[variables[i] for i in keep],'residuals':finalrows,'variant':f'pooled{len(keep)}','parent_equation_sha256':hashlib.sha256(raw).hexdigest(),'source_commit':'892d73e1ab4bc5fd34ecca1967b06dc47ca95494'}
 poly={}
 for rr in finalrows:
  p={tuple(m):z for z,m in rr['terms']};poly=add(poly,mul(p,p))
 metrics={'variables':len(keep),'rows':len(finalrows),'degree':max(map(len,poly)),'monomials':len(poly),'height':max(map(abs,poly.values())),'row_height':max(abs(z) for rr in finalrows for z,_ in rr['terms'])}
 certificate={'schema':'pooled_powers_certificate_v1','parent_equation_sha256':hashlib.sha256(raw).hexdigest(),'groups':cert,'frame_edits':frame,'frame_strengthened':strong_frame,'removed_variables':sorted(delete_vars),'removed_rows':sorted(delete_rows),'old_to_new':[[i,j] for i,j in ren.items()],'new_row_parent_indices':origin}
 out.mkdir(parents=True,exist_ok=True)
 for fn,obj in [('equation.json',result),('expanded_polynomial.json',{'schema':'sparse-polynomial-v1','variables':len(keep),'domain':'unrestricted integers','terms':tp(poly)}),('METRICS.json',metrics),('pool_certificate.json',certificate)]:write(out/fn,obj)
 print(json.dumps(metrics))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--parent',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--norm-reduce',action='store_true');ap.add_argument('--strong-frame',action='store_true');a=ap.parse_args();main(a.parent,a.output,a.norm_reduce,a.strong_frame)
