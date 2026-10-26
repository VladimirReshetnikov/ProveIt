#!/usr/bin/env python3
"""Literal unweighted joint-orientation and power pooling at the frozen weighted source."""
import json,hashlib,sys,copy
from pathlib import Path
from polynomial_kernel import raw,ser,poly,add,mul,degree
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT/'source/pell209_affine.json'
def scale(p,c):return {m:c*v for m,v in p.items()if c*v}
def sq(p):return mul(p,p)
def sm(ps):
 out={}
 for p in ps:out=add(out,p)
 return out
def product(ps):
 out={():1}
 for p in ps:out=mul(out,p)
 return out
def lincomb(target,basis):
 from fractions import Fraction as F
 pivots={}
 for i,p in basis.items():
  row={m:F(c)for m,c in p.items()};coef={i:F(1)}
  while row:
   lead=min(row)
   if lead not in pivots:
    a=row[lead];pivots[lead]=({m:c/a for m,c in row.items()},{j:c/a for j,c in coef.items()});break
   rr,cc=pivots[lead];a=row[lead];row=add(row,rr,-a);coef=add(coef,cc,-a)
 row={m:F(c)for m,c in target.items()};answer={}
 while row:
  lead=min(row)
  if lead not in pivots:raise ValueError(('not in row span',lead,row[lead]))
  rr,cc=pivots[lead];a=row[lead];row=add(row,rr,-a);answer=add(answer,cc,a)
 if any(c.denominator!=1 for c in answer.values()):raise ValueError('nonintegral residual basis')
 return [[i,int(c)]for i,c in sorted(answer.items())]
def build(partition=((0,),(1,),(2,),(3,)),fuse=0,orientation_frame_shift=0):
 src=json.loads(SOURCE.read_text());n=len(src['variables']);names={v['name']:i for i,v in enumerate(src['variables'])};rows=[poly(r['terms'])for r in src['residuals']];labels={r['label']:i for i,r in enumerate(src['residuals'])}
 def var(s):return {(names[s],):1}
 one={():1};A=var('shared.A');D=add(A,one,-1);q=add(var('pow2.output'),one,-1);t=var('t0') if 't0' in names else add({():16},scale(var('cofinal.horizon_root'),32))
 pairs=[]
 ks={'index0':t,'index2':add(t,var('growth.F')),'index3':var('crt.encoded.a'),'index5':var('crt.encoded.b'),'index6':var('crt.encoded.c'),'index7':var('crt.encoded.d'),'index8':var('crt.encoded.S'),'index9':var('beta.y_plus_one'),'index10':var('crt.encoded.Sp'),'index11':var('crt.encoded.u'),'index12':var('x'),'index13':var('crt.encoded.vq'),'index14':scale(var('crt.even_index_half'),2)}
 wires={'index0':'mul.460','index2':'mul.503','index3':'mul.529','index5':'mul.554','index6':'mul.567','index7':'mul.580','index8':'mul.593','index9':'mul.606','index10':'mul.619','index11':'mul.632','index12':'mul.645','index13':'mul.658','index14':'mul.671'}
 normrows=[];gaterows=[]
 for name,k in ks.items():
  dd=var(name+'.X_minus_AY');yy=var(name+'.Y');xx=var(wires[name])
  if name in ['index0','index9','index12']:xx=add(xx,one)
  zz=add(xx,dd,-1);norm=sm([sq(xx),scale(sq(zz),-1),sq(yy),{():-1}]);gate=add(zz,mul(A,yy),-1)
  nr=[i for i,r in enumerate(rows)if r==norm or r==scale(norm,-1)];gr=[i for i,r in enumerate(rows)if r==gate or r==scale(gate,-1)]
  if len(nr)!=1 or len(gr)!=1:raise ValueError(('pair row mismatch',name,nr,gr))
  normrows+=nr;gaterows+=gr;pairs.append({'name':name,'k':k,'X':xx,'Y':yy,'Z':zz,'D':dd,'norm_row':nr[0],'gate_row':gr[0]})
 byname={p['name']:p for p in pairs};omega=sm([add(sq(add(p['X'],one,-1)),sq(add(p['Y'],p['k'],-1)))for p in pairs]);orient=names['cap.pooled_quotient'];orows=[i for i,r in enumerate(rows)if any(orient in m for m in r)]
 if len(orows)!=1:raise ValueError('orientation privacy')
 oi=orows[0];numerator=add(rows[oi],mul(D,{(orient,):1}));diff=add(omega,numerator,-1)
 guard_candidates=[i for i,p in enumerate(rows)if p.get((names['new_guard3.a'],names['new_guard3.a']))==-1 and not any(orient in m for m in p)]
 if len(guard_candidates)!=1:raise ValueError('guard row identification')
 orientation_adjust=lincomb(diff,{i:rows[i]for i in normrows+guard_candidates})
 specs=[('singleton1',var('choose0.output'),[('pow1.output','index12')]),('singleton2',sm([{():2},scale(var('growth.F'),2),scale(var('crt.even_index_half'),4)]),[(None,'index12')]),('radix',q,[('pow4.output','index0'),('pow11.output','index9'),('pow14.output','index12')]),('radix_plus_one',add(q,one),[('pow3.output','index2'),('pow5.output','index3'),('pow7.output','index5'),('pow8.output','index6'),('pow9.output','index7'),('pow10.output','index8'),('pow12.output','index10'),('pow13.output','index11'),('pow15.output','index13'),('pow16.output','index14')])]
 blocks=[];removed={orient} if fuse is not None else set();deleted={oi} if fuse is not None else set()
 for j,(name,base,rr)in enumerate(specs):
  requests=[{'m':q if output is None else var(output),'pair':pn}for output,pn in rr];T=sm([scale(mul(A,base),2),scale(sq(base),-1),{():-1}]);H=sm([mul(byname[r['pair']]['Y'],add(r['m'],byname[r['pair']]['X'],-1))for r in requests]);S=sm([add(sq(add(r['m'],byname[r['pair']]['D'],-1)),sq(byname[r['pair']]['Y']),-1)for r in requests]);E=add(S,scale(mul(base,H),2),-1)
  if j<2:
   singleton_id=j+1
   tv=names[f'base{singleton_id}.T'];qv=names[f'pow{singleton_id}.quotient'];private={tv,qv};hits=[i for i,row in enumerate(rows)if any(private.intersection(m)for m in row)]
   delta=sm([requests[0]['m'],scale(byname[requests[0]['pair']]['D'],-1),scale(mul(base,byname[requests[0]['pair']]['Y']),-1)])
   expect=[add({(tv,):1},T,-1),add(delta,{tuple(sorted((tv,qv))):1})]
   if len(hits)!=2 or not all(any(rows[i]==p or rows[i]==scale(p,-1)for i in hits)for p in expect):raise ValueError('singleton rows')
   extra={'T_variable':tv,'Q_variable':qv,'delta':delta}
  else:
   kv,lv=names[name+'.K'],names[name+'.L'];private={kv,lv};hits0=[i for i,p in enumerate(rows)if any(private.intersection(m)for m in p)]
   ia=next(i for i in hits0 if rows[i].get((kv,))==1 and not any(kv in m and m!=(kv,)for m in rows[i]));hits=[ia,next(i for i in hits0 if i!=ia)]
   ar=sm([{(kv,):1},scale(H,-2),scale(mul(add(scale(A,2),base,-1),{(lv,):1}),-1)]);br=sm([S,scale(mul(base,{(kv,):1}),-1),{(lv,):1}])
   if rows[hits[0]]!=ar:raise ValueError(('aggregate row',name))
   adjust=lincomb(add(br,rows[hits[1]],-1),{i:rows[i]for i in normrows})
   S=add(S,sm([scale(rows[i],c)for i,c in adjust]),-1);E=add(S,scale(mul(base,H),2),-1)
   extra={'K_variable':kv,'L_variable':lv,'norm_adjustments':adjust}
  removed|=private;deleted.update(hits)
  blocks.append({'name':name,'base':base,'T':T,'H':H,'S':S,'E':E,'requests':requests,'private':sorted(private),'rows':hits,**extra})
 for i,row in enumerate(rows):
  if i not in deleted and any(removed.intersection(m)for m in row):raise ValueError(('privacy',i))
 if sorted(j for group in partition for j in group)!=list(range(4)):raise ValueError('partition')
 proxy=omega;proxy_adjustments=[]
 if orientation_frame_shift:
  w=names['shared.W'];frame_candidates=[i for i,p in enumerate(rows)if p.get((w,))==1 and not any(w in m and m!=(w,)for m in p)and len(p)>20]
  if len(frame_candidates)!=1:raise ValueError('frame row')
  fi=frame_candidates[0]
  if fi in deleted:raise ValueError('frame row deleted')
  proxy=add(omega,rows[fi],orientation_frame_shift);proxy_adjustments=[[fi,orientation_frame_shift]]
 keep=[i for i in range(n)if i not in removed];ren={v:i for i,v in enumerate(keep)};outrows=[(src['residuals'][i]['label'],rows[i])for i in range(len(rows))if i not in deleted]
 variables=[src['variables'][i]for i in keep]
 for p,ids in enumerate(partition):
  z=n+p;ren[z]=len(variables);variables.append({'name':f'joint_pool.z{p}','kind':'unrestricted integer'});den=product([blocks[j]['T']for j in ids]);res=add(sm([mul(blocks[j]['E'],product([blocks[h]['T']for h in ids if h!=j]))for j in ids]),mul({(z,):1},den),-1)
  if p==fuse:res=add(mul(proxy,den),mul(D,res))
  outrows.append((f'joint_pool.{p}',res))
 def remap(p):return {tuple(sorted(ren[i]for i in m)):c for m,c in p.items()}
 out={'schema':'unweighted-joint-pooling-v1','domain':'unrestricted integers','polynomial':'sum(square(row) for row in residuals)','variables':variables,'residuals':[{'label':label,'terms':ser(remap(p))}for label,p in outrows]}
 def serialize(obj):
  if isinstance(obj,dict):
   if obj and all(isinstance(k,tuple)for k in obj):return ser(obj)
   return {k:serialize(v)for k,v in obj.items()}
  if isinstance(obj,list):return [serialize(x)for x in obj]
  return obj
 cert=serialize({'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'A':A,'D':D,'pairs':pairs,'blocks':blocks,'Omega':omega,'orientation_proxy':proxy,'orientation_proxy_adjustments':proxy_adjustments,'orientation_row':oi,'orientation_variable':orient,'orientation_identity':'Omega - (orientation_row + D*orientation_variable) = recorded retained row combination','orientation_adjustments':orientation_adjust,'norm_rows':normrows,'removed_variables':sorted(removed),'removed_rows':sorted(deleted),'retained_original_indices':keep,'partition':partition,'fused_group':fuse})
 return out,cert
if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path);ap.add_argument('--all',action='store_true');ap.add_argument('--partition');ap.add_argument('--fuse',default='0');ap.add_argument('--output',type=Path);ap.add_argument('--orientation-frame-shift',type=int,default=0);args=ap.parse_args()
 if args.source:SOURCE=args.source
 partition=json.loads(args.partition)if args.partition else(((0,1,2,3),)if args.all else((0,),(1,),(2,),(3,)))
 eq,cert=build(partition,None if args.fuse=='none' else int(args.fuse),args.orientation_frame_shift);degree0=2*max(degree(poly(r['terms']))for r in eq['residuals']);dest=args.output or ROOT/f'pell_joint{len(eq["variables"])}_degree{degree0}';dest.mkdir(exist_ok=True,parents=True);(dest/'equation.json').write_bytes(raw(eq));(dest/'certificate.json').write_bytes(raw(cert));print(dest,degree0,sum(len(r['terms'])for r in eq['residuals']))
