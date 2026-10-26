#!/usr/bin/env python3
"""Independent source-port and emitted residual check; imports no research producer."""
from pathlib import Path
from collections import defaultdict
import json,hashlib,copy
R=Path(__file__).resolve().parent
def poly(ts):
 p=defaultdict(int)
 for c,m in ts:p[tuple(sorted(m))]+=c
 return {m:c for m,c in p.items()if c}
def add(*ps):
 d=defaultdict(int)
 for p in ps:
  for m,c in p.items():d[m]+=c
 return {m:c for m,c in d.items()if c}
def scale(p,k):return {m:c*k for m,c in p.items()if c*k}
def mul(a,b):
 d=defaultdict(int)
 for m,c in a.items():
  for n,e in b.items():d[tuple(sorted(m+n))]+=c*e
 return {m:c for m,c in d.items()if c}
def sq(p):return mul(p,p)
def sub(a,b):return add(a,scale(b,-1))
def prod(ps):
 a={():1}
 for b in ps:a=mul(a,b)
 return a
def require(b,msg):
 if not b:raise ValueError(msg)
def equal(a,b,msg):require(a==b,msg)
def check_seed(SOURCE,folder):
 SOURCE=Path(SOURCE);folder=Path(folder)
 c=json.loads((folder/'certificate.json').read_text())
 source=json.loads(SOURCE.read_text());rows=[poly(r['terms'])for r in source['residuals']];names={x['name']:i for i,x in enumerate(source['variables'])}
 eq=json.loads((folder/'equation.json').read_text());c=json.loads((folder/'certificate.json').read_text())
 require(c['source_sha256']==hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'source hash')
 one={():1};v=lambda name:{(names[name],):1};A=v('shared.A');D=sub(A,one);q=sub(v('pow2.output'),one);t=v('t0') if 't0' in names else add({():16},scale(v('cofinal.horizon_root'),32))
 equal(poly(c['A']),A,'A');equal(poly(c['D']),D,'D')
 expected_indices={'index0':t,'index2':add(t,v('growth.F')),'index3':v('crt.encoded.a'),'index5':v('crt.encoded.b'),'index6':v('crt.encoded.c'),'index7':v('crt.encoded.d'),'index8':v('crt.encoded.S'),'index9':v('beta.y_plus_one'),'index10':v('crt.encoded.Sp'),'index11':v('crt.encoded.u'),'index12':v('x'),'index13':v('crt.encoded.vq'),'index14':scale(v('crt.even_index_half'),2)}
 require({p['name']for p in c['pairs']}==set(expected_indices),'all14pairs')
 pairs={};omega={};normsum={};gaterows=[];normrows=[]
 for p in c['pairs']:
  pn=p['name'];X,Y,Z,k=[poly(p[t])for t in ['X','Y','Z','k']];dd=v(pn+'.X_minus_AY');yy=v(pn+'.Y')
  if pn in ['index0','index9','index12']:
   require(any(X==add(v(w),one) for w in ['mul.460','mul.606','mul.645']),'shifted X actual chart')
  equal(Y,yy,'Y chart');equal(k,expected_indices[pn],'nominal index');equal(sub(X,Z),dd,'X decomposition')
  gate=sub(Z,mul(A,Y));norm=add(sq(X),scale(sq(Z),-1),sq(Y),scale(one,-1))
  gr,nr=p['gate_row'],p['norm_row'];require(rows[gr]in [gate,scale(gate,-1)],'gate row');require(rows[nr]in [norm,scale(norm,-1)],'norm row')
  gaterows.append(gr);normrows.append(nr);normsum=add(normsum,norm);omega=add(omega,sq(sub(X,one)),sq(sub(Y,k)));pairs[pn]=(X,Y,Z,dd,k)
 equal(poly(c['Omega']),omega,'Omega literal')
 oi,ov=c['orientation_row'],c['orientation_variable'];adjust=add(*[scale(rows[i],a)for i,a in c['orientation_adjustments']]);equal(sub(omega,add(rows[oi],mul(D,{(ov,):1}))),adjust,'orientation exact ideal identity');require(all(i!=oi for i,a in c['orientation_adjustments']),'orientation correction uses retained rows')
 specs=[(v('choose0.output'),[('pow1.output','index12')]),(add({():2},scale(v('growth.F'),2),scale(v('crt.even_index_half'),4)),[(None,'index12')]),(q,[('pow4.output','index0'),('pow11.output','index9'),('pow14.output','index12')]),(add(q,one),[('pow3.output','index2'),('pow5.output','index3'),('pow7.output','index5'),('pow8.output','index6'),('pow9.output','index7'),('pow10.output','index8'),('pow12.output','index10'),('pow13.output','index11'),('pow15.output','index13'),('pow16.output','index14')])]
 blocks=[];fused=c['fused_group'] is not None and c['fused_group']>=0;deleted={oi}if fused else set();private={ov}if fused else set();requests=0
 for j,(b,sp)in enumerate(zip(c['blocks'],specs)):
  base=sp[0];equal(poly(b['base']),base,'base actual expression')
  expected=[(v(o)if o else q,pn)for o,pn in sp[1]];require(len(b['requests'])==len(expected),'request count')
  H={};S={};sumdelta={};sumY={};gatecorrection={}
  for req,(m,pn)in zip(b['requests'],expected):
   require(req['pair']==pn,'request pair');equal(poly(req['m']),m,'request output');X,Y,Z,dd,k=pairs[pn]
   H=add(H,mul(Y,sub(m,X)));S=add(S,sq(sub(m,dd)),scale(sq(Y),-1));delta=sub(sub(m,dd),mul(base,Y));sumdelta=add(sumdelta,sq(delta));sumY=add(sumY,sq(Y));gatecorrection=add(gatecorrection,scale(mul(mul(base,Y),sub(Z,mul(A,Y))),2));requests+=1
  T=add(scale(mul(A,base),2),scale(sq(base),-1),scale(one,-1));correction=add(*[scale(rows[i],a)for i,a in b.get('norm_adjustments',[])]);require(all(i in normrows for i,a in b.get('norm_adjustments',[])),'norm adjustment retained');S=sub(S,correction);E=sub(S,scale(mul(base,H),2))
  for key,val in [('T',T),('E',E),('H',H),('S',S)]:equal(poly(b[key]),val,key+' formula')
  # Verify the exact polynomial ideal correction rather than assuming AY wires.
  equal(sub(add(sumdelta,gatecorrection),correction),sub(E,mul(T,sumY)),'squared-error ideal identity')
  if j<2:
   tv,qv=b['T_variable'],b['Q_variable'];rr=[sub({(tv,):1},T),add(delta,{tuple(sorted((tv,qv))):1})]
   require(all(any(rows[h]in [r,scale(r,-1)]for h in b['rows'])for r in rr),'singleton source rows')
  else:
   kv,lv=b['K_variable'],b['L_variable'];rr=[sub(sub({(kv,):1},scale(H,2)),mul(sub(scale(A,2),base),{(lv,):1})),add(sub(S,mul(base,{(kv,):1})),{(lv,):1})]
   equal([rows[h]for h in b['rows']],rr,'pooled source rows')
  deleted.update(b['rows']);private.update(b['private']);blocks.append((T,E))
 require(private==set(c['removed_variables']),'private partition');require(deleted==set(c['removed_rows']),'row partition');require(len(private)==(9 if fused else 8)and len(deleted)==(9 if fused else 8),'private count')
 for i,row in enumerate(rows):
  if i not in deleted:require(not any(set(m)&private for m in row),'private occurrence outside deleted rows')
 proxy=poly(c['orientation_proxy'])if 'orientation_proxy'in c else omega
 adjustment=add(*[scale(rows[i],k)for i,k in c.get('orientation_proxy_adjustments',[])])
 require(all(type(k)is int and i not in deleted for i,k in c.get('orientation_proxy_adjustments',[])),'proxy retained integer row combination')
 equal(sub(proxy,omega),adjustment,'exact orientation proxy identity')
 kept=[i for i in range(len(source['variables']))if i not in private];require(kept==c['retained_original_indices'],'retained coordinate order');ren={old:new for new,old in enumerate(kept)}
 raw=[rows[i]for i in range(len(rows))if i not in deleted]
 for g,ids in enumerate(c['partition']):
  z=len(source['variables'])+g;ren[z]=len(kept)+g;den=prod([blocks[i][0]for i in ids]);summ={}
  for i in ids:summ=add(summ,mul(blocks[i][1],prod([blocks[j][0]for j in ids if j!=i])))
  residual=sub(summ,mul({(z,):1},den))
  if g==c['fused_group']:residual=add(mul(proxy,den),mul(D,residual))
  raw.append(residual)
 def remap(p):return {tuple(sorted(ren[i]for i in m)):v for m,v in p.items()}
 equal([poly(r['terms'])for r in eq['residuals']],[remap(p)for p in raw],'all emitted residuals')
 require(len(eq['variables'])==len(kept)+len(c['partition']),'dimension')
 return {'path':str(folder.name),'source_sha256':c['source_sha256'],'equation_sha256':hashlib.sha256((folder/'equation.json').read_bytes()).hexdigest(),'variables':len(eq['variables']),'rows':len(raw),'degree':2*max(len(m)for row in raw for m in row),'literal_residual_terms':sum(len(r)for r in raw),'pairs':len(pairs),'requests':requests,'source_rows_and_exact_emitted_residuals_pass':True}
if __name__=='__main__':
 source=R/'source/pell209_affine.json'
 result=[check_seed(source,R/'seeds'/n)for n in ['joint_13_frame','plain_13','plain_22']]
 receipt={'method':'Independent sparse-polynomial implementation; imports no producer or its arithmetic','results':result}
 print(json.dumps(receipt,indent=2))
