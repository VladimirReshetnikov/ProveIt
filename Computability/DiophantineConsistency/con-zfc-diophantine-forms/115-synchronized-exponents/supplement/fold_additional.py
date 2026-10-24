#!/usr/bin/env python3
from fold_transport import ROOT, OUT, require, Poly, variables, metrics, evaluate
from pathlib import Path
import json, hashlib, random

def sq(a):return a*a

def norm(s,a,b,c):
 p=s+c-a-b; sc=s*c; ab=a*b;e=sq(p)-4*(sc+ab)
 return sq(e)-64*sc*ab

def standard_tail(fs,fa,fb,fc,out):
 return [
 ['fold_sumsc','+',fs,fc],['fold_sumab','+',fa,fb],['fold_difference','-','fold_sumsc','fold_sumab'],
 ['fold_sc','*',fs,fc],['fold_ab','*',fa,fb],['fold_sumprod','+','fold_sc','fold_ab'],
 ['fold_4sumprod','*',4,'fold_sumprod'],['fold_difference2','*','fold_difference','fold_difference'],
 ['fold_e','-','fold_difference2','fold_4sumprod'],['fold_e2','*','fold_e','fold_e'],
 ['fold_scab','*','fold_sc','fold_ab'],['fold_64scab','*',64,'fold_scab'],[out,'-','fold_e2','fold_64scab']]

def check_parent_child(old,new,path,name,diff):
 new['name']=name;new.update(metrics(new));require(new['operations']==old['operations']-diff,'gate count'+name)
 raw=path.read_bytes();new['parent_sha256']=hashlib.sha256(raw).hexdigest();new.pop('register_degrees',None)
 new.pop('system_operations',None)
 new['coefficient_binding']='../coefficients/BINDING.json'
 new['proof']='../REPORT_SECTION.tex'
 new['status']='Same polynomial as pinned parent by universal ring identities. Degree/zeros transfer pointwise.'
 rng=random.Random(49954)
 for prime in (1009,10007,1000003):
  for i in range(128):
   vals={x:rng.randrange(-prime,prime)for x in old['witnesses']+old['fixed_numerals']}
   require(evaluate(old,vals,prime)==evaluate(new,vals,prime),'signed full output control')
 target=OUT/(name+'.json');target.write_text(json.dumps(new,indent=2)+'\n')
 return {'name':name,'source':str(path.relative_to(ROOT)),'parent_sha256':hashlib.sha256(raw).hexdigest(),'child_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'metrics':metrics(new),'exact_degree':old['exact_degree'],'supplementary_evaluations':384}

def main():
 receipts=[]
 # Direct ten-variable carrier: q3*q*(q-1)=P1.
 q,qm,H,n,V,K,mu2,Y,B,e,L,X=variables('q qm H n V K mu2 Y B e L X')
 q3=q*q*q;P1=q3*q*qm
 zold=P1*mu2*(H*(n+V)+K)+H*(mu2*(q*qm*Y-q3*(1+q*qm*L)*B-qm*X)-P1*e)
 znew=P1*mu2*(H*(n+V-L*B)+K)+H*(mu2*(qm*(q*Y-X)-q3*B)-P1*e)
 require(not(zold-znew).terms,'complete direct center identity')
 path=ROOT/'candidates/ten-positive-direct-zero-offset/equation.json';old=json.loads(path.read_bytes());new=dict(old);rows=[]
 for n,op,a,b in old['source']:
  if n in ('qbJ','qm1L','W','WBt','q3WBt','lowY','lowX','inner0'):continue
  if n=='nV':
   rows.extend([['fold_LB','*','L','B'],[n,op,a,b],['fold_nV','-','nV','fold_LB']]);continue
  if n=='Hn':rows.append([n,op,'Hp','fold_nV']);continue
  if n=='inner':
   rows.extend([['fold_qY','*','q','Y'],['fold_qYmX','-','fold_qY','X'],['fold_low','*','bJ','fold_qYmX'],['fold_q3B','*','q3','B'],['inner','-','fold_low','fold_q3B']]);continue
  rows.append([n,op,a,b])
 new['source']=rows;receipts.append(check_parent_child(old,new,path,'positive10_direct103_degree340',2))
 # The existing centered 18-gate norm equals the scaled standard norm (16 gates).
 z,A,B,C,d=variables('z A B C d')
 J=d*(z-A-B)-C;T=A*B*d*d;R=C*d
 original=sq(sq(J)-4*(T+(A+B)*R))-64*T*R*z
 require(not(original-norm(d*z,d*A,d*B,C)).terms,'full generic norm identity')
 # Carrier contraction identical to ordinary form with g58 as center variable.
 p,qm,centre,Y,B,L=variables('p qm centre Y B L')
 oldc=p*qm*centre+qm*Y-p*(1+qm*L)*B
 newc=p*qm*(centre-L*B)+qm*Y-p*B
 require(not(oldc-newc).terms,'eleven-positive center identity')
 path=ROOT/'candidates/positive11-adaptive-shears/positive11.json';old=json.loads(path.read_bytes());new=dict(old);rows=[]
 oldnames=[r[0]for r in old['source']];start=oldnames.index('ABsum');end=oldnames.index('N8')
 for idx,(n,op,a,b) in enumerate(old['source']):
  if n in ('g53','W','g62','g63','S'):continue
  if n=='g59':
   rows.extend([['fold_LBt','*','L','Bt'],['fold_g58','-','g58','fold_LBt'],['g59','*','M','fold_g58']]);continue
  if n=='Zbar':
   rows.extend([['fold_q3Bt','*','q3','Bt'],['Zbar','-','g61','fold_q3Bt']]);continue
  if n=='U':rows.append(['U','*','Y','q2']);continue
  if n=='g71':rows.append(['g71','*','E','q']);continue
  if idx==start:
   rows.extend([['fold_fs','*','delta','z2'],['fold_fa','*','delta','A'],['fold_fb','*','delta','Bf']]);rows.extend(standard_tail('fold_fs','fold_fa','fold_fb','Cnum','N8'));continue
  if start<idx<=end:continue
  rows.append([n,op,a,b])
 new['source']=rows;receipts.append(check_parent_child(old,new,path,'positive11_107_degree211',4))
 (OUT/'ADDITIONAL_CHECK.json').write_text(json.dumps({'universal_ring_identities':'PASS','receipts':receipts},indent=2)+'\n')
 print(json.dumps(receipts,indent=2))
if __name__=='__main__':main()
