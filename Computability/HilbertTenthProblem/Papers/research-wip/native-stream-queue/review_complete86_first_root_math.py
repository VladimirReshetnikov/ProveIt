#!/usr/bin/env python3
"""Independent bounded coordinate/sign audit. Reads frozen source; executes none."""
import argparse,hashlib,json,math
from collections import Counter
from pathlib import Path
PINS={'author_source':'29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f',
 'author_receipt':'2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e',
 'parent_source':'a87578023ae99433519555a3d1f566c853a4b6a8323ab566a72fc9108acb6660',
 'parent_receipt':'47a059a8871c101466d7d0440cf39c5dda4ddffd55fcc8d8ac118874aedbac98'}
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong','norm_linear']
def need(v,s):
 if not v:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 return type(a)is type(b) and (a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a) if type(a)is dict else len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b)) if type(a)is list else a==b)
def plus(a,b,c=1):
 r=dict(a)
 for m,v in b.items():r[m]=r.get(m,0)+c*v
 return {m:v for m,v in r.items() if v}
def times(a,b):
 r={}
 for x,v in a.items():
  for y,w in b.items():
   m=tuple(sorted(x+y));r[m]=r.get(m,0)+v*w
 return {m:v for m,v in r.items() if v}
def var(x):return {(x,):1}
def const(x):return {():x} if x else {}
def execute(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a] if type(a)is str else a;b=e[b] if type(b)is str else b
  e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e
def tree(rows):
 e={}
 for n,o,a,b in rows:
  if n=='norm_first':e[n]=('proved_coordinate_identity',);continue
  e[n]=(o,e.get(a,('free',a)) if type(a)is str else ('int',a),e.get(b,('free',b)) if type(b)is str else ('int',b))
 return e

def run(source,receipt,root):
 paths={'author_source':Path(source),'author_receipt':Path(receipt),'parent_source':root/'complete75_asymmetric_scale_tradeoffs.py','parent_receipt':root/'complete75_asymmetric_scale_tradeoffs.json'}
 for k,p in paths.items():need(sha(p.read_bytes())==PINS[k],'Frozen '+k)
 parent=json.loads(paths['parent_receipt'].read_text())['source'];child=json.loads(paths['author_receipt'].read_text())['forms']
 need([p['normalized'] for p in parent]==[True,False] and [p['normalized'] for p in child]==[True,False],'Two modes')
 # A separate tiny sparse coefficient ring proves the identity, not floating tests.
 L,k,g,T,A=map(var,('L','k','g','T','other_factor_product'))
 old=plus(times(g,g),times(L,plus(times(const(2),g),k,-1)))
 def new(t):return plus(times(t,t),times(L,plus(L,k)),-1)
 need(new(plus(L,g))==old,'Forward exact coefficients')
 inverse=plus(T,L,-1)
 pulled=plus(times(inverse,inverse),times(L,plus(times(const(2),inverse),k,-1)))
 need(pulled==new(T),'Inverse exact coefficients')
 need(plus(times(new(plus(L,g)),A),const(1),-1)==plus(times(old,A),const(1),-1),'Whole product-minus-one coefficient identity')
 records=[];count=Counter(symbolic_local_identities=2,symbolic_whole_product_identity=1)
 for pp,cc in zip(parent,child):
  rows=pp['source'];got=cc['source'];norm=pp['normalized'];expected=[]
  for n,o,a,b in rows:
   if n=='tau_square':expected.append([n,'*','tau_root','tau_root'])
   elif n=='norm_first':expected += [['first_next','+','first_root_base','R10b'],['first_product','*','first_root_base','first_next'],['norm_first','-','tau_square','first_product']]
   elif n not in ('twice_tau_gap','first_signed_gap','first_cross'):expected.append([n,o,a,b])
  need(exact(expected,got),'Entire expected source rewrite')
  need({n for n,_,a,b in rows if 'tau_gap' in (a,b)}=={'tau_square','twice_tau_gap'},'Old root privacy')
  nodes={n:(o,a,b) for n,o,a,b in got}
  required={'R10b':('+','eta','zeta'),'wn2':('*','w','q'),'sn2':('*','s','n2'),'n2':('*','Lbig','q'),'Lbig':('*','q','q'),'UM':('*','wn2','sn2'),'ksn2':('*','R10b','sn2'),'first_root_base':('*','UM','ksn2'),'q':('+','repunit',1),'repunit':('*','Bm1','Jrep')}
  need(all(nodes[n]==v for n,v in required.items()),'Unconditional positive L,k producers')
  # Expand only L after cutting q; obtains w*s²*q^7*(eta+zeta).
  env={'q':var('q')}
  for n in ('Lbig','n2','wn2','sn2','UM','R10b','ksn2','first_root_base'):
   op,a,b=nodes[n];aa=env.get(a,var(a));bb=env.get(b,var(b));env[n]=times(aa,bb) if op=='*' else plus(aa,bb)
  target={tuple(sorted(['w','s','s']+['q']*7+['eta'])):1,tuple(sorted(['w','s','s']+['q']*7+['zeta'])):1}
  need(env['first_root_base']==target,'Literal exact L=w*s²*q^7*k')
  aa,bb=tree(rows),tree(got)
  for f in FACTORS+['polynomial']:need(aa[f]==bb[f],'All factors/finalizer preserved after proved local cut');count['full_factor_finalizer_DAG_identities']+=1
  co=Counter(o for _,o,_,_ in got);need((len(got),co['*'],co['+']+co['-'])==((86,48,38) if norm else (87,47,40)),'Whole paid count')
  need(got[-1]==['polynomial','-','eight_units',1] and len(cc['witnesses'])==19 and 'tau_root'in cc['witnesses'] and 'tau_gap'not in cc['witnesses'],'Same full interface')
  vals={n:1 for n in cc['witnesses']+['x']};vals.update(Bm1=15,Kconstant=83,twice_cell_bits=8,inner_bits=3,MC=14,MF=4)
  e=execute(got,vals);gap=vals['tau_root']-e['first_root_base'];need(gap<0 and e['polynomial']!=0,'Whole positive orthant inverse fails only offzero here')
  records.append(dict(normalized=norm,M=co['*'],A=co['+']+co['-'],operations=len(got),witnesses=19,root_base_exact_degree=11,first_factor_exact_degree=22,complete_degree_from_retained_factor_proof=179 if norm else 135,positive_offzero_restored_gap=gap))
 # This is an exhaustive bounded local UNIT census, not full universal zeros.
 signs=Counter();examples=[]
 for l in range(1,257):
  for kk in range(2,129):
   for eps in (-1,1):
    rad=l*l+l*kk+eps;t=math.isqrt(rad);count['local_unit_radicals_tested']+=1
    if t*t!=rad:continue
    need(t>l and t-l>=1 and (t-l)**2+l*(2*(t-l)-kk)==eps,'Unit forces positive restoration')
    signs[str(eps)]+=1
    if len(examples)<12:examples.append(dict(L=l,k=kk,T=t,sign=eps,g=t-l))
 need(set(signs)=={'-1','1'},'Both signs witnessed')
 # Sharp omitted hypotheses, only scalar-factor boundaries.
 need(1*1-1*(1+1)==-1 and 1-1==0,'Lk=1 boundary')
 need((-4)**2-3*(3+2)==1 and -4-3<0,'Positive root required')
 return dict(status='PASS',pins=PINS,scope='Independent mathematical/circuit-coordinate audit; no historical module execution, no complete universal Pell zero, degree upper/lower proof inherited for seven unchanged factors',counts=dict(count),local_unit_sign_counts=dict(signs),local_unit_examples=examples,forms=records,boundaries={'Lk_equal_one':{'L':1,'k':1,'T':1,'first_factor':-1,'restored_g':0},'signed_root':{'L':3,'k':2,'T':-4,'first_factor':1,'restored_g':-7}})
def main():
 a=argparse.ArgumentParser();a.add_argument('--source',type=Path,required=True);a.add_argument('--receipt',type=Path,required=True);a.add_argument('--root',type=Path,required=True);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);v=a.parse_args();o=run(v.source,v.receipt,v.root)
 if v.expect:need(exact(o,json.loads(v.expect.read_text())),'Exact saved receipt')
 if v.output:v.output.write_text(json.dumps(o,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':o['status'],'counts':o['counts'],'forms':o['forms']},sort_keys=True))
if __name__=='__main__':main()
