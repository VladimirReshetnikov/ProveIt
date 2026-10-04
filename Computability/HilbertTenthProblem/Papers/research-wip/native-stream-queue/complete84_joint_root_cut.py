#!/usr/bin/env python3
"""Fresh bounded two-output root-cut check, reading frozen JSON only."""
import argparse,collections,fractions,hashlib,json,pathlib,random
PINS={'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737','complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf','complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade'}
def need(b,m):
 if not b:raise ValueError(m)
def nodup(ps):
 d={}
 for k,v in ps:need(k not in d,'duplicate key');d[k]=v
 return d
def parse(b):return json.loads(b,object_pairs_hook=nodup)
def poly(x):return {():x}if type(x)is int else{(x,):1}
def add(a,b,s=1):
 d=a.copy()
 for m,c in b.items():d[m]=d.get(m,0)+s*c
 return {m:c for m,c in d.items()if c}
def mul(a,b):
 d={}
 for m,c in a.items():
  for n,e in b.items():k=tuple(sorted(m+n));d[k]=d.get(k,0)+c*e
 return {m:c for m,c in d.items()if c}
def cut(rows):
 leaves=['R12','R10a','wn2','a4m5','index_rhs','W','rho','sigma'];v={x:poly(x)for x in leaves}
 for n,op,a,b in rows:
  need(a in v and b in v,'cut dependency');v[n]=mul(v[a],v[b])if op=='*'else add(v[a],v[b],1 if op=='+'else-1)
 return v
ROOTNAMES=['cam2','D1','gamma_sum','gam','R14','difference_multiple','exponent_partial','modulus_multiple','exponent_rhs']
def topo(rows,free):
 by={r[0]:r for r in rows};need(len(by)==len(rows),'duplicate row');known=set(free);order=[];busy=set()
 def visit(n):
  if type(n)is int or n in known:return
  need(n in by and n not in busy,'unknown/cyclic');busy.add(n);r=by[n];visit(r[2]);visit(r[3]);busy.remove(n);known.add(n);order.append(r)
 visit('polynomial');need(len(order)==len(rows),'dead row')
 return order
def evaluate(rows,assignment):
 v=dict(assignment)
 def get(x):return x if type(x)is int else v[x]
 for n,op,a,b in rows:
  aa,bb=get(a),get(b);v[n]=aa*bb if op=='*'else aa+bb if op=='+'else aa-bb
 return v
p=argparse.ArgumentParser();p.add_argument('--root',type=pathlib.Path,required=True);p.add_argument('--output',type=pathlib.Path,required=True);args=p.parse_args()
for n,h in PINS.items():need(hashlib.sha256((args.root/n).read_bytes()).hexdigest()==h,n)
parent=parse((args.root/'complete84_scaled_strong_output.json').read_bytes())['packet'];old=parent['source'];oldcut=[r for r in old if r[0]in ROOTNAMES]
newcut=[['cam2','*','R10a','R12'],['D1','+','wn2','cam2'],['modulus_multiple','*','rho','a4m5'],['sigma_multiple','*','sigma','a4m5'],['root_shared_partial','+','D1','modulus_multiple'],['R14','+','root_shared_partial','sigma_multiple'],['difference_multiple','*','index_rhs','R12'],['exponent_partial','+','W','difference_multiple'],['exponent_rhs','+','exponent_partial','modulus_multiple']]
u,v=cut(oldcut),cut(newcut)
for n in ['R14','exponent_rhs']:need(u[n]==v[n],'formal root identity')
changed=topo([r for r in old if r[0]not in ROOTNAMES]+newcut,parent['free']);need(len(changed)==84,'fullcount');counts=collections.Counter(r[1]for r in changed);need(counts['*']==47 and counts['+']+counts['-']==37,'wholeledger')
# Exact expression interning: the two proved root values are cut labels; all other retained rows compare literally through these labels.
common_names=set(r[0]for r in old)&set(r[0]for r in changed);intern={};ids={}
def signatures(rows):
 out={x:('free',x)for x in parent['free']}
 def expr(x):return ('int',x)if type(x)is int else out[x]
 for n,op,a,b in rows:
  if n in ('R14','exponent_rhs'):out[n]=('proved_joint_cut',n)
  else:
   key=(op,expr(a),expr(b));out[n]=intern.setdefault(key,len(intern))
 return out
s0=signatures(topo(old,parent['free']));s1=signatures(changed)
for n in parent['factors']+['polynomial']:need(s0[n]==s1[n],'whole-source cut identity')
# Independent mixed-coefficient flattening, columns c,kappa,rho,sigma.
flat=[[1,0,0,0],[0,1,0,0],[0,0,1,1],[0,0,1,0]];mat=[[fractions.Fraction(x)for x in row]for row in flat];rank=0
for col in range(4):
 piv=next((j for j in range(rank,4)if mat[j][col]),None)
 if piv is None:continue
 mat[rank],mat[piv]=mat[piv],mat[rank];factor=mat[rank][col];mat[rank]=[x/factor for x in mat[rank]]
 for j in range(4):
  if j!=rank:
   fact=mat[j][col];mat[j]=[x-fact*y for x,y in zip(mat[j],mat[rank])]
 rank+=1
need(rank==4,'bilinear rank')
# No two binary additions/subtractions of four raw monomials produce both core roots.
base=[(0,0,0,0)]+[tuple(int(i==j)for i in range(4))for j in range(4)];targets={(1,0,1,1),(0,1,1,0)};trials=0;hits=0
for a in base:
 for b in base:
  for sign in (1,-1):
   t=tuple(x+sign*y for x,y in zip(a,b));available=base+[t]
   for c in available:
    for d in available:
     for sg in (1,-1):
      z=tuple(x+sg*y for x,y in zip(c,d));trials+=1
      hits+=targets.issubset(set(available+[z]))
need(hits==0,'two-add postprocessor')
rng=random.Random(841903);numeric=0
for case in range(64):
 assignment={x:fractions.Fraction(rng.randrange(-4,5),rng.randrange(1,4) if case>=32 else 1)for x in parent['free']}
 a=evaluate(old,assignment);b=evaluate(changed,assignment)
 for n in parent['factors']+['polynomial','R14','exponent_rhs']:need(a[n]==b[n],'whole rational identity')
 numeric+=1
# A distinct first/main overlap uses the paid U=E*(kY), but needs two extra terms.
firstmain_extra=[['firstmain_E_eta','*','UM','eta'],['firstmain_Y_c','*','sn2','R10a'],['firstmain_partial','+','first_root_base','firstmain_E_eta'],['cam2','+','firstmain_partial','firstmain_Y_c']]
firstmain=topo([r for r in old if r[0]!='cam2']+firstmain_extra,parent['free'])
fc=collections.Counter(r[1]for r in firstmain);need(len(firstmain)==87 and fc['*']==48 and fc['+']+fc['-']==39,'first/main ledger')
by={r[0]:r for r in old}
for row in [['R12','+','UM','sn2'],['R10a','+','ksn2','eta'],['first_root_base','*','UM','ksn2'],['cam2','*','R10a','R12']]:need(by[row[0]]==row,'first/main defining row')
E,Y,KY,eta=[poly(x)for x in ('E','Y','KY','eta')]
c=add(KY,eta);a=add(E,Y)
need(mul(a,c)==add(add(mul(E,KY),mul(E,eta)),mul(Y,c)),'first/main expansion')
firstmain_numeric=0
for case in range(16):
 assignment={x:fractions.Fraction(rng.randrange(-3,4),1 if case<8 else rng.randrange(1,4))for x in parent['free']}
 aa=evaluate(old,assignment);bb=evaluate(firstmain,assignment)
 for n in parent['factors']+['polynomial','cam2']:need(aa[n]==bb[n],'first/main whole identity')
 firstmain_numeric+=1
out={'status':'BOUNDED_JOINT_ROOT_NO_SAVING','pins':PINS,'parent_packet':parent,'alternate_source':changed,'alternate_ledger':{'M':47,'A':37,'total':84},'root_cut':{'inputs':['a','H','c','kappa','rho','sigma','X','W'],'parent_rows':oldcut,'alternate_rows':newcut,'both_cost':'4M+5A','identical_outputs':['R14','exponent_rhs']},'first_main_overlap':{'identity':'a*c=U+E*eta+Y*c where a=E+Y,c=kY+eta,U=E*kY','source':firstmain,'ledger':{'M':48,'A':39,'total':87},'supplementary_complete_signed_rational_fixtures':firstmain_numeric},'bilinear_core_flattening':flat,'bilinear_rank':rank,'two_add_sub_postprocessor_trials':trials,'successful_two_add_sub_postprocessors':hits,'complete_signed_rational_fixtures':numeric,'rational_fixtures':32,'scope':'The9-gate lower bound is only for separated homogeneous bilinear algorithms at independent a,H cuts with two final offset attachments. No claim for actual H=4a+3 recombination, nonlinear multiplications/cancellations, simultaneous norm replacement, or new positive coordinates.'}
args.output.write_text(json.dumps(out,indent=2)+'\n');print(out['status'],len(changed),rank,trials)
