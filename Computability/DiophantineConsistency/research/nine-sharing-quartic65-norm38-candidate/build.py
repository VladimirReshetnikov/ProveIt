#!/usr/bin/env python3
"""Generate a quartic candidate for the five unit-norm conditions of Carrier65."""
import json,hashlib,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];src=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';raw=src.read_bytes();assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(raw);assert len(g['source'])==65 and len(g['witnesses'])==14 and g['fixed_numerals']==['beta','K0','MC','MF']
N=lambda x:['num',x];V=lambda i:['var',i];Z=N(0)
def add(a,b):return b if a==Z else a if b==Z else ['add',a,b]
def sub(a,b):return a if b==Z else ['sub',a,b]
def mul(a,b):return Z if a==Z or b==Z else b if a==N(1) else a if b==N(1) else ['mul',a,b]
def degree(t):
 if t[0] in ('num','port'):return 0
 if t[0]=='var':return 1
 a,b=map(degree,t[1:]);return a+b if t[0]=='mul' else max(a,b)
pairs={n:(add(V(i+1),N(1)),Z) for i,n in enumerate(g['witnesses'])};pairs.update({n:(['port',n],Z) for n in g['fixed_numerals']});get=lambda x:(N(x),Z) if type(x)==int else pairs[x];nextvar=15;records=[];residuals=[]
def parts(op,a,b):
 ap,an=a;bp,bn=b
 if op=='+':return add(ap,bp),add(an,bn)
 if op=='-':return add(ap,bn),add(an,bp)
 assert op=='*';return add(mul(ap,bp),mul(an,bn)),add(mul(ap,bn),mul(an,bp))
cuts={'Dc2','Delta','E','V','V2minusY2','X','Y','c2','cTminusR','ell','f2','gap','kY','main_root','normalized_S','normalized_S2','q2','q3','tau'}
terminal={'N0','N1','Nt','Na','scaled_Ns'}
for name,op,a,b in g['source'][:60]:
 assert name not in pairs and op in ('+','-','*');ep,en=parts(op,get(a),get(b));deg=max(degree(ep),degree(en));assert deg<=2;record={'name':name,'op':op,'left':a,'right':b,'pair_degree':deg}
 if name in terminal:
  target=get('Delta') if name=='scaled_Ns' else (N(1),Z)
  lhs=sub(ep,en);rhs=sub(*target);e=sub(lhs,rhs);assert degree(e)<=2
  record['kind']='norm';record['target']='Delta' if name=='scaled_Ns' else 1;residuals.append({'kind':'norm','gate':name,'target':record['target'],'expr':e});pairs[name]=(ep,en);records.append(record);continue
 if name not in cuts:record['kind']='inline';pairs[name]=(ep,en)
 else:
  record['kind']='materialized';v=V(nextvar);nextvar+=1;record['positive_coordinate']=v[1];residuals.append({'kind':'positive','gate':name,'expr':sub(v,ep)})
  if en==Z:pairs[name]=(v,Z)
  else:
   w=V(nextvar);nextvar+=1;record['negative_coordinate']=w[1];residuals.append({'kind':'negative','gate':name,'expr':sub(w,en)});pairs[name]=(v,w)
 records.append(record)
assert nextvar==39 and len(residuals)==29 and sum(r['kind']=='inline' for r in records)==36 and sum(r['kind']=='materialized' for r in records)==19 and sum(r['kind']=='norm' for r in records)==5
assert records[2]['name']=='q2' and records[2]['positive_coordinate']==15
out={'schema':'sharing-quartic-five-unit-norms-v1','source_graph':'../../candidates/one-page-padding-staircase-carrier65-2011/polynomial.json','source_graph_sha256':hashlib.sha256(raw).hexdigest(),'fixed_ports':g['fixed_numerals'],'coefficient_binding':g['coefficient_binding'],'input_coordinate':0,'domain':'coordinates 1..38 range over natural numbers; distinguished input coordinate arbitrary','original_coordinates':{n:i+1 for i,n in enumerate(g['witnesses'])},'positive_shift':1,'normalization_witness':'first q2 residual evaluates to -(beta+1)^2 at zero witnesses','coordinate_count':nextvar,'jones_witness_count':nextvar-1,'gate_records':records,'residuals':residuals,'norm_targets':{'N0':1,'N1':1,'Na':1,'Nt':1,'scaled_Ns':'Delta'},'omitted_graph_rows':g['source'][60:],'output':'sum of squares of every residual','status':'external candidate; norm bridge, Lean model proof and Jones/iPRA endpoint unchecked'}
assert not (P/'seed.json').exists();(P/'seed.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
