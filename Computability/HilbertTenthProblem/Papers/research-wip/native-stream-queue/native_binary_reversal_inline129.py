#!/usr/bin/env python3
"""New output/scale substitutions; predecessor JSON is read only as data."""
import argparse,hashlib,json
from pathlib import Path
DEFAULT=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
def require(p,message):
 if not p:raise ValueError(message)
def digest(data):return hashlib.sha256(data).hexdigest()
def pairs(xs):
 d={}
 for k,v in xs:require(k not in d,'duplicate JSON key');d[k]=v
 return d
def parsed(path):return json.loads(path.read_text(),object_pairs_hook=pairs)
def add(p,q,sgn=1):
 r=dict(p)
 for k,c in q.items():r[k]=r.get(k,0)+sgn*c
 return {k:c for k,c in r.items() if c}
def times(p,q):
 r={}
 for a,c in p.items():
  for b,d in q.items():k=tuple(sorted(a+b));r[k]=r.get(k,0)+c*d
 return {k:c for k,c in r.items() if c}
def evaluate(rows,inputs,formal=False):
 env=dict(inputs)
 def value(x):return ({():x} if x else {}) if formal and type(x)is int else x if type(x)is int else env[x]
 for name,op,a,b in rows:
  x,y=value(a),value(b)
  env[name]=(times(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)) if formal else x*y if op=='*' else x+y if op=='+' else x-y
 return env

def build(parent,inline_scale):
 rows=[list(r) for r in parent['source']];eq=[list(r) for r in parent['comparisons']];aux=list(parent['positive_witnesses']);params=list(parent['parameters_positive'])
 require(rows[17]==['congruence_right','+','scaled_reverse_sum',1] and eq[3]==['Ahat','congruence_right'],'original output comparison')
 rows.pop(17);eq.pop(3);aux.remove('Ahat')
 edited=0
 for r in rows:
  if r[0]=='and__scaled_Z':require(r==['and__scaled_Z','*',16,'Ahat'],'output scaling');r[3]='scaled_reverse_sum';edited+=1
  if r[0]=='and__F3':require(r==['and__F3','-','and__scaled_Z',8],'output padding');r[1]='+';edited+=1
 require(edited==2,'both output rows')
 if inline_scale:
  require(eq[0]==['repunit_P','P'],'original P comparison');eq.pop(0);aux.remove('P')
  # Replace all uses of P by its positive definition, then topologically emit.
  for r in rows:
   for i in [2,3]:
    if r[i]=='P':r[i]='repunit_P'
  ordered=[];available=set(params+aux)
  while rows:
   for i,row in enumerate(rows):
    if all(type(v)is int or v in available for v in row[2:]):ordered.append(row);available.add(row[0]);rows.pop(i);break
   else:raise ValueError('cyclic substitution')
  rows=ordered
 full=[list(r) for r in rows]
 for i,(a,b) in enumerate(eq):full.append([f'new_residual_{i}','-',a,b])
 for i in range(len(eq)):full.append([f'new_square_{i}','*',f'new_residual_{i}',f'new_residual_{i}'])
 output='new_square_0'
 for i in range(1,len(eq)):
  full.append([f'new_sum_{i}','+',output,f'new_square_{i}']);output=f'new_sum_{i}'
 def audit(rs,outs):
  available=set(params+aux);graph={}
  for name,op,a,b in rs:
   require(name not in available and op in '+-*','producer');require(all(type(v)is int or v in available for v in [a,b]),'topology');available.add(name);graph[name]=[a,b]
  live=set();todo=list(outs)
  while todo:
   v=todo.pop()
   if type(v)is int or v in live:continue
   live.add(v);todo+=graph.get(v,[])
  require(set(graph)|set(params+aux)<=live,'all rows and ports live')
  m=sum(r[1]=='*' for r in rs);return {'M':m,'A':len(rs)-m,'total':len(rs)}
 co=audit(rows,[v for e in eq for v in e]);po=audit(full,[output]);require(co=={'M':66,'A':63,'total':129},'producer cost')
 require(po==({'M':98,'A':126,'total':224} if inline_scale else {'M':99,'A':128,'total':227}),'polynomial cost')
 formal={v:{(v,):1} for v in params+aux};e=evaluate(full,formal,True);poly=e[output];degree=max(map(len,poly));lead={m:c for m,c in poly.items() if len(m)==degree}
 exps={'and__w':4,'and__s':8,'and__k':4,'q':24 if inline_scale else 12,'J' if inline_scale else 'P':12};mon=tuple(sorted(v for v,k in exps.items() for _ in range(k)));coefficient=2**(60 if inline_scale else 48)
 require(degree==(52 if inline_scale else 40) and lead=={mon:coefficient},'exact entire leading form')
 return {'parameters_positive':params,'positive_witnesses':aux,'source':rows,'comparisons':eq,'full_source':full,'output':output,'producer_cost':co,'polynomial_cost':po,'witnesses':len(aux),'equations':len(eq),'degree':degree,'polynomial_terms':len(poly),'leading_coefficient':coefficient,'leading_monomial':exps,'all_rows_and_ports_live':True,'inline_scale':inline_scale}

def outer_checks(cert):
 count=0
 for n in range(2,11):
  q=2**n;B=2*q;P=B**n;J=sum(B**i for i in range(n));K=sum((2*B)**i for i in range(n))
  for x in range(1,q):
   z=int(format(x,f'0{n}b')[::-1],2);selected=(2*x*K)&(q*J);require(selected%q==0,'selection divisible by q');R=selected//q;qh=(R-z)//(q-1)+1
   vals=dict(x=x,q=q,z=z,P=P,J=J,K=K,quotient_hat=qh,input_slack=q-x,output_slack=q-z)
   if cert['inline_scale']:vals.pop('P')
   # Only the fresh outer rows are evaluated; no old helper/source is run.
   outer=[r for r in cert['source'] if not r[0].startswith(('geo__','and__'))];e=evaluate(outer,vals)
   require(e['scaled_reverse_sum']==selected,'restored selected output');require(all(v>0 for v in vals.values()),'positive outer tuple')
   require(16*e['scaled_reverse_sum']+8==16*(selected+1)-8,'exact output substitution')
   if cert['inline_scale']:require(e['repunit_P']==P and e['scale']==q*P,'positive scale substitution')
   count+=1
 return {'outer_words_n2_through10':count,'full_native_Pell_zeros_materialized':0}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=DEFAULT);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args()
 path=a.root/'native_binary_reversal130.json';raw=path.read_bytes();old=parsed(path);parent=old['certificate'];variants={}
 for mode in [False,True]:
  c=build(parent,mode);c['fresh_outer_checks']=outer_checks(c);variants['inline_output_and_scale' if mode else 'inline_output']=c
 d={'status':'PASS_REVERSAL_INLINE129','source_sha256':digest(Path(__file__).read_bytes()),'parent_json':{'name':path.name,'bytes':len(raw),'sha256':digest(raw)},'variants':variants,'scope':'Fixed arity padded positive binary reversal only; unique positive output/scale substitutions. No frozen helper executed/imported; no universal saving; no full Pell zero tuples.'}
 if a.output:
  with a.output.open('x') as f:json.dump(d,f,sort_keys=True,indent=2);f.write('\n')
 else:require((json.dumps(d,sort_keys=True,indent=2)+'\n').encode()==a.expect.read_bytes(),'exact receipt')
 print(json.dumps({k:{x:v[x] for x in ['producer_cost','polynomial_cost','witnesses','equations','degree','polynomial_terms']} for k,v in variants.items()}))
if __name__=='__main__':main()
