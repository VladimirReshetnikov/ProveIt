#!/usr/bin/env python3
"""Independent complete geometry delta expansion; no subject module execution."""
import argparse,hashlib,json
from collections import Counter
from pathlib import Path
import sympy as S
PINS={'group_linked_binary_geometry46.py':'c7f6f774a8a8088deacd77f687068fae79c0173676d6b3566e6cc740e0e27944',
'group_linked_binary_geometry46.json':'0e6f0991291c1ff5c4fd51880a2c46551d7f2d90024f0bcfda2a2d2c287ed759',
'group_linked_binary_geometry46.md':'8bb3856e55872c2072e4e3d951c41df9ffe6fb80837d622509a0d0d476781db4'}
def need(x,m):
 if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def sos(source,pairs):
 rows=list(source);out=None
 for i,(a,b) in enumerate(pairs):
  r=f'geometry_residual_{i}';q=f'geometry_square_{i}';rows.extend([[r,'-',a,b],[q,'*',r,r]])
  if out is None:out=q
  else:n=f'geometry_sum_{i}';rows.append([n,'+',out,q]);out=n
 return rows,out
def evaluate(rows,ports):
 e={n:S.Symbol(n) for n in ports}
 for n,op,a,b in rows:
  a=S.Integer(a) if type(a)is int else e[a];b=S.Integer(b) if type(b)is int else e[b]
  e[n]=S.expand(a*b if op=='*' else a+b if op=='+' else a-b)
 return e
def ledger(rows,ports,outputs):
 ready=set(ports);defs={};c=Counter()
 for n,op,a,b in rows:
  need(n not in ready and op in ('+','-','*'),'valid fresh gate')
  need(all(type(v)is int or type(v)is str and v in ready for v in (a,b)),'closed exact operands')
  defs[n]=(a,b);ready.add(n);c['M' if op=='*' else 'A']+=1
 live=set();todo=list(outputs)
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  need(n in ready,'valid terminal');live.add(n)
  if n in defs:todo.extend(defs[n])
 need(live==set(ports)|set(defs),'all gates and supplied coordinates live')
 return dict(operations=len(rows),M=c['M'],A=c['A'],all_gates_live=True)
def verify(root,subject):
 for n,h in PINS.items():need(sha(subject/n)==h,'frozen author pin '+n)
 child=json.loads((subject/'group_linked_binary_geometry46.json').read_text())
 for n,h in child['parent_pins'].items():need(sha(root/n)==h,'actual dependency pin '+n)
 old=json.loads((root/'group_linked_binary_geometry47.json').read_text())['source'];forms=[];counts=Counter()
 for parent,record in zip(old,child['forms']):
  p=record['packet'];shared=parent['shared_B'];rows=parent['source'];pairs=parent['comparisons'];ports=parent['parameters']+parent['auxiliaries']
  need(p['shared_B'] is shared and exact(pairs,p['comparisons']) and exact(ports,p['parameters']+p['auxiliaries']),'complete unchanged interface')
  d={n:(op,a,b) for n,op,a,b in rows}
  need(d['UM']==('*','wn2','sn2') and d['ksn2']==('*','k','sn2') and 'k' in parent['auxiliaries'],'actual supplied-k producer cone')
  need(d['R9']==('*','tau','tauplus1') and d['tauplus1']==('+','tau',1),'unchanged native root convention')
  replacement=[['first_root_base','*','UM','ksn2'],['first_next','+','first_root_base','k'],['L9','*','first_root_base','first_next']]
  removed={'UM2','scaled_norm_coefficient','ratio_product2','L9'};expected=[]
  for row in rows:
   if row[0]=='L9':expected.extend(replacement)
   elif row[0] not in removed:expected.append(row)
  need(exact(expected,p['source']),'only declared literal rewrite')
  oldpoly,out=sos(rows,pairs);newpoly,out2=sos(expected,pairs)
  need(out==out2==p['output'] and exact(newpoly,p['polynomial_source']),'entire explicit SOS finalizer')
  a=evaluate(oldpoly,ports);b=evaluate(newpoly,ports);variables=[S.Symbol(n) for n in ports]
  at=lambda e,n:S.Integer(n) if type(n)is int else e[n]
  for left,right in pairs:
   need(at(a,left)==at(b,left) and at(a,right)==at(b,right),'all complete operand polynomials');counts['operand_identities']+=2
  ar=[S.expand(at(a,l)-at(a,r)) for l,r in pairs];br=[S.expand(at(b,l)-at(b,r)) for l,r in pairs]
  need(ar==br and a[out]==b[out] and b[out]==S.expand(sum(v*v for v in br)),'all residuals and complete polynomial identities')
  counts['residual_identities']+=len(br);counts['full_polynomial_identities']+=1
  degrees=[S.Poly(v,*variables).total_degree() for v in br];need(degrees==p['degree_certificate']['exact_residual_degrees'],'actual residual degrees')
  poly=S.Poly(b[out],*variables);degree=poly.total_degree();leaders=[(m,int(c)) for m,c in poly.terms() if sum(m)==degree]
  top=tuple({'w':4,'s':8,'k':4,'q':12}.get(n,0) for n in ports)
  need(degree==28 and leaders==[(top,1)] and len(poly.terms())==141,'unique exact full degree28 leader and whole support')
  serial=[[list(m),int(c)] for m,c in sorted(poly.terms())]
  need(serial==record['exact_degree_expansion']['expanded_SOS_terms'],'complete independently expanded141-term receipt')
  c=ledger(expected,ports,[v for pair in pairs for v in pair]);f=ledger(newpoly,ports,[out])
  need(c==p['certificate_ledger'] and f==p['polynomial_ledger'],'independent complete ledgers')
  o=ledger(rows,ports,[v for pair in pairs for v in pair]);need(c['M']==o['M']-1 and c['A']==o['A'],'exact one multiplication saving')
  if shared:
   need([n for n,op,l,r in rows if 'B' in (l,r)]==['geometry_index_bound'],'sole B dependence')
   q,B,beta=S.symbols('q B index_beta');change={B:8*q*q,beta:beta+B-8*q*q}
   need(all(S.expand(v.subs(change,simultaneous=True)-v)==0 for v in br),'every residual invariant under scale transport')
   counts['symbolic_scale_transport_residuals']+=len(br)
  else:need(rows[:2]==[['geometry_q2','*','q','q'],['B','*',8,'geometry_q2']],'standalone scale computation paid')
  # The supplied-k error affects the complete positive-tuple output by exactly one.
  one={v:1 for v in variables};L=b['first_root_base'];wrong=S.expand(b[out]-(b['L9']-b['R9'])**2+(L*(L+b['R10b'])-b['R9'])**2)
  need(S.expand(wrong-b[out]).subs(one)==1,'complete wrong-k positive boundary');counts['wrong_k_full_boundaries']+=1
  forms.append({'shared_B':shared,'certificate':c,'polynomial':f,'positive_auxiliaries':len(parent['auxiliaries']),'comparisons':len(pairs),'residual_degrees':degrees,'exact_degree':degree,'full_polynomial_terms':len(poly.terms()),'leading_monomial':dict(zip(ports,top))})
 return {'status':'PASS_INDEPENDENT_GEOMETRY46_FULL_EXPANSION','review_source_sha256':sha(Path(__file__)),'author_pins':PINS,'dependency_pins':child['parent_pins'],'forms':forms,'counts':dict(counts),'scope':'Exact same-coordinate full polynomial identities. Shared-B population projection still assumes B>=8q² externally; standalone pays B=8q². No dyadic P typing, repunit equation, computation controller or universal claim. Parent semantic proof reviewed, not reconstructed by finite tests.'}
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--subject-root',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);v=p.parse_args();j=verify(v.root,v.subject_root)
 if v.expect:need(exact(j,json.loads(v.expect.read_text())),'exact saved review receipt')
 if v.output:v.output.write_text(json.dumps(j,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':j['status'],'counts':j['counts']}))
if __name__=='__main__':main()
