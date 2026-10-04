#!/usr/bin/env python3
"""Fresh reversal source. Frozen predecessor JSON/Markdown are inert inputs only."""
import argparse,hashlib,json,random
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
def need(v,m):
 if not v:raise ValueError(m)
def H(b):return hashlib.sha256(b).hexdigest()
def unique(pairs):
 d={}
 for k,v in pairs:need(k not in d,'duplicate key');d[k]=v
 return d
def equal(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(equal(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(equal(x,y) for x,y in zip(a,b))
 return a==b

def build(root):
 oldpath=root/'native_binary_input_dilation129.json';raw=oldpath.read_bytes();old=json.loads(raw,object_pairs_hook=unique)['certificate'];src=old['source']
 need(src[10]==['copies','*','x','J'],'old input binding')
 need(src[12:18]==[['modulus','-','Q',1],['quotient_product','*','modulus','quotient_hat'],['congruence_left','+','Ahat','Q'],['congruence_right0','+','quotient_product','z'],['congruence_right','+','congruence_right0',2],['output_bound','+','z','output_slack']],'old congruence boundary')
 need(src[65:70]==[['and__q','*',16,'scale'],['and__scaled_A','*',16,'copies'],['and__padded_A','+','and__scaled_A',12],['and__scaled_B','*',16,'K'],['and__padded_B','+','and__scaled_B',10]],'old native port boundary')
 rows=[list(r) for r in src[:10]]+[['copies','*','x','K'],['reverse_mask','*','q','J'],list(src[11]),['modulus','-','q',1],['quotient_minus_one','-','quotient_hat',1],['quotient_product','*','modulus','quotient_minus_one'],['congruence_right0','+','quotient_product','z'],['scaled_reverse_sum','*','q','congruence_right0'],['congruence_right','+','scaled_reverse_sum',1],list(src[17])]
 rows = [["B","+","q","q"]]+rows[2:]
 rows += [list(r) for r in src[18:]]
 for r in rows:
  if r[0]=='and__scaled_A':r[2]=32
  if r[0]=='and__scaled_B':r[3]='reverse_mask'
 eq=[list(r) for r in old['comparisons']];need(eq[3]==['congruence_left','congruence_right'] and eq[4]==['output_bound','Q'],'old comparisons');eq[3]=['Ahat','congruence_right'];eq[4]=['output_bound','q']
 params=['x','q','z'];aux=[x for x in old['auxiliaries'] if x!='q'];need(len(aux)==48,'arity')
 need(rows[19:66]==src[18:65],'whole raw geometry retained')
 oldand=[list(r) for r in src[65:]];oldand[1][2]=32;oldand[3][3]='reverse_mask';need(rows[66:]==oldand,'native AND exactly bound to new words')
 need(eq[:3]==old['comparisons'][:3] and eq[5:]==old['comparisons'][5:],'all29 native comparisons retained')
 complete=[list(r) for r in rows]
 for i,(a,b) in enumerate(eq):complete.append([f'residual_{i}','-',a,b])
 for i in range(len(eq)):complete.append([f'square_{i}','*',f'residual_{i}',f'residual_{i}'])
 out='square_0'
 for i in range(1,len(eq)):
  name=f'sum_{i}';complete.append([name,'+',out,f'square_{i}']);out=name
 def audit(rs,outputs):
  defined={};available=set(params+aux)
  for name,op,a,b in rs:
   need(name not in available and op in ['+','-','*'],'unique producer');need(all(type(v)is int or v in available for v in [a,b]),'topology');defined[name]=(op,a,b);available.add(name)
  live=set();todo=list(outputs)
  while todo:
   v=todo.pop()
   if type(v)is int or v in live:continue
   live.add(v)
   if v in defined:todo.extend(defined[v][1:])
  need(set(defined)|set(params+aux)<=live,'every row and port live')
  M=sum(r[1]=='*' for r in rs);return {'M':M,'A':len(rs)-M,'total':len(rs)}
 co=audit(rows,[v for e in eq for v in e]);fo=audit(complete,[out]);need(co=={'M':66,'A':64,'total':130} and fo=={'M':100,'A':131,'total':231},'ledgers')
 return {'parameters_positive':params,'positive_witnesses':aux,'source':rows,'comparisons':eq,'full_source':complete,'output':out,'certificate_cost':co,'polynomial_cost':fo,'equations':34,'witnesses':48,'all_rows_ports_live':True,'preserved_geometry_rows':47,'preserved_native_AND_rows_with_two_input_rebindings':64,'parent_json':{'name':oldpath.name,'bytes':len(raw),'sha256':H(raw)}}

def degree_audit(p):
 # Exact leading homogeneous polynomial at each producer, with a structural
 # degree upper bound. No predecessor source is evaluated.
 ports=p['parameters_positive']+p['positive_witnesses'];idx={v:i for i,v in enumerate(ports)}
 env={v:(1,{(idx[v],):1}) for v in ports}
 def val(v):return (0,{():v} if v else {}) if type(v)is int else env[v]
 def plus(a,b,sign):
  da,pa=a;db,pb=b;d=max(da,db);r=dict(pa) if da==d else {}
  if db==d:
   for m,c in pb.items():r[m]=r.get(m,0)+sign*c
  return d,{m:c for m,c in r.items() if c}
 def times(a,b):
  da,pa=a;db,pb=b;r={}
  for x,c in pa.items():
   for y,k in pb.items():m=tuple(sorted(x+y));r[m]=r.get(m,0)+c*k
  return da+db,{m:c for m,c in r.items() if c}
 for name,op,a,b in p['full_source']:env[name]=times(val(a),val(b)) if op=='*' else plus(val(a),val(b),1 if op=='+' else -1)
 deg,poly=env[p['output']];expected=tuple(sorted([idx['and__w']]*4+[idx['and__s']]*8+[idx['and__k']]*4+[idx['q']]*12+[idx['P']]*12));need(deg==40 and poly=={expected:2**48},'exact top degree and coefficient')
 residuals=[env[f'residual_{i}'][0] for i in range(34)];need(residuals.count(20)==1,'unique top residual')
 return {'exact_degree':40,'leading_coefficient':2**48,'leading_monomial':{'and__w':4,'and__s':8,'and__k':4,'q':12,'P':12},'residual_degree_bounds':residuals,'top_residual_index':residuals.index(20)}

def evaluate(rows,vals):
 e=dict(vals)
 for name,op,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b];e[name]=a*b if op=='*' else a+b if op=='+' else a-b
 return e

def checks(p):
 cases=0;allones=0;wrong=0
 for n in range(2,13):
  q=1<<n;B=2*q;P=B**n;S=q*P;J=(P-1)//(B-1);K=(S-1)//(2*B-1)
  need(J>B and q==1<<J.bit_count(),'geometry words')
  for x in range(1,q):
   z=sum(((x>>i)&1)<<(n-1-i) for i in range(n));R=sum(((x>>(n-1-i))&1)<<( (n+1)*i) for i in range(n))
   selected=(2*x*K)&(q*J);need(selected==q*R,'reverse selection');need(0<2*x*K<S and 0<q*J<S,'native prescribed scale')
   need(R>=z and (R-z)%(q-1)==0,'quotient existence')
   vals={'x':x,'q':q,'z':z,'P':P,'J':J,'K':K,'Ahat':selected+1,'quotient_hat':(R-z)//(q-1)+1,'input_slack':q-x,'output_slack':q-z}
   e=evaluate(p['source'][:19],vals);need(all(e[a]==e[b] for a,b in p['comparisons'][:5]),'all five outer comparisons')
   need(16*(2*e['copies']+1)-4==32*e['copies']+12 and 16*(e['reverse_mask']+1)-6==16*e['reverse_mask']+10,'restored positive native ports')
   need(all(v>0 for v in vals.values()),'outer positive coordinates');cases+=1
   if x==q-1:need(z==q-1 and R%(q-1)==0,'zero residue retained');allones+=1
   bad=dict(vals);bad['z']+=1;e=evaluate(p['source'][:19],bad);need(e['Ahat']!=e['congruence_right'],'wrong output');wrong+=1
 rng=random.Random(130);algebraic=0
 for signed in [False,True]:
  for _ in range(256):
   vals={k:rng.randrange(-5,8) if signed else rng.randrange(1,8) for k in p['parameters_positive']+p['positive_witnesses']};e=evaluate(p['source'],vals)
   need(e['Ahat']-e['congruence_right']==vals['Ahat']-1-vals['q']*((vals['q']-1)*(vals['quotient_hat']-1)+vals['z']),'all-value quotient polynomial')
   need(e['and__padded_A']==32*vals['x']*vals['K']+12 and e['and__padded_B']==16*vals['q']*vals['J']+10,'all-value rebound ports')
   full=evaluate(p['full_source'],vals);need(full[p['output']]==sum((e[a]-e[b])**2 for a,b in p['comparisons']),'literal new-source SOS');algebraic+=1
 return {'outer_word_cases_n2_through12':cases,'all_ones_cases':allones,'wrong_output_outer_equations_rejected':wrong,'arbitrary_new_source_algebraic_assignments':algebraic,'full_native_Pell_zero_tuples_tested':0,'scope':'Outer word/quotient checks and new-source algebra only; full positive native extension is a mathematical inherited-contract proof.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=ROOT);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();p=build(a.root)
 pins=[]
 for name in ['native_binary_input_dilation129.md','native_binary_masked_selection63.md','finite_word_hadamard_skew.md','group_linked_binary_geometry47.md','../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md']:
  b=(a.root/name).read_bytes();pins.append({'name':name,'bytes':len(b),'sha256':H(b),'use':'inert theorem/source-interface dependency; no code execution'})
 d={'status':'PASS_COMPLETE_PADDED_BINARY_REVERSAL130','source_sha256':H(Path(__file__).read_bytes()),'certificate':p,'degree':degree_audit(p),'fresh_checks':checks(p),'inert_dependencies':pins,'scope':'Fixed arity in unbounded n, external positive width q=2^n,n>=2; z=reverse_n(x),0<x<q. No canonical length normalization, no universal arithmetic saving, no predecessor helper execution/import.'}
 if a.output:
  with a.output.open('x') as f:json.dump(d,f,indent=2,sort_keys=True);f.write('\n')
 else:need(equal(d,json.loads(a.expect.read_text(),object_pairs_hook=unique)),'exact receipt mismatch')
 print(json.dumps({'status':d['status'],'cost':p['certificate_cost'],'full_cost':p['polynomial_cost'],'degree':d['degree'],'checks':d['fresh_checks']}))
if __name__=='__main__':main()
