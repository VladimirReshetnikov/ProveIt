#!/usr/bin/env python3
"""Independent literal-source and semantic-contract audit of double loading."""
import argparse,copy,hashlib,json,random,tempfile,types
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={
 'source':'cd595535905dc3302144de243d3cc5430294c453f0bc5110b8eff973d4049070',
 'receipt':'6ba153b1cda8c68a3ad6cdd373b9033f6f6f72ba47c674a771d2b643fd778787',
 'note':'60dc6e343b73c19b4c7110fa19aeb212c1893740c3964ffb6eb6142c75590881'}
PARENT={
 'pell_fixed_affine_exponent52.py':'64893c621c538a8f5dba8a0fc417fd46aae7c607da996dd5f304ca13642f1486',
 'pell_fixed_affine_exponent52.json':'ebf7cafaa1f19c77c72302e5fee2e2c41c19b76a1ab72942758478ab1dd1adf1',
 'pell_fixed_affine_exponent52.md':'891301377f3740657c268e3e48f697dc5cb5a08037665aa772c1bff0d200b9ec',
 'three_mass_exponential_input_bridge.py':'fe892d2920a866c723ad648ea52ac467d0f531c6aabe13c000f3cd53fef57ef2',
 'three_mass_exponential_input_bridge.json':'976e75fc90da362949774ee5cfae2e1b48f35bf351203825b82b3dfba7353296',
 'three_mass_exponential_input_bridge.md':'0d839b4661cad99e37c19a590e9e14840d1d2961383a111c107f2957ccd87187'}
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def audit_rows(rows,inputs,outputs):
 env={v:1 for v in inputs};by={};M=0
 for n,op,a,b in rows:
  assert type(n)is str and n not in env and op in ('+','-','*')
  assert all(type(v)is int or type(v)is str and v in env for v in (a,b))
  da=0 if type(a)is int else env[a];db=0 if type(b)is int else env[b]
  env[n]=da+db if op=='*' else max(da,db);by[n]=(a,b);M+=op=='*'
 todo=list(outputs);live=set()
 while todo:
  n=todo.pop()
  if type(n)is str and n not in live:
   live.add(n);todo.extend(by.get(n,()))
 assert set(by)|set(inputs)<=live
 return {'operations':len(rows),'M':M,'A':len(rows)-M,'all_gates_and_coordinates_live':True,'literal_degree_upper_bound':max(env[x] if type(x)is str else 0 for x in outputs)}

def ev(rows,assignment):
 out=dict(assignment)
 for n,op,a,b in rows:
  a=a if type(a)is int else out[a];b=b if type(b)is int else out[b]
  out[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return out

def reconstruct(e,parent,C):
 prefix=[]
 for n,op,a,b in e['source'][:-1]:
  rename=lambda v:v if type(v)is int or v=='x' else 'first__'+v
  prefix.append(['first__'+n,op,rename(a),rename(b)])
 def inner(rows):
  ans=[]
  for n,op,a,b in rows:
   if n=='exp__r':assert (op,a,b)==('*',48,'x');a,b=48*C,'first__Q'
   ans.append([n,op,a,b])
  return ans
 whole=prefix+inner(parent['polynomial_source'])+[
  ['first_residual','-','first__factor_product_5',1],['first_square','*','first_residual','first_residual'],
  ['double_output','+','first_square',parent['output']]]
 return prefix+inner(parent['source']),whole

class ExactDAG:
 def __init__(self):self.table={}
 def intern(self,t):
  if t not in self.table:self.table[t]=len(self.table)
  return self.table[t]
 def atom(self,v):return self.intern((type(v).__name__,v))
 def op(self,op,a,b):return self.intern((op,a,b))
 def walk(self,rows,env,cut):
  env=dict(env)
  for n,op,a,b in rows:
   av=self.atom(a) if type(a)is int else env[a];bv=self.atom(b) if type(b)is int else env[b]
   env[n]=self.op(op,av,bv)
   if n in cut:env[n]=cut[n]
  return env

def run(source,receipt,note,root):
 for name,path in [('source',source),('receipt',receipt),('note',note)]:assert sha(path.read_bytes())==PINS[name]
 for name,pin in PARENT.items():assert sha((root/name).read_bytes())==pin
 r=json.loads(receipt.read_text());assert r['source_sha256']==PINS['source']
 e=json.loads((root/'pell_fixed_affine_exponent52.json').read_text())
 pp=json.loads((root/'three_mass_exponential_input_bridge.json').read_text())
 parents={f['variant']:f['packet'] for f in pp['forms'] if f['finalizer']=='sos'}
 mod=types.ModuleType('_independently_authenticated_double');mod.__file__=str(source)
 exec(compile(source.read_bytes(),str(source),'exec'),mod.__dict__)
 rng=random.Random(9610852);counts=Counter();ledgers=[]
 for f in r['forms']:
  p=f['packet'];C=f['program_multiplier'];variant=f['variant'];parent=parents[variant]
  assert C in (1,3) and p['program_multiplier']==C
  assert exact(mod.build(variant,program_multiplier=C,root=root),p)
  oldconsumer=[row for row in parent['polynomial_source'] if 'x' in row[2:]]
  assert oldconsumer==[['exp__r','*',48,'x']] and not any('x' in pair for pair in parent['comparisons'])
  sr,pol=reconstruct(e,parent,C);assert exact(sr,p['source']) and exact(pol,p['polynomial_source'])
  assert p['parameters']==['x','y','T'] and p['auxiliaries']==['first__'+n for n in e['auxiliaries']]+parent['auxiliaries']
  assert p['comparisons']==[['first__factor_product_5',1]]+parent['comparisons']
  assert len(p['comparisons'])==22
  supplied=p['parameters']+p['auxiliaries'];roots=[x for pair in p['comparisons'] for x in pair]
  assert audit_rows(sr,supplied,roots)==p['certificate_ledger']
  led=audit_rows(pol,supplied,[p['output']]);assert led==p['polynomial_ledger']
  assert [led[k]-parent['polynomial_ledger'][k] for k in ('operations','M','A')]==[54,32,22]
  assert len(p['auxiliaries'])==len(parent['auxiliaries'])+12
  assert p['degree']=={'exact_degree_claimed':False,'upper_bound':parent['degree']['upper_bound']}
  assert led['literal_degree_upper_bound']==p['degree']['upper_bound']
  # Exact affine identity for the actual two-input expression, followed by
  # complete expression-DAG equality of all retained parent registers.
  assert e['source'][:2]==[['r','*',48,'x'],['Q','+','r','delta']]
  # Coefficients in actual external x and fresh first__delta, in that order.
  virtual_r=[48*C*a for a in (48,1)];folded_r=[(48*C)*a for a in (48,1)]
  assert virtual_r==folded_r==[2304*C,48*C]
  d=ExactDAG();base={v:d.atom(v) for v in supplied};cut=d.atom(('proved_second_r_affine',2304*C,48*C))
  child=d.walk(pol,base,{'exp__r':cut})
  first=d.walk(e['source'][:-1],{'x':base['x'],**{v:base['first__'+v] for v in e['auxiliaries']}},{})
  pv={'x':d.op('*',d.atom(C),first['Q']),'y':base['y'],'T':base['T'],**{v:base[v] for v in parent['auxiliaries']}}
  old=d.walk(parent['polynomial_source'],pv,{'exp__r':cut})
  for n,_,_,_ in parent['polynomial_source']:assert child[n]==old[n]
  for pair in parent['comparisons']:
   for v in pair:assert (d.atom(v) if type(v)is int else child[v])==(d.atom(v) if type(v)is int else old[v])
  res=d.op('-',first['factor_product_5'],d.atom(1))
  assert child[p['output']]==d.op('+',d.op('*',res,res),old[parent['output']])
  counts['complete_literal_sources']+=1;counts['complete_polynomial_identities']+=1;counts['retained_comparisons']+=21
  counts['recounted_full_gates']+=len(pol)
  for j in range(12):
   values={v:rng.randrange(-2,4) for v in supplied}
   if j>=8:values={v:Fraction(w,3) for v,w in values.items()}
   a=ev(e['source'][:-1],{'x':values['x'],**{v:values['first__'+v] for v in e['auxiliaries']}})
   b=ev(parent['polynomial_source'],{'x':C*a['Q'],'y':values['y'],'T':values['T'],**{v:values[v] for v in parent['auxiliaries']}})
   c=ev(pol,values)
   assert c[p['output']]==(a['factor_product_5']-1)**2+b[parent['output']]
   get=lambda v:v if type(v)is int else c[v]
   assert c[p['output']]==sum((get(x)-get(y))**2 for x,y in p['comparisons'])
   counts['full_numeric_and_SOS_checks']+=1;counts['rational_cases']+=j>=8
  vals={v:1 for v in supplied}
  for field,v in [('program_multiplier',float(C)),('program_multiplier',True),('output','x')]:
   bad=copy.deepcopy(p);bad[field]=v
   try:mod.checked(bad,root=root)
   except ValueError:counts['guard_rejections']+=1
   else:raise AssertionError('packet mutation accepted')
  bad=copy.deepcopy(p);bad['polynomial_source'][51][2]=float(48*C)
  try:mod.checked(bad,root=root)
  except ValueError:counts['guard_rejections']+=1
  else:raise AssertionError('float coefficient accepted')
  for key,v in [('x',0),('x',True),('y',-1),('T',-1),('first__delta',0),('exp__delta',0)]:
   bad=dict(vals);bad[key]=v
   try:mod.evaluate(p,bad,root=root)
   except ValueError:counts['guard_rejections']+=1
   else:raise AssertionError('domain mutation accepted')
  got=mod.build(variant,program_multiplier=C,root=root);got['comparisons'][0][1]=99
  assert exact(mod.build(variant,program_multiplier=C,root=root),p);counts['copy_checks']+=1
  ledgers.append({'variant':variant,'C':C,'ledger':led,'positive_private_witnesses':len(p['auxiliaries'])})
 assert len(r['forms'])==8 and {(f['variant'],f['program_multiplier']) for f in r['forms']}==set((v,C) for v in parents for C in (1,3))
 for C in (2,27,10**80+7):
  p=mod.build('nop',program_multiplier=C,root=root);sr,pol=reconstruct(e,parents['nop'],C)
  assert exact(pol,p['polynomial_source']) and p['polynomial_ledger']['operations']==578
  counts['additional_exact_fixed_coefficients']+=1
 with tempfile.TemporaryDirectory() as tmp:
  rr=Path(tmp)
  for name in PARENT:(rr/name).write_bytes((root/name).read_bytes())
  mod.build(root=rr)
  for name in PARENT:
   raw=(rr/name).read_bytes();(rr/name).write_bytes(raw+b'\n')
   try:mod.build(root=rr)
   except ValueError:counts['warm_source_pin_rejections']+=1
   else:raise AssertionError('warm source mutation accepted')
   (rr/name).write_bytes(raw)
 q1minus=2**92;second_negative_exponent=96*q1minus-4
 assert second_negative_exponent>0 and second_negative_exponent%96==92
 # The actual positive extensions for these exponents are inherited theorems;
 # this scalar check deliberately does not materialize giant Pell witnesses.
 assert (-1)*(-1)*(1+0)-1==0 and ((-1)-1)**2+((-1)-1)**2+0==8
 return {'status':'PASS_INDEPENDENT_DOUBLE_INPUT_REVIEW','review_source_sha256':sha(Path(__file__).read_bytes()),
 'pins':PINS,'parent_pins':PARENT,'counts':dict(counts),'ledgers':ledgers,
 'negative_branch_obstruction':{'x':1,'C':1,'Q1_minus':str(q1minus),'log2_Q2_minus':str(second_negative_exponent),'unchecked_product_value':0,'actual_SOS_value':8,'full_witnesses_materialized':False},
 'scope':'All eight actual emitted full sources independently reconstructed and checked. General C is a fixed positive numeral; no universal table/divider hidden in fixture counts. Primary source theorem reviewed separately.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 for n in ('source','receipt','note','root'):ap.add_argument('--'+n,type=Path,required=True)
 ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=run(a.source,a.receipt,a.note,a.root)
 if a.expect:assert exact(r,json.loads(a.expect.read_text()))
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts']}))
if __name__=='__main__':main()
