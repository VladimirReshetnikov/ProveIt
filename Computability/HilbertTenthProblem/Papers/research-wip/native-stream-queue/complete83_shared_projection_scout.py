"""Fresh bounded source experiment; read the parent solely as bytes/JSON."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path

PINS = {
 'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'complete84_scaled_strong_output.py': '8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
}

def require(ok, message):
 if not ok: raise ValueError(message)

def evaluate(rows, ports, add=lambda x,y:x+y, sub=lambda x,y:x-y, mul=lambda x,y:x*y, const=lambda x:x):
 env=dict(ports)
 for name,op,left,right in rows:
  a=const(left) if type(left) is int else env[left]
  b=const(right) if type(right) is int else env[right]
  env[name]={'*':mul,'+':add,'-':sub}[op](a,b)
 return env

def source(root):
 for name,digest in PINS.items():
  require(hashlib.sha256((root/name).read_bytes()).hexdigest()==digest, 'pin '+name)
 parent=json.loads((root/'complete84_scaled_strong_output.json').read_bytes())['packet']
 old=parent['source']; byname={r[0]:r for r in old}
 for expected in [
  ['gamma_sum','+','rho','sigma'],['gam','*','gamma_sum','a4m5'],
  ['R14','+','D1','gam'],['modulus_multiple','*','rho','a4m5'],
  ['exponent_rhs','+','exponent_partial','modulus_multiple']]:
  require(byname[expected[0]]==expected,'cut definition')
 require([(r[0],i) for r in old for i in (2,3) if r[i]=='rho']==[('gamma_sum',2),('modulus_multiple',2)],'rho consumers')
 require([r[0] for r in old if 'gamma_sum' in r[2:]]==['gam'],'gamma consumer')
 require([r[0] for r in old if 'modulus_multiple' in r[2:]]==['exponent_rhs'],'projection consumer')
 rows=[]
 for row in old:
  name=row[0]
  if name in ('gamma_sum','modulus_multiple'):continue
  if name=='gam':rows.append(['gam','*','sigma','a4m5'])
  elif name=='R14':rows.extend([['shared_main_partial','+','D1','shared_projection'],['R14','+','shared_main_partial','gam']])
  elif name=='exponent_rhs':rows.append(['exponent_rhs','+','exponent_partial','shared_projection'])
  else:rows.append(row)
 free=['shared_projection' if x=='rho' else x for x in parent['free']]
 witnesses=['shared_projection' if x=='rho' else x for x in parent['witnesses']]
 known=set(free)
 for name,op,l,r in rows:
  require(name not in known and op in ('+','-','*'),'unique gate')
  require(all(type(x) is int or x in known for x in (l,r)),'dependency')
  known.add(name)
 used={'polynomial'}
 for name,op,l,r in reversed(rows):
  require(name in used,'dead row '+name)
  used.update(x for x in (l,r) if type(x) is str)
 require(set(free)<=used,'dead port')
 counts=Counter(r[1] for r in rows); ledger={'M':counts['*'],'A':counts['+']+counts['-'],'total':len(rows)}
 require(ledger=={'M':46,'A':37,'total':83},'ledger')
 return parent,rows,free,witnesses,ledger

# Exact sparse polynomial cut in D1,H,rho,sigma,P=exponent_partial.
def cut_identity():
 n=5; z=(0,)*n
 def lit(c):return {z:c} if c else {}
 def var(i):return {tuple(int(j==i) for j in range(n)):1}
 def add(a,b):
  c=dict(a)
  for m,v in b.items():c[m]=c.get(m,0)+v
  return {m:v for m,v in c.items() if v}
 def mul(a,b):
  c={}
  for m,x in a.items():
   for n,y in b.items():
    k=tuple(i+j for i,j in zip(m,n));c[k]=c.get(k,0)+x*y
  return {m:v for m,v in c.items() if v}
 base,H,rho,sigma,P=map(var,range(5)); U=mul(rho,H)
 require(add(base,mul(add(rho,sigma),H))==add(add(base,U),mul(sigma,H)),'main cut identity')
 require(add(P,mul(rho,H))==add(P,U),'input cut identity')
 return {'independent_ports':['D1','H','rho','sigma','exponent_partial'], 'identities':['D1+(rho+sigma)*H=(D1+rho*H)+sigma*H','P+rho*H=P+U under U=rho*H'], 'scope':'all commutative rings; unchanged downstream row induction'}

def numeric(parent,rows):
 checks=0
 for case in range(48):
  env={p:((j*17+case*11)%13-6) for j,p in enumerate(parent['free'])}
  if case>=24:env={p:Fraction(v,(j+case)%5+1) for j,(p,v) in enumerate(env.items())}
  old=evaluate(parent['source'],env); newports={k:v for k,v in env.items() if k!='rho'}
  newports['shared_projection']=env['rho']*old['a4m5']; new=evaluate(rows,newports)
  for name in set(old)&set(new)-{'gam'}:
   require(old[name]==new[name], 'numeric '+name);checks+=1
  require(all(old[n]==new[n] for n in parent['factors']+['polynomial']),'outputs')
 return {'assignments':48,'rational_assignments':24,'retained_value_equalities':checks,'full_positive_zeros_materialized':0}

def coefficients(parent,rows):
 # Full dense coefficient evaluation of emitted arrays; diagnostics, not valid-program data.
 receipts=[]
 for modulus,shift in [(1000003,1),(1000033,3)]:
  def clean(a):
   while a and a[-1]==0:a.pop()
   return a
  def add(a,b):return clean([((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0))%modulus for i in range(max(len(a),len(b)))])
  def sub(a,b):return add(a,[(-x)%modulus for x in b])
  def mul(a,b):
   if not a or not b:return []
   c=[0]*(len(a)+len(b)-1)
   for i,x in enumerate(a):
    for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%modulus
   return clean(c)
  const=lambda n:clean([n%modulus])
  fixed={p:2*j+shift+2 for j,p in enumerate(parent['fixed_numerals'])}
  ports={p:const(fixed[p]) if p in fixed else [0,(j+shift+1)%modulus] for j,p in enumerate(parent['free']) if p!='rho'}
  ports['shared_projection']=[0,29+shift]
  out=evaluate(rows,ports,add,sub,mul,const)
  degrees=[len(out[p])-1 for p in parent['factors']]
  require(degrees==[22,18,32,60,7,2,46] and len(out['polynomial'])-1==187,'degree diagnostic')
  receipts.append({'prime':modulus,'fixed_diagnostic_numerals':fixed,'factor_degrees':degrees,'degree':187,'leading_coefficient':out['polynomial'][-1], 'coefficient_sha256':hashlib.sha256(json.dumps(out['polynomial'],separators=(',',':')).encode()).hexdigest()})
 return receipts

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--root',type=Path,required=True);parser.add_argument('--output',type=Path);parser.add_argument('--expect',type=Path);a=parser.parse_args()
 parent,rows,free,witnesses,ledger=source(a.root)
 result={'scope':'Unresolved positive shared-projection83 relaxation; no new universal bound', 'parent_pins':PINS,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
  'packet':{'source':rows,'free':free,'witnesses':witnesses,'witness_domain':'strictly positive integers','ordinary_input':parent['ordinary_input'],'fixed_numerals':parent['fixed_numerals'],'factors':parent['factors'],'output':'polynomial','ledger':ledger,'exact_degree':187,'factor_exact_degrees':[22,18,32,60,7,2,46], 'forward_map':'shared_projection=rho*(4*a+3), all other ports unchanged','inverse_condition':'(4*a+3) divides shared_projection','universal_language':'unresolved'},
  'cut':cut_identity(),'numeric':numeric(parent,rows),'degree_diagnostics':coefficients(parent,rows)}
 encoded=json.dumps(result,indent=2,sort_keys=True)+'\n'
 if a.expect:require(a.expect.read_text()==encoded,'exact receipt mismatch')
 if a.output:a.output.write_text(encoded)
 print(json.dumps({'ledger':ledger,'witnesses':len(witnesses),'degree':187,'receipt_sha256':hashlib.sha256(encoded.encode()).hexdigest()},sort_keys=True))
if __name__=='__main__':main()
