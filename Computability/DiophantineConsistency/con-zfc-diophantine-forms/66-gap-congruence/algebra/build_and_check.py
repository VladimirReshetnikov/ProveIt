"""Authored transformation/checker; reads upstream JSON as inert data only."""
import collections, hashlib, json, random
from pathlib import Path
ROOT=Path(__file__).resolve().parent
UP=ROOT/'upstream'

def require(p,msg):
 if not p: raise ValueError(msg)
def evaluate(d,inputs,mod=None):
 v=dict(inputs)
 for n,o,a,b in d['source']:
  x=a if isinstance(a,int) else v[a];y=b if isinstance(b,int) else v[b]
  z=x+y if o=='+' else x-y if o=='-' else x*y
  v[n]=z if mod is None else z%mod
 return v[d['output']]
def live(rows,out):
 needed={out}
 for n,o,a,b in reversed(rows):
  if n in needed:needed.update([a,b])
 return [r for r in rows if r[0] in needed],needed

def transform(old,degree):
 d=json.loads(json.dumps(old));rows=d['source']
 # Reuse V+u for 2V+u. Match structure, not the incidental gate numbers.
 vu=next(n for n,o,a,b in rows if o=='+' and (a,b)==('V','u'))
 twice=next(n for n,o,a,b in rows if o=='*' and (a,b)==(2,'V'))
 twiceplus=next(n for n,o,a,b in rows if o=='+' and (a,b)==(twice,'u'))
 rows=[([n,'+','V',vu] if n==twiceplus else [n,o,a,b]) for n,o,a,b in rows]
 if degree==24:
  # Translate z_old=z+1 and regroup the transport residual exactly.
  pos=next(i for i,r in enumerate(rows) if r[0]=='transport_res')
  rows[pos:pos+1]=[
   ['shift_KC','*','K0','C'],['shift_zqm','*','z','qm'],
   ['shift_t0','-','shift_KC','F'],['shift_t1','-','shift_t0','shift_zqm'],
   ['shift_qt','*','q','shift_t1'],['shift_XC','*','X','C'],
   ['transport_res','+','shift_qt','shift_XC']]
 rows,needed=live(rows,d['output']);d['source']=rows
 require(set(d['witnesses']+d['fixed_numerals'])<=needed,'dead input')
 require(len({r[0] for r in rows})==len(rows),'duplicate name')
 d['operations']=len(rows);d['operation_breakdown']=dict(collections.Counter(r[1] for r in rows))
 d['residual_evaluator_operations']=len(live(rows,d['residuals'][0])[0]) # reset below to union
 required=set(d['residuals'])
 for n,o,a,b in reversed(rows):
  if n in required:required.update([a,b])
 d['residual_evaluator_operations']=sum(r[0] in required for r in rows)
 d['name']=f'fifteen_positive_shortened_degree_{degree}'
 d['proof']='SHORTENED_INTEGRAL_ROOT_PROOF.md'
 d['coefficient_binding_file']='coefficients/COEFFICIENT_BINDING.json'
 d['transformation']={'reuse_auxiliary_sum':True,'transport_shift':degree==24,'source_sha256':hashlib.sha256((UP/f'circuits/p15_degree{degree}.json').read_bytes()).hexdigest()}
 return d

def main():
 rng=random.Random(840159);receipt=[]
 for degree,ops in [(24,88),(26,87),(30,78)]:
  old=json.loads((UP/f'circuits/p15_degree{degree}.json').read_text());new=transform(old,degree)
  require(new['operations']==ops,'cost mismatch')
  for j in range(240):
   inp={x:rng.randrange(-7,9) for x in old['witnesses']+old['fixed_numerals']}
   oldinp=dict(inp)
   if degree==24:oldinp['z']+=1
   modulus=None if j<120 else 1000000007
   require(evaluate(new,inp,modulus)==evaluate(old,oldinp,modulus),f'identity {degree}/{j}')
  # Generic two local polynomial identities, independent of full circuit.
  for j in range(1000):
   V,u,q,K,C,F,z,X=[rng.randrange(-50,51) for _ in range(8)]
   require(2*V+u==V+(V+u),'sum identity')
   require(q*(K*C+(q-F)-(z+1)*(q-1))+X*C-q==q*(K*C-F-z*(q-1))+X*C,'transport identity')
  (ROOT/f'p15_{ops}_degree{degree}.json').write_text(json.dumps(new,indent=2)+'\n')
  receipt.append({'degree':degree,'operations':ops,'source_operations':old['operations'],'signed_exact_checks':120,'modular_checks':120,'local_identity_checks':2000,'source_sha256':new['transformation']['source_sha256'],'status':'PASS'})
 (ROOT/'RESULTS.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
