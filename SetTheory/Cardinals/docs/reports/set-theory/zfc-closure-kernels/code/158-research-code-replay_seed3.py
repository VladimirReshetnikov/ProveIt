#!/usr/bin/env python3
"""Generate and independently replay a closed native-code theorem E(0,0)=3.

K and S are already-established derived schemas of C222. This is a finite
Python proof certificate, not a Lean/Rocq compilation or machine check.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json
PIN='63396d6ec0b98744b8b4502c316fbdb7fdb018dcda1dbaed0d2e612e5351b7cc'
T=('zero',)
def I(a,b):return('I',a,b)
def Q(i,a):return('Q',i,a)
def R(a,b):return('R',a,b)
def E(a,b):return('E',a,b)
F=R(T,T)
def N(a):return I(a,F)
def Ex(i,a):return N(Q(i,N(a)))
def frozen(x):return tuple(map(frozen,x))if isinstance(x,list)else x
def axiom(rule,args):
 if rule=='K':a,b=args;return I(a,I(b,a))
 if rule=='S':a,b,c=args;return I(I(a,I(b,c)),I(I(a,b),I(a,c)))
 if rule=='rho1':a,b=args;return Ex(a,E(a,b))
 if rule=='rho2':a,b,c=args;return I(Q(a,I(b,c)),I(Q(a,b),Q(a,c)))
 if rule=='rho6':a,b=args;return I(Ex(a,Q(a,b)),b)
 if rule=='G':a,b,c=args;return I(E(c,a),I(E(c,b),Q(R(a,b),E(a,b))))
 raise ValueError('Unknown axiom: '+rule)
def check(data):
 assert data['convention']=='Every listed node is a closed theorem; GEN has no open assumptions.'
 formulas=[]
 for i,node in enumerate(data['nodes']):
  rule=node['rule'];f=frozen(node['formula']);args=frozen(node['args']);ps=node['parents']
  assert all(type(p)is int and 0<=p<i for p in ps)
  if rule=='mp':
   assert len(ps)==2 and not args
   major,minor=ps;assert formulas[major]==I(formulas[minor],f)
  elif rule=='gen':
   assert len(ps)==1 and len(args)==1;assert f==Q(args[0],formulas[ps[0]])
  else:
   assert not ps;assert f==axiom(rule,args)
  formulas.append(f)
 assert data['output']==len(formulas)-1 and formulas[-1]==E(T,T)
 assert data['native_output_code']==3
 return {'status':'CLOSED_EQUALITY_CERTIFICATE_PASS','nodes':len(formulas),'rules':sorted({x['rule']for x in data['nodes']}),'native_output_code':3}
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--generator',type=Path);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--check-only',type=Path);a=ap.parse_args()
 a.output.mkdir(parents=True,exist_ok=True)
 if a.check_only:
  data=json.loads(a.check_only.read_text());receipt=check(data)
 else:
  assert a.generator is not None
  raw=a.generator.read_bytes();assert hashlib.sha256(raw).hexdigest()==PIN
  spec=importlib.util.spec_from_file_location('seed3_inherited_generator',a.generator);p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
  k=p.eq_refl(p.T);assert p.validate() and not p.nodes[k]['open'];seen=set();todo=[k]
  while todo:
   n=todo.pop()
   if n not in seen:seen.add(n);todo.extend(p.nodes[n]['parents'])
  ordered=sorted(seen);renum={n:i for i,n in enumerate(ordered)};assert ordered[-1]==k
  ns=[]
  for n in ordered:
   old=p.nodes[n];assert not old['open'];ns.append({'rule':old['rule'],'formula':old['formula'],'args':old['args'],'parents':[renum[x]for x in old['parents']]})
  data={'convention':'Every listed node is a closed theorem; GEN has no open assumptions.','nodes':ns,'output':renum[k],'native_output_code':3,'derived_schema_dependency':'K/S are theorems of C222 by the inherited unrestricted Lukasiewicz rho8 basis.'}
  # Serialize and read back before using the independent rule reader.
  proof=a.output/'seed3-proof.json';proof.write_text(json.dumps(data,separators=(',',':'))+'\n');data=json.loads(proof.read_text());receipt=check(data)
  receipt.update(generator_sha256=PIN,generated_nodes=len(p.nodes),closed_ancestor_nodes=len(ordered),proof_sha256=hashlib.sha256(proof.read_bytes()).hexdigest(),scope='Independent finite rule replay with inherited K/S theorem schemas; no new kernel compilation and no TM verification.')
 (a.output/'seed3-replay.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
if __name__=='__main__':main()
