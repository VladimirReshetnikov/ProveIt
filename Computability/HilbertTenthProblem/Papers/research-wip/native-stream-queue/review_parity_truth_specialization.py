#!/usr/bin/env python3
"""Independent full-source audit; never call the candidate's evaluator/checker."""
from pathlib import Path
from fractions import Fraction
import argparse, hashlib, itertools, json, types
import sympy as s
PIN='fabf4eef1b31f4cf6695cc5907e2d56f5bd2fac1e9ab8f0ad5b375cbc0100bf7'
def need(ok,message):
 if not ok:raise ValueError(message)
def run(source):
 data=source.read_bytes();need(hashlib.sha256(data).hexdigest()==PIN,'source pin')
 module=types.ModuleType('authenticated_parity_candidate');module.__file__=str(source)
 exec(compile(data,str(source),'exec'),module.__dict__)
 counts={};records=[]
 def check(name,ok):need(bool(ok),name);counts[name]=counts.get(name,0)+1
 def interpret(p,values):
  env=dict(values)
  for n,op,a,b in p['gates']:
   need(n not in env and op in ('add','sub','mul'),'topological register')
   a=a if type(a) is int else env[a];b=b if type(b) is int else env[b]
   env[n]={'add':lambda:a+b,'sub':lambda:a-b,'mul':lambda:a*b}[op]()
  return env[p['output']],None if p['truth_output'] is None else env[p['truth_output']]
 def atom(x,mode,prefix='',boolean=True):
  q=x[prefix+'q'] if mode=='natural' else x[prefix+'qp']-x[prefix+'qm'];b=x[prefix+'b']
  return (x[prefix+'L']-2*q-b)**2+(b*(b-1) if boolean else 0)+(x[prefix+'qp']*x[prefix+'qm'] if mode=='signed_canonical' else 0)
 for mode in ('signed_existential','signed_canonical','natural'):
  packets=[module.build_atom(mode,materialize_truth=t) for t in (False,True)]+[module.build_nand(mode,variant=v) for v in ('relation','accepted','projected','factored')]
  for p in packets:
   x={k:s.Symbol(k) for k in p['inputs']+p['witnesses']};poly,truth=interpret(p,x);c=p['config'];isatom=c['kind']=='atom'
   if isatom:
    expected=atom(x,mode);ledger={'signed_existential':(3,5),'signed_canonical':(4,6),'natural':(3,4)}[mode];ledger=(ledger[0],ledger[1]+int(c['materialize_truth']))
    if c['materialize_truth']:check('materialized_truth',truth==1-x['b'])
   else:
    a,b=x['a_b'],x['b_b'];g=(a-1)*(b-1);v=c['variant']
    if v=='factored':expected=atom(x,mode,'a_',False)+atom(x,mode,'b_',False)+(a+b-1)**2-a*b
    else:
     expected=atom(x,mode,'a_')+atom(x,mode,'b_')+(g*g if v=='projected' else (x['z']-1+g)**2)
     if v=='accepted':expected+=(x['z']-1)**2
    m,A={'relation':(8,14),'accepted':(9,15),'projected':(8,12),'factored':(6,11)}[v];ledger=(m+2*(mode=='signed_canonical'),A+2*(mode=='signed_canonical')-2*(mode=='natural'))
   check('whole_polynomial_identity',s.expand(poly-expected)==0)
   degree=s.Poly(poly,*x.values()).total_degree();check('exact_degree',degree==(2 if isatom or c['variant']=='factored' else 4))
   M=sum(row[1]=='mul' for row in p['gates']);A=len(p['gates'])-M;check('complete_paid_ledger',(M,A)==ledger and p['ledger']=={'M':M,'A':A,'total':M+A,'witnesses':len(p['witnesses'])})
   dependencies={n:[v for v in (a,b) if type(v) is str] for n,op,a,b in p['gates']};live=set()
   def visit(n):
    if n in dependencies and n not in live:
     live.add(n)
     for v in dependencies[n]:visit(v)
   visit(p['output']);visit(p['truth_output']);check('all_gates_live',len(live)==len(p['gates']))
   records.append({'config':c,'M':M,'A':A,'total':M+A,'witnesses':len(p['witnesses']),'exact_degree':degree,'full_polynomial':str(s.expand(poly)),'gate_sha256':hashlib.sha256(json.dumps(p['gates'],separators=(',',':')).encode()).hexdigest()})
  p=packets[0]
  for L in range(0 if mode=='natural' else -17,18):
   for w in itertools.product(range(7),repeat=len(p['witnesses'])):
    x=dict(zip(p['witnesses'],w));x['L']=L;value,_=interpret(p,x)
    q=x['q'] if mode=='natural' else x['qp']-x['qm'];expected=x['b']==L%2 and q==L//2 and (mode!='signed_canonical' or x['qp']*x['qm']==0)
    check('unfiltered_natural_atom_fibers',value>=0 and (value==0)==expected)
 # An independent integer-lattice Boolean identity and domain counterexamples.
 for a,b in itertools.product(range(-50,51),repeat=2):
  B=(a+b-1)**2-a*b;check('signed_integer_NAND_block',B>=0 and (B==0)==((a,b) in ((0,1),(1,0),(1,1))))
 check('real_atom_false_zero',interpret(module.build_atom('natural'),{'L':1,'q':0,'b':Fraction(1,2)})[0]==0)
 check('signed_canonical_false_zero',interpret(module.build_atom('signed_canonical'),{'L':3,'qp':1,'qm':-1,'b':0})[0]==0)
 check('private_quotient_observation',interpret(module.build_atom(),{'L':0,'qp':1,'qm':1,'b':0})[0]==0 and interpret(module.build_atom('signed_canonical'),{'L':0,'qp':1,'qm':1,'b':0})[0]==1)
 return {'status':'PASS','source_sha256':PIN,'review_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'checks':counts,'circuits':records,'scope':'Independent full-polynomial interpretation, paid ledgers and unfiltered bounded atom fibers. Unbounded correctness relies on the accompanying integer/fiber proof, not this finite census. No candidate evaluator or verifier called; authenticated bytes compiled directly, bypassing .pyc.'}
def main():
 p=argparse.ArgumentParser();p.add_argument('--source',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--expect',type=Path);a=p.parse_args();r=run(a.source)
 encoded=json.dumps(r,indent=2,sort_keys=True)+'\n'
 if a.expect:need(a.expect.read_text()==encoded,'exact receipt bytes')
 a.output.write_text(encoded);print(json.dumps(r['checks'],sort_keys=True))
if __name__=='__main__':main()
