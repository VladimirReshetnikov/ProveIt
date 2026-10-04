#!/usr/bin/env python3
"""Data-only exact sparse-polynomial audit of frozen raw-recoder DAGs.
This does not import or execute the arithmetic DAG producer or upstream code.
"""
import argparse, hashlib, json
from collections import Counter
from pathlib import Path

EXPECTED = {
 'exp': 'ef4bb40c0423ac84e4db8bbe7dac0053e6befdad220996659ccea383a9556047',
 'forward': '0e1e8892b0bd7d6f8c0d9787be9bf3f20d19c141bd182ea1032fbb45604794e5',
 'reverse': 'd86813b7849607f9f7e26f0ae221697a1479cafb31e9370d9640f94a27f4f292',
 'pair': 'd8af326714f0c741b1f1039724b70cf688a8a86cf6254a5c69f09f6b78f64a14',
 'pair_inline': 'a8fbf064395d2fac5aa041a4c54826938ea2645fba793e0de7500e19f7ca4567',
 'pair_positive': 'f4c3a0fe8d4a423e364057107f164c72e1e1ed90c5afad7002ba6e2996792b62',
}
PORTS = {'exp': {'base','index','output'}, 'forward': {'C','Raw'}, 'reverse': {'C','Raw'},
 'pair': {'G','RawLeft','RawRight','A','B','T'},
 'pair_inline': {'G','RawLeft','RawRight'},
 'pair_positive': {'G','RawLeft','RawRight','A','B','Tplus'}}

def require(test, message):
 if not test: raise ValueError(message)
def const(x): return {():x} if x else {}
def variable(x): return {(x,):1}
def add(a,b,sign=1):
 c=dict(a)
 for m,v in b.items():
  c[m]=c.get(m,0)+sign*v
  if not c[m]:del c[m]
 return c
def mul(a,b):
 c={}
 for x,u in a.items():
  for y,v in b.items():
   m=tuple(sorted(x+y));c[m]=c.get(m,0)+u*v
 return {m:v for m,v in c.items() if v}
def degree(p):return max(map(len,p),default=-1)
def signature(p):return hashlib.sha256(json.dumps([[list(m),v] for m,v in sorted(p.items())],separators=(',',':')).encode()).hexdigest()

def check(path,mode):
 blob=path.read_bytes();require(hashlib.sha256(blob).hexdigest()==EXPECTED[mode],'Frozen DAG hash mismatch: '+mode)
 d=json.loads(blob);env={x:variable(x) for x in PORTS[mode]|set(d['witnesses'])}
 require(len(d['witnesses'])==len(set(d['witnesses'])),'Duplicate witness')
 def resolve(x):
  if type(x) is int:return const(x)
  require(type(x) is str and x in env,'Unknown expression '+repr(x));return env[x]
 M=A=0
 for row in d['nodes']:
  require(len(row)==4,'Bad gate');out,op,left,right=row
  require(out not in env,'Repeated definition');x,y=resolve(left),resolve(right)
  if op=='+':z=add(x,y);A+=1
  elif op=='-':z=add(x,y,-1);A+=1
  elif op=='*':z=mul(x,y);M+=1
  else:raise ValueError('Unknown operation')
  env[out]=z
 residuals=[add(resolve(a),resolve(b),-1) for a,b in d['equations']]
 E=len(residuals);distribution=Counter(map(degree,residuals));maximum=max(distribution)
 sos={}
 for p in residuals:sos=add(sos,mul(p,p))
 require(maximum==6,'Residual degree is not exactly6');require(degree(sos)==12,'SOS degree is not exactly12')
 leading={m:v for m,v in sos.items() if len(m)==12}
 expected_top=1 if mode=='exp' else 7 if mode in ('forward','reverse') else 14
 require(len(leading)==expected_top,'Unexpected top-degree monomial count')
 for m,v in leading.items():
  powers=Counter(m)
  require(v==1 and sorted(powers.values())==[4,8],'Unexpected highest-degree coefficient or exponent pattern')
  w=[name for name,e in powers.items() if e==8][0];z=[name for name,e in powers.items() if e==4][0]
  require(w.endswith('w') and z==w[:-1]+'z','Leading monomial is not w^8 z^4')
 return {'source_sha256':EXPECTED[mode], 'base_M':M,'base_A':A,'base_operations':M+A,
  'positive_witnesses':len(d['witnesses']),'equations':E,'residual_degree_counts':{str(k):v for k,v in sorted(distribution.items())},
  'max_total_degree':maximum,'sos_exact_total_degree':degree(sos),'sos_nonzero_monomials':len(sos),'sos_degree12_monomials':len(leading),
  'sos_additional_M':E,'sos_additional_A':2*E-1,'sos_additional_operations':3*E-1,
  'single_polynomial_M':M+E,'single_polynomial_A':A+2*E-1,'single_polynomial_operations':M+A+3*E-1,
  'sos_polynomial_sha256':signature(sos),'degree12_terms':[[dict(Counter(m)),v] for m,v in sorted(leading.items())]}

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--evidence',type=Path,default=Path('/workspace/shared/fixed-digit-dilation-20261003/final-evidence'))
 args=p.parse_args();results={m:check(args.evidence/(m+'-dag.json'),m) for m in EXPECTED}
 print(json.dumps({'scope':'Exact symbolic expansion of data-only frozen recoder DAGs; every free input and every positive witness has degree1. No periodic-board or inherited-history substitution is included.','modes':results},indent=2,sort_keys=True))
if __name__=='__main__':main()
