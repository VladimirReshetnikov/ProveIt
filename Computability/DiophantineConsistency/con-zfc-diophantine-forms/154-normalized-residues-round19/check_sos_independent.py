#!/usr/bin/env python3
"""Producer-independent literal integer SOS expansion with strict index checks."""
import argparse,collections,hashlib,json,pathlib

def require(test,msg):
 if not test:raise ValueError(msg)
def loadterms(ts,n,degree):
 require(isinstance(ts,list),'terms not list');p={}
 for t in ts:
  require(isinstance(t,list) and len(t)==2,'bad term')
  c,m=t;require(type(c)is int and c!=0,'coefficient');require(isinstance(m,list) and all(type(v)is int and 0<=v<n for v in m),'index')
  require(m==sorted(m) and len(m)<=degree,'monomial');key=tuple(m);require(key not in p,'duplicate monomial');p[key]=c
 return p
def verify(eqpath,polypath):
 e=json.loads(eqpath.read_text());p=json.loads(polypath.read_text());n=len(e['variables']);out=collections.defaultdict(int)
 require(len({v['name'] for v in e['variables']})==n,'duplicate names')
 for rr in e['residuals']:
  r=loadterms(rr['terms'],n,2)
  for a,c in r.items():
   for b,d in r.items():out[tuple(sorted(a+b))]+=c*d
 out={m:c for m,c in out.items() if c};claimed=loadterms(p['terms'],n,4);require(out==claimed,'literal SOS coefficient mismatch')
 require(p.get('variables',n)==n,'polynomial variable metadata')
 return dict(variables=n,residuals=len(e['residuals']),degree=max(map(len,out)),monomials=len(out),height=max(map(abs,out.values())),equation_sha256=hashlib.sha256(eqpath.read_bytes()).hexdigest(),polynomial_sha256=hashlib.sha256(polypath.read_bytes()).hexdigest())
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('root',type=pathlib.Path);a=ap.parse_args();report=[]
 for p in sorted(a.root.rglob('expanded_polynomial.json')):
  e=p.with_name('equation.json')
  if e.exists():report.append(dict(path=str(e.relative_to(a.root)),**verify(e,p)))
 require(bool(report),'No equations found');print(json.dumps(report,indent=2))
