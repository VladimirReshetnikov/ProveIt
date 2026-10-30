"""Exact factor-degree certificate for the specific factored 87-gate parent."""
from pathlib import Path
import hashlib,json,runpy
here=Path(__file__).resolve().parent;s=runpy.run_path(str(here/'verify_equation86.py'));P=s['P'];zero=s['zero'];candidate=here.parent/'adaptive-first-root-factor87/candidate.json';raw=candidate.read_bytes();assert hashlib.sha256(raw).hexdigest()=='da6b88365da3ec9db6040373c25de20b30baf63edc9fdf742de2aa4b2c06e6e8';j=json.loads(raw);assert len(j['source'])==87
names=j['witnesses']+j['fixed_numerals'];g={}
for idx,n in enumerate(names):
 e=list(zero);e[idx]=1;g[n]=P({tuple(e):1})
for name,op,a,b in j['source']:
 if name in ['g86','g87','g88','P13']:continue
 x=P.coerce(a) if isinstance(a,int) else g[a];y=P.coerce(b) if isinstance(b,int) else g[b]
 g[name]=x+y if op=='+' else x-y if op=='-' else x*y
assert j['source'][-4:]==[['g86','*','F0','F1'],['g87','*','Fa','g86'],['g88','*','Fs','g87'],['P13','-','g88',1]]
cert=[('F0',15,{'J':9,'X':2,'Y':2,'eta':2},(9,0,0,0),-2),
      ('F1',13,{'J':4,'X':2,'Y':5,'eta':1,'gamma':1},(4,0,0,0),8),
      ('Fa',13,{'J':4,'f':4,'X':2,'Y':2,'u':1},(4,0,0,0),2),
      ('Fs',10,{'i':2,'Y':4,'eta':4},(0,0,0,0),1)]
for name,degree,monomial,ports,coefficient in cert:
 poly=g[name].d;assert max(sum(e[:13]) for e in poly)==degree
 key=tuple(monomial.get(n,0) for n in names[:13]);terms={e[13:]:c for e,c in poly.items() if e[:13]==key};assert terms=={ports:coefficient},(name,terms)
 print(name,'degree',degree,'witness monomial',monomial,'coefficient',coefficient,'port exponents',ports)
beta=(2**47)**2011-1;assert beta>0
print('PASS: exact factored-87 factor degrees 15,13,13,10; product-minus-one degree 51; positive shift preserves degree')
