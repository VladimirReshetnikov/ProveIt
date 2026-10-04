#!/usr/bin/env python3
"""Data-only independent exact polynomial interpretation. Imports no packet code."""
import collections, hashlib, json, pathlib
QA=pathlib.Path(__file__).resolve().parent
ROOT=QA/'authenticated_extraction'/'literal-turmite-endpoint-release-20261003'
u,x0,v,y0=481238074400,481225262775,576000,29948
# A monomial is a sorted tuple of (symbol, positive exponent) pairs.
class P:
 def __init__(self, terms): self.t={m:c for m,c in terms.items() if c}
 @staticmethod
 def constant(n): return P({():n})
 @staticmethod
 def variable(n): return P({((n,1),):1})
 def __add__(self,b):
  if isinstance(b,int):b=P.constant(b)
  t=self.t.copy()
  for m,c in b.t.items(): t[m]=t.get(m,0)+c
  return P(t)
 __radd__=__add__
 def __neg__(self): return P({m:-c for m,c in self.t.items()})
 def __sub__(self,b): return self+(-P.constant(b) if isinstance(b,int) else -b)
 def __rsub__(self,b): return P.constant(b)+(-self)
 def __mul__(self,b):
  if isinstance(b,int):b=P.constant(b)
  t={}
  for ma,ca in self.t.items():
   for mb,cb in b.t.items():
    d=collections.Counter(dict(ma)); d.update(dict(mb)); m=tuple(sorted(d.items())); t[m]=t.get(m,0)+ca*cb
  return P(t)
 __rmul__=__mul__
 def __pow__(self,n):
  assert type(n) is int and n>=0
  out=P.constant(1); a=self
  while n:
   if n&1:out=out*a
   a=a*a; n//=2
  return out
 def __eq__(self,b): return self.t==b.t
 def exact_degree_certificate(self):
  # Ignoring formal Z gives an upper bound. A nonzero modular coefficient
  # at that degree certifies it survives the exact specialization Z=3.
  groups={}
  for m,c in self.t.items():
   actual=tuple((s,e) for s,e in m if s!='Z'); z=dict(m).get('Z',0)
   groups.setdefault(actual,{}).setdefault(z,0); groups[actual][z]+=c
  degree=max(sum(e for s,e in m) for m in groups)
  for actual,terms in groups.items():
   if sum(e for s,e in actual)!=degree:continue
   for modulus in (1000000007,1000000009,998244353):
    residue=sum(c*pow(3,e,modulus) for e,c in terms.items())%modulus
    if residue:return {'degree':degree,'actual_monomial':actual,'formal_Z_coefficient':sorted(terms.items()),'nonzero_modulus':modulus,'nonzero_residue':residue}
  raise AssertionError('No surviving leading-degree coefficient proved')
Z=P.variable('Z'); K=Z**x0; C=Z**u-1; D=C-1
out=[]
for path in sorted(ROOT.glob('endpoint_*_source.json')):
 s=json.loads(path.read_text()); paid='paid_numerals' in path.name; five='five_witness' in path.name; folded='folded' in path.name
 witnesses=['U','V','Uq','Vq','BoundCol'] if five else ['HxPlus','HyPlus','BoundCol']
 assert s['new_positive_witnesses']==witnesses
 assert s['existing_relation_ports']==['W','FinalHead','FinalSignPlus']
 assert s['literal_ports']==(['1','3'] if paid else ['1'])
 recipes={} if paid else {'K':{'base':3,'exponent':x0},'C':{'base':3,'exponent':u,'subtract':1},**({'D':{'base':3,'exponent':u,'subtract':2}} if folded or five else {})}
 assert s['fixed_numeral_recipes']==recipes
 ports=s['existing_relation_ports']+witnesses; variables={p:P.variable(p) for p in ports}
 values={'1':P.constant(1),**variables,**({'3':Z} if paid else {n:{'K':K,'C':C,'D':D}[n] for n in recipes})}
 deps={}; operations=collections.Counter()
 for g in s['gates']:
  assert set(g)=={'out','op','args'} and g['out'] not in values
  assert g['op'] in ('mul','add','sub') and len(g['args'])==2 and all(type(a) is str and a in values for a in g['args'])
  a,b=(values[n] for n in g['args']); values[g['out']]={'mul':lambda:a*b,'add':lambda:a+b,'sub':lambda:a-b}[g['op']]()
  deps[g['out']]=g['args']; operations[g['op']]+=1
 W=variables['W']; B=variables['BoundCol']; FH=variables['FinalHead']; FS=variables['FinalSignPlus']; A=W**v; T=W**y0
 if five:
  U,V,Uq,Vq=(variables[n] for n in ('U','V','Uq','Vq'))
  expected=[U+C-1-C*Uq,V+A-2-(A-1)*Vq,K*U+B-W,K*U*T*V-FH,FS-1]
 else:
  U=1+C*(variables['HxPlus']-1); V=1+(A-1)*(variables['HyPlus']-1)
  expected=[K*U+B-W,K*U*T*V-FH,FS-1]
 actual=[values[a]-values[b] for a,b in s['equalities']]
 assert actual==expected
 targets=s['power_targets']; assert set(targets)=={'K','ThreeToU','T','WToV'}
 assert values[targets['K']]==K and values[targets['T']]==T and values[targets['WToV']]==A
 assert (values[targets['ThreeToU']]==Z**u) if paid else (targets['ThreeToU'] is None)
 live=set()
 def visit(n):
  if n in live:return
  live.add(n)
  for child in deps.get(n,[]):visit(child)
 for a,b in s['equalities']:visit(a);visit(b)
 assert set(deps)<=live
 const_end,var_end,total=s['section_ends']; assert total==len(s['gates'])
 assert var_end-const_end==32
 assert all(g['op']=='mul' for g in s['gates'][const_end:var_end])
 sections=[]
 for a,b in ((0,const_end),(const_end,var_end),(var_end,total)):
  c=collections.Counter(g['op'] for g in s['gates'][a:b]);sections.append({'M':c['mul'],'A':c['add']+c['sub'],'total':b-a})
 assert sections[0]==({'M':57,'A':2 if folded or five else 1,'total':59 if folded or five else 58} if paid else {'M':0,'A':0,'total':0})
 assert sections[1]=={'M':32,'A':0,'total':32}
 assert sections[2]=={'M':5,'A':5 if folded or five else 6,'total':10 if folded or five else 11}
 counts={'M':operations['mul'],'A':operations['add']+operations['sub'],'total':total}
 assert counts==({'M':94,'A':7,'total':101} if paid else {'M':37,'A':5 if folded or five else 6,'total':42 if folded or five else 43})
 cert=[p.exact_degree_certificate() for p in actual]
 assert [c['degree'] for c in cert]==([1,576001,1,29950,1] if five else [1,605950,1])
 out.append({'source':path.name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'counts':counts,'section_ledgers':sections,'witnesses':witnesses,'equations':len(actual),'all_gates_acyclic_and_live':True,'exact_symbolic_equations_match':True,'degree_certificates':cert})
assert len(out)==6
assert ((481225262850-75)%u,(288650-258702)%v)==(x0,y0)
assert ((75-75),(288650-288650))==(0,0)
assert (u%2,v%2,x0%2,y0%2)==(0,0,1,0)
report={'status':'PASS_EXTERNAL_DATA_ONLY_DAG_CHECK','packet_modules_imported':False,'all_six_DAGs_interpreted_gate_by_gate':True,'exact_integer_polynomial_comparison_in_formal_Z':True,'formal_Z_specialized_to':3,'no_giant_coefficient_materialization':True,'sources':out}
(QA/'independent_dag_check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'sources':len(out),'counts':[s['counts'] for s in out]},indent=2))
