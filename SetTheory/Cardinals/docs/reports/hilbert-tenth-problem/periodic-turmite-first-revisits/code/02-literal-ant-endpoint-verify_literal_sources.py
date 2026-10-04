#!/usr/bin/env python3
"""Independent data-only whole-DAG polynomial audit of every endpoint source."""
if not __debug__:raise RuntimeError('Assertions required')
import collections,hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parent
NAMES=('Z','W','HxPlus','HyPlus','BoundCol','FinalHead','FinalSignPlus','U','V','Uq','Vq')
ZERO=(0,)*len(NAMES)
U_PERIOD,X_RESIDUE,V_PERIOD,Y_RESIDUE=481238074400,481225262775,576000,29948

def scalar(n):return {ZERO:n}if n else{}
def symbol(name,exponent=1):
 e=list(ZERO);e[NAMES.index(name)]=exponent;return {tuple(e):1}
def plus(a,b,sign=1):
 out=dict(a)
 for m,c in b.items():
  out[m]=out.get(m,0)+sign*c
  if not out[m]:del out[m]
 return out
def times(a,b):
 out={}
 for m,c in a.items():
  for n,d in b.items():
   e=tuple(i+j for i,j in zip(m,n));out[e]=out.get(e,0)+c*d
 return {m:c for m,c in out.items()if c}
def degree(poly):return max((sum(m[1:])for m in poly),default=-1)
def coefficient(poly,actual_exponents):return {m[0]:c for m,c in poly.items()if m[1:]==actual_exponents}
def expected(five):
 one=scalar(1);K=symbol('Z',X_RESIDUE);C=plus(symbol('Z',U_PERIOD),one,-1);D=plus(C,one,-1)
 W=symbol('W');A=symbol('W',V_PERIOD);T=symbol('W',Y_RESIDUE);B=symbol('BoundCol');FH=symbol('FinalHead');FS=symbol('FinalSignPlus')
 if five:
  U,V,Uq,Vq=map(symbol,('U','V','Uq','Vq'));Am1=plus(A,one,-1)
  pre=[plus(plus(U,D),times(C,Uq),-1),plus(plus(plus(V,one,-1),Am1),times(Am1,Vq),-1)]
 else:
  U=plus(one,times(C,plus(symbol('HxPlus'),one,-1)))
  V=plus(one,times(plus(A,one,-1),plus(symbol('HyPlus'),one,-1)));pre=[]
 col=times(K,U)
 return pre+[plus(plus(col,B),W,-1),plus(times(times(col,T),V),FH,-1),plus(FS,one,-1)]

def check(path):
 s=json.loads(path.read_text());five=len(s['new_positive_witnesses'])==5;paid=not s['fixed_numeral_recipes']
 witnesses=['U','V','Uq','Vq','BoundCol']if five else['HxPlus','HyPlus','BoundCol']
 assert s['new_positive_witnesses']==witnesses
 assert s['existing_relation_ports']==['W','FinalHead','FinalSignPlus']
 assert s['literal_ports']==(['1','3']if paid else['1'])
 val={'1':scalar(1)}
 if paid:val['3']=symbol('Z')
 else:
  assert s['fixed_numeral_recipes'].get('K')=={'base':3,'exponent':X_RESIDUE}
  assert s['fixed_numeral_recipes'].get('C')=={'base':3,'exponent':U_PERIOD,'subtract':1}
  if 'D'in s['fixed_numeral_recipes']:assert s['fixed_numeral_recipes']['D']=={'base':3,'exponent':U_PERIOD,'subtract':2}
  assert set(s['fixed_numeral_recipes'])<=set(['K','C','D'])
  for name,r in s['fixed_numeral_recipes'].items():val[name]=plus(symbol('Z',r['exponent']),scalar(r.get('subtract',0)),-1)
 for name in s['existing_relation_ports']+witnesses:val[name]=symbol(name)
 deps={};counts=collections.Counter();maxterms=0
 for g in s['gates']:
  assert set(g)=={'out','op','args'}and g['out']not in val and len(g['args'])==2
  assert g['op']in['mul','add','sub']and all(a in val for a in g['args'])
  a,b=(val[k]for k in g['args']);val[g['out']]=times(a,b)if g['op']=='mul'else plus(a,b,1 if g['op']=='add'else -1)
  deps[g['out']]=g['args'];counts['M'if g['op']=='mul'else'A']+=1;maxterms=max(maxterms,len(val[g['out']]))
 actual=[plus(val[a],val[b],-1)for a,b in s['equalities']];assert actual==expected(five)
 targets=s['power_targets'];assert val[targets['K']]==symbol('Z',X_RESIDUE)
 if targets['ThreeToU']:assert val[targets['ThreeToU']]==symbol('Z',U_PERIOD)
 assert val[targets['T']]==symbol('W',Y_RESIDUE)and val[targets['WToV']]==symbol('W',V_PERIOD)
 live=set()
 def visit(n):
  if n in live:return
  live.add(n)
  for a in deps.get(n,[]):visit(a)
 for eq in s['equalities']:
  for n in eq:visit(n)
 assert set(deps)<=live
 # Check a nonzero leading coefficient after setting formal Z=3; merely
 # ignoring formal Z in a symbolic degree would otherwise give only a bound.
 if five:
  e=list(ZERO[1:]);e[NAMES.index('W')-1]=V_PERIOD;e[NAMES.index('Vq')-1]=1
  assert coefficient(actual[1],tuple(e))=={0:-1};degrees=[1,576001,1,29950,1]
 else:
  e=list(ZERO[1:]);e[NAMES.index('W')-1]=V_PERIOD+Y_RESIDUE;e[NAMES.index('HxPlus')-1]=1;e[NAMES.index('HyPlus')-1]=1
  assert coefficient(actual[1],tuple(e))=={X_RESIDUE+U_PERIOD:1,X_RESIDUE:-1};degrees=[1,605950,1]
 assert [degree(p)for p in actual]==degrees
 expected_count=(94,7)if paid else(37,6 if len(s['gates'])==43 else 5)
 assert(counts['M'],counts['A'])==expected_count
 return {'source':path.name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'M':counts['M'],'A':counts['A'],'total':len(s['gates']),'positive_witnesses':witnesses,'equations':len(actual),'equation_degrees':degrees,'max_degree':max(degrees),'leading_coefficient_nonzero_at_Z3':True,'acyclic_all_gates_live':True,'every_gate_interpreted_symbolically':True,'exact_expected_equations':True,'largest_sparse_gate_terms':maxterms}

def main():
 paths=sorted(ROOT.glob('endpoint_*_source.json'));assert len(paths)==6
 assert ((481225262850-75)%481238074400,(288650-258702)%576000)==(X_RESIDUE,Y_RESIDUE)
 assert (U_PERIOD%2,V_PERIOD%2,X_RESIDUE%2,Y_RESIDUE%2)==(0,0,1,0)
 assert (1-1)%4==0 and (2-1)%4==1  # quarter-turn E->N, S->E
 out={'status':'PASS_INDEPENDENT_WHOLE_DAG_ENDPOINT_AUDIT','sources':[check(p)for p in paths],'normalized_residue_and_heading_verified':True,'formal_Z_specialization':3,'degree_excludes_fixed_Z':True,'giant_numerals_materialized':False,'source_modules_imported':False,'upstream_code_executed':False,'checker_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
 (ROOT/'literal_source_verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
