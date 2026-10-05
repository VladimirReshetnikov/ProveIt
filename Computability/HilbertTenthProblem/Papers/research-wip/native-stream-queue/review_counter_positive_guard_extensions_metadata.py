#!/usr/bin/env python3
"""Fresh review mathematics and inert source matching; no array interpreter."""
from pathlib import Path
from fractions import Fraction
from math import prod,lcm
import hashlib,json

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs')
WIP=ROOT/'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
PINS={
 '/tmp/residue_affine_complement_reuse.md':'4bde0d333a56da85f66e05ff4607fa1bfdba49fdf057df1e735814a7bcae34af',
 '/tmp/residue_affine_complement_reuse.py':'810a9e2572d2efd075dcfcd7d5e024a90ad3d4c4aac588d3adc9860be935871d',
 '/tmp/residue_affine_complement_reuse.json':'3809b7765209043c3de7afbdc7188b237b4a68b9162f59ddc34ece91262d7673',
 '/tmp/counter_vector_positive_guard.md':'f4253a97fa9c03f1c38911fac754dfc41d1faaf55d4cd4b313257cd3a5c33453',
 str(WIP/'residue_affine_factored_counter_step.md'):'60250f0f6d12f7583b5de747c82d0d91205eab98ca0f4095992d458aaf8a951f',
 str(WIP/'residue_affine_factored_counter_step.py'):'0dcc6e5d4cf306037d343d7aaed8183f920c2b9e15e1b31757aadcf4606feb8a',
 str(WIP/'residue_affine_factored_counter_step.json'):'fc8c20c02a28edcb6eaa3eed27128e282ea3835c88fc313d907c91e6e733b282',
 str(WIP/'markov_positive_guard_savings.md'):'901accac868c13967883c56ff5b5a949ef42fcfd82a470999f042272ead8dc15'}
def check(ok,msg):
 if not ok:raise RuntimeError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()
deps={}
for name,expected in PINS.items():
 b=Path(name).read_bytes();check(digest(b)==expected,name)
 deps[name]={'sha256':expected,'bytes':len(b),'lines':len(b.splitlines())}
a=json.loads(Path('/tmp/residue_affine_complement_reuse.json').read_bytes())
prior=json.loads((WIP/'residue_affine_factored_counter_step.json').read_bytes())['counter']
check(a['helper_sha256']==PINS['/tmp/residue_affine_complement_reuse.py'],'self pin')
K=11;primes=[2,3,5]
instructions={1:['dec',0,2,3],2:['inc',1,1],3:['dec',1,4,5],4:['inc',2,3],5:['dec',2,5,6],6:['inc',0,6]}
for j in range(7,12):instructions[j]=['inc',0,j]
check(a['instructions']=={str(k):v for k,v in instructions.items()},'instruction table')
branches=[]
for state,ins in instructions.items():
 p=primes[ins[1]]
 types=[('inc',p,1,ins[2])] if ins[0]=='inc' else [('dec',1,p,ins[2]),('zero',1,1,ins[3])]
 for kind,A,D,O in types:
  branches.append(dict(I=state,A=A,D=D,E=A*(K-state)-D*(K-O),p=p,kind=kind,target=O))
check(branches==a['branches'],'branches')
B=len(branches);check(B==14 and a['K']==K and a['B']==B,'parameters')
# Independent direct Lagrange coefficients, not the author's Newton routine.
rat={}
for key in ['I','A','D','E','p']:
 coefficients=[Fraction(0)]*B
 for j,branch in enumerate(branches,1):
  numerator=[1];denominator=1
  for k in range(1,B+1):
   if k==j:continue
   nxt=[0]*(len(numerator)+1)
   for t,c in enumerate(numerator):nxt[t]-=k*c;nxt[t+1]+=c
   numerator=nxt;denominator*=j-k
  for t,c in enumerate(numerator):coefficients[t]+=Fraction(branch[key]*c,denominator)
 rat[key]=coefficients
L=lcm(*(v.denominator for cs in rat.values() for v in cs))
coeffs={key:[int(L*c) for c in cs] for key,cs in rat.items()}
check(L==a['L']==prior['interpolation_denominator'],'denominator')
check(coeffs==a['coefficient_rows']==prior['coefficient_rows'],'all coefficient rows')
# Literal new-array reconstruction only. No source row is evaluated.
expected=[];table={}
for key in ['I','A','D','E','p']:
 cs=coeffs[key];previous=cs[-1]
 for j in range(B-2,-1,-1):
  pname=f'{key}_product_{j}';sname=f'{key}_sum_{j}'
  expected.extend([[pname,'*',previous,'z'],[sname,'+',pname,cs[j]]]);previous=sname
 table[key]=previous
I,A,D,E,p=[table[key] for key in ['I','A','D','E','p']]
expected += [
 ['selector','+','z','v'],['Ln','*',L,'n'],['LKP','*',L*K,'P'],
 ['input_lhs','+','Ln',L*K],['input_rhs','+','LKP',I],
 ['output_lhs','*',D,'y'],['An','*',A,'n'],['output_rhs','+','An',E],
 ['S','+',A,D],['pL','+',p,L],['H','-','pL','S'],['HP','*','H','P'],
 ['HP_plus_S','+','HP','S'],['HP_plus_S_plus_V','+','HP_plus_S','V'],
 ['guard_lhs','-','HP_plus_S_plus_V',2*L],['guard_rhs','*',p,'Q'],['complement','+','U','V']]
sides=[['selector',B+1],['input_lhs','input_rhs'],['output_lhs','output_rhs'],['guard_lhs','guard_rhs'],['complement',p]]
graph_rows=len(expected)
for i,(left,right) in enumerate(sides):expected.append([f'residual_{i}','-',left,right])
for i in range(5):expected.append([f'square_{i}','*',f'residual_{i}',f'residual_{i}'])
for i in range(1,5):expected.append([f'join_{i}','+',f'join_{i-1}' if i>1 else 'square_0',f'square_{i}'])
check(expected==a['source'] and sides==a['equation_sides'],'all literal rows and sides')
ports=['n','y','z','v','P','Q','U','V'];check(a['ports']==ports,'ports')
check(a['positive_witnesses']==ports[2:] and a['external_positive_integer_ports']==ports[:2],'domain')
check(a['residuals']==[f'residual_{i}' for i in range(5)] and a['output']=='join_4','finalizer')
seen=set(ports);parents={}
for dst,op,l,r in expected:
 check(dst not in seen and op in ['+','-','*'] and all(type(v)is int or v in seen for v in [l,r]),'topology')
 seen.add(dst);parents[dst]=[v for v in [l,r] if isinstance(v,str)]
live=set();stack=['join_4']
while stack:
 x=stack.pop()
 if x in live:continue
 live.add(x);stack+=parents.get(x,[])
check(live==seen,'liveness')
counts=lambda rows:dict(M=sum(r[1]=='*' for r in rows),A=sum(r[1]!='*' for r in rows),total=len(rows))
check(counts(expected[:graph_rows])==a['graph_counts']==dict(M=71,A=76,total=147),'graph count')
check(counts(expected)=={k:a['polynomial_counts'][k] for k in ['M','A','total']}==dict(M=76,A=85,total=161),'SOS count')
# Independent polynomial algebra of the five handwritten equations.
zero=(0,)*8
def const(c):return {zero:c} if c else {}
def var(j):return {tuple(int(k==j) for k in range(8)):1}
def plus(*terms):
 out={}
 for p in terms:
  for m,c in p.items():out[m]=out.get(m,0)+c
 return {m:c for m,c in out.items() if c}
def scale(k,p):return {m:k*c for m,c in p.items() if k*c}
def times(p,q):
 out={}
 for m,c in p.items():
  for n,d in q.items():
   a=tuple(x+y for x,y in zip(m,n));out[a]=out.get(a,0)+c*d
 return {m:c for m,c in out.items() if c}
def enc(p):return [[list(m),c] for m,c in sorted(p.items())]
n,y,z,v,P,Q,U,V=map(var,range(8))
polys={key:{(0,0,j,0,0,0,0,0):c for j,c in enumerate(cs) if c} for key,cs in coeffs.items()}
I,A,D,E,p=[polys[key] for key in ['I','A','D','E','p']]
S=plus(A,D);H=plus(p,const(L),scale(-1,S))
newguard=plus(times(H,P),S,V,const(-2*L),scale(-1,times(p,Q)))
c=plus(U,V,scale(-1,p));oldguard=plus(newguard,scale(-1,c))
res=[plus(z,v,const(-B-1)),plus(scale(L,n),const(L*K),scale(-L*K,P),scale(-1,I)),plus(times(D,y),scale(-1,times(A,n)),scale(-1,E)),newguard,c]
check([enc(p) for p in res]==a['residual_coefficients'],'five formula coefficient dictionaries')
new=plus(*(times(p,p) for p in res));old=plus(*(times(p,p) for p in res[:3]),times(oldguard,oldguard),times(c,c))
correction=plus(scale(2,times(oldguard,c)),times(c,c))
check(plus(new,scale(-1,old))==correction,'formal full correction')
check(enc(new)==a['full_output_coefficients'],'all full-output formula coefficients')
check(max(map(sum,new))==a['polynomial_counts']['exact_degree']==28,'exact degree')
check(coeffs['p'][-1]-coeffs['A'][-1]-coeffs['D'][-1]==5447,'H leader')
out={'schema':'independent-counter-positive-guard-extensions-review-v1','dependencies':deps,
 'scalar':{'K':K,'B':B,'L':L,'direct_lagrange_rows':5,'table_entries':70,'literal_rows_matched':161,
 'graph_counts':counts(expected[:graph_rows]),'polynomial_counts':counts(expected),'rows_and_ports_live':True,
 'formal_residual_term_counts':[len(p) for p in res],'full_formula_terms':len(new),'exact_degree':28,'H_leading_coefficient':5447,
 'full_formula_matches_saved_coefficients':True,'formal_correction_verified':True,
 'saved_arrays_executed':False,'author_cases_replayed':False},
 'vector':{'scope':'complete proof-only template challenge; no emitted vector array executed',
 'graph_total':'2(r+2)K+4r+4','SOS_total':'2(r+2)K+7r+11','witnesses':2,'equations':'r+3',
 'degree_upper':'2K+2','Boolean_guard_saving':{'M':2,'A':1,'total':3},'unbounded_iteration_paid':False},
 'review_scope':{'author_and_vector_notes_read_fully':True,'author_helper_200_lines_read_inertly':True,
 'parent_note_read_fully':True,'parent_helper_read_spans':[[45,58],[114,122]],
 'external_universality_rechecked':False,'universal_polynomial_claim':False,'repository_mutation':False},'status':'PASS'}
Path('/tmp/review_counter_positive_guard_extensions.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','literal_rows':len(expected),'full_formula_terms':len(new),'residual_terms':[len(p) for p in res]}))
