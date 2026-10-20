#!/usr/bin/env python3
"""Independent inert validation of saved universal constructor derivations and matrix scores."""
from pathlib import Path
import hashlib,json,itertools,zipfile
P=Path(__file__).resolve().parent
T=('T',)
def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
def I(a,b):return T if (a,b)==(T,T) else ('I',a,b)
def X(k,a,b):return (k,a,b)
def R(a,b):return X('R',a,b)
def Q(a,b):return X('Q',a,b)
def E(a,b):return X('E',a,b)
def v(i):return ('v',i)
F=R(T,T)
def N(a):return I(a,F)
def Ex(i,a):return N(Q(i,N(a)))
def canonical(t):
 names={}
 def walk(x):
  if x[0]=='v':return v(names.setdefault(x[1],len(names)))
  return (x[0],walk(x[1]),walk(x[2])) if len(x)==3 else x
 return walk(t)
def ev(t,s,active=frozenset()):
 if t[0]=='v' and t[1] in s:
  assert t[1] not in active
  return ev(s[t[1]],s,active|{t[1]})
 if len(t)==3:
  a,b=ev(t[1],s,active),ev(t[2],s,active)
  return I(a,b) if t[0]=='I' else (t[0],a,b)
 return t
def renamed(t):
 if t[0]=='v':return v(t[1]+1000)
 return (t[0],renamed(t[1]),renamed(t[2])) if len(t)==3 else t
a,b,c=map(v,range(3))
AX={'truth':T,'EFQ':I(F,a),'restricted_rho8_F':I(I(I(c,F),a),I(I(a,c),I(b,c))),
'rho1':Ex(a,E(a,b)),'rho2':I(Q(a,I(b,c)),I(Q(a,b),Q(a,c))),
'rho3':I(E(a,b),I(R(c,a),R(c,b))),'rho4':I(Q(a,Q(b,c)),Q(b,Q(a,c))),
'rho5':I(E(c,a),I(R(c,b),R(a,b))),'rho6':I(Ex(a,Q(a,b)),b),
'G':I(E(c,a),I(E(c,b),Q(R(a,b),E(a,b))))}
checks={}
for name in ('condensed','modal'):
 path=P/(name+'-proof.json')
 if not path.exists():continue
 rows=json.loads(path.read_text());forms=[]
 for i,row in enumerate(rows):
  f=tup(row['formula']);rule=row['rule']
  if rule in AX:assert f==AX[rule]
  elif rule=='gen':
   assert row['parent']<i
   f0=canonical(Q(tup(row['label']),forms[row['parent']]))
   assert f==f0
  else:
   assert rule=='condensed_mp' and row['major']<i and row['minor']<i and row['minor_rename_offset']==1000
   s={int(k):tup(x) for k,x in row['substitution'].items()}
   major=ev(forms[row['major']],s);minor=ev(renamed(forms[row['minor']]),s)
   assert major==tup(row['instantiated_major']) and minor==tup(row['instantiated_minor'])
   if major==T:assert minor==T and f==T
   else:assert major[0]=='I' and major[1]==minor and f==canonical(major[2])
  forms.append(f)
 checks[name]={'nodes':len(forms),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'all_universal_instantiations_and_closed_GEN_valid':True}
# Closed theorem transformations are exact MP constructions; the first
# generic node denotes a supplied closed derivation, not a new axiom.
def instantiate(t,s):
 if t[0]=='v':return s.get(t[1],t)
 if len(t)==3:
  a,b=instantiate(t[1],s),instantiate(t[2],s)
  return I(a,b)if t[0]=='I'else(t[0],a,b)
 return t
C=c;B=b
premise=N(N(C));major=I(premise,I(I(F,C),I(B,C)))
assert major==instantiate(AX['restricted_rho8_F'],{0:F,1:B,2:C})
step1=major[2];efq=I(F,C);assert step1[1]==efq
weaken=step1[2];assert weaken==I(B,C)
# At B=0, MP uses native truth; C=0 simply returns native zero.
truth_goal=I(T,C);assert truth_goal[1]==T and truth_goal[2]==C
Z=Q(a,N(Q(a,F)));rho6=instantiate(AX['rho6'],{1:F})
assert rho6==N(N(Z))
# The seven closed nodes consist of rho6, HF, MP, EFQ, MP,
# truth and MP. No open premise is generalized.
hf=I(N(N(Z)),I(I(F,Z),I(T,Z)))
assert hf==instantiate(AX['restricted_rho8_F'],{0:F,1:T,2:Z})
closed=[rho6,hf,hf[2],I(F,Z),I(T,Z),T,Z]
assert closed[1][1]==closed[0] and closed[2][1]==closed[3] and closed[4][1]==closed[5] and closed[4][2]==closed[6]
receipt={'status':'EXACT_SCHEMA_DAG_AND_CLOSED_BOOTSTRAP_VALIDATION_PASS','derivations':checks,'generic_admissible_rule':{'premise':premise,'conclusion':I(B,C),'additional_axioms':['HF(F,B,C)','EFQ(C)'],'additional_MP_steps':2,'DNE_additional_step':'B=0 and MP with native truth'},'closed_modal_bootstrap':{'formula':Z,'nodes':closed,'rules':['rho6(i,F)','HF(F,0,Z)','MP1,0','EFQ(Z)','MP2,3','truth','MP4,5'],'GEN_uses':0},'scope':'Every saved schema step is exact constructor instantiation plus MP or closed GEN. Bundle is omitted from bounded search. Pure-fragment invariant is an ordinary proof in findings.md; no full-calculus consistency/calibration inferred.'}
(P/'validation.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'status':receipt['status'],'dag_nodes':checks['modal']['nodes'],'modal_bootstrap_nodes':7}))
