"""Independent ordinary-substitution + modus ponens checker. No imports from search code."""
import json,itertools
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def parse(s,namespace='t'):
 def p(pos):
  assert pos<len(s)
  if s[pos]=='C':
   a,q=p(pos+1); b,r=p(q); return ('imp',a,b),r
  assert s[pos].islower()
  return namespace+s[pos],pos+1
 t,k=p(0); assert k==len(s); return t

def leaves(t):
 return {t} if isinstance(t,str) else leaves(t[1])|leaves(t[2])

def replace(t,key,val):
 if isinstance(t,str):return val if t==key else t
 return ('imp',replace(t[1],key,val),replace(t[2],key,val))

def subst(t,m):
 if isinstance(t,str):
  return subst(m[t],m) if t in m else t
 return ('imp',subst(t[1],m),subst(t[2],m))

def solve(equations):
 # Goal variables t* are rigid; the disjoint premise namespaces m*/n* are flexible.
 env={};todo=list(equations)
 while todo:
  a,b=todo.pop(0)
  a,b=subst(a,env),subst(b,env)
  if a==b:continue
  af=isinstance(a,str) and a[0] in 'mn'
  bf=isinstance(b,str) and b[0] in 'mn'
  if af or bf:
   if not af:a,b=b,a
   assert a not in leaves(b),('occurs check',a,b)
   env[a]=b
  else:
   assert isinstance(a,tuple) and isinstance(b,tuple),('rigid mismatch',a,b)
   todo.extend([(a[1],b[1]),(a[2],b[2])])
 return {x:subst(v,env) for x,v in env.items()}

def fmt(t):
 return t if isinstance(t,str) else '('+fmt(t[1])+' -> '+fmt(t[2])+')'

def truth(t,v):
 return v[t] if isinstance(t,str) else not truth(t[1],v) or truth(t[2],v)

def count(t):return 0 if isinstance(t,str) else 1+count(t[1])+count(t[2])
def dag(t):return set() if isinstance(t,str) else {t}|dag(t[1])|dag(t[2])

rows=json.loads((ROOT/'H_PW_certificate.json').read_text());past={};audit=[]
assert rows[0]['polish']=='CCpqCCqrCpr'
assert rows[1]['polish']=='CCCpqpCrp'
for row in rows:
 goal=parse(row['polish']);vs=sorted(leaves(goal))
 assert all(truth(goal,dict(zip(vs,bits))) for bits in itertools.product([False,True],repeat=len(vs)))
 if row['parents'] is not None:
  major_id,minor_id=row['parents']
  assert major_id<row['id'] and minor_id<row['id']
  major=parse(past[major_id],'m');minor=parse(past[minor_id],'n')
  assert leaves(major).isdisjoint(leaves(minor))
  assert major[0]=='imp'
  env=solve([(major[1],minor),(major[2],goal)])
  mi=subst(major,env);ni=subst(minor,env)
  assert mi[1]==ni and mi[2]==goal
  audit.append({'id':row['id'],'parents':row['parents'],'substitution':{k:fmt(v) for k,v in sorted(env.items())},'major_instance':fmt(mi),'minor_instance':fmt(ni),'conclusion':fmt(goal),'ordinary_mp_verified':True})
 past[row['id']]=row['polish']
assert rows[9]['polish']=='CCCpqpp'
assert rows[11]['polish']=='CpCqp'
a,b=map(lambda x:parse(x['polish']),rows[:2])
report={'status':'PASS','schema_semantics':'Arbitrary formulas may replace schematic variables; no restriction to propositional atoms. Each CD line is replayed as explicit substitutions followed by ordinary modus ponens.','fresh_variable_namespaces':True,'occurs_checks':True,'boolean_tautology_check_all_rows':True,'axioms':[fmt(a),fmt(b)],'tree_constructor_counts':[count(a),count(b)],'shared_dag_constructor_count':len(dag(a)|dag(b)),'total_cd_steps':len(audit),'peirce_line':10,'k_line':12,'steps':audit}
(ROOT/'H_PW_VERIFIED.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS: 10 independently replayed explicit-substitution + MP steps; K and Peirce derived; DAG=8, tree=9.')
for r in audit: print(r['id'],r['conclusion'])
