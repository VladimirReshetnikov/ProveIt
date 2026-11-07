#!/usr/bin/env python3
"""Independently traverse the finite syntactic candidate tree; no Lean."""
import collections,hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-sextic-positive-cut-survey';S=D/'research/nine-sharing-sign31-sextic-candidate/seed.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P/'survey.py')=='2a697e8b254011a6d33a777aeec71f24ae4b805aa4eb93dd11b0161e1d0dfda4' and sha(P/'result.json')=='b6d4a736e8425fd70426d195bb36ecc7665f2885ab185174810dbb9963c4d434' and sha(S)=='827740a7f65961bd1a04ae424f4c8873a636285d2b1410bb72d0bee7e3e9e6c1'
s=json.loads(S.read_bytes());ports=set(s['coefficient_binding']['ports'])
def subst(t,k,r):
 if t[0]=='var':return r if t[1]==k else t[:]
 if t[0] in ('num','port'):return t[:]
 assert t[0] in ('add','sub','mul') and len(t)==3
 return [t[0],subst(t[1],k,r),subst(t[2],k,r)]
def degree(t):
 if t[0]=='var':return 1
 if t[0] in ('num','port'):return 0
 d,e=degree(t[1]),degree(t[2]);return d+e if t[0]=='mul' else max(d,e)
def natural(t):
 if t[0]=='var':return type(t[1])==int and 0<=t[1]<=31
 if t[0]=='port':return t[1] in ports
 if t[0]=='num':return type(t[1])==int and t[1]>=0
 return t[0] in ('add','mul') and natural(t[1]) and natural(t[2])
queue=collections.deque([(s['residuals'],())]);term=[];visits=0;root_choices=[]
while queue:
 rows,path=queue.popleft();visits+=1;successors=[]
 for i,row in enumerate(rows):
  e=row['expr'];
  if row['kind']!='positive' or e[0]!='sub' or e[1][0]!='var' or not natural(e[2]):continue
  k=e[1][1];assert subst(e[2],k,['num',-1])==e[2]
  new=[dict(r,expr=subst(r['expr'],k,e[2])) for j,r in enumerate(rows) if i!=j]
  if all(degree(r['expr'])<=3 for r in new):successors.append((new,path+(row['gate'],)))
 if not path:root_choices=[p[-1] for _,p in successors]
 if successors:queue.extend(successors)
 else:term.append(path)
expected=json.loads((P/'result.json').read_text());assert expected['status']=='PASS_RESTRICTED_SYNTACTIC_ENUMERATION' and visits==expected['visited_sequence_nodes']==27 and sorted(map(list,term))==expected['terminal_paths'] and len(term)==12 and {len(p) for p in term}=={3} and {frozenset(p) for p in term}=={frozenset(('X','c2','normalized_S2')),frozenset(('X','Dc2','normalized_S2'))}
x=subprocess.run([sys.executable,'-I','-S','-B',str(P/'survey.py')],capture_output=True,check=True,timeout=30);assert not x.stderr and x.stdout==(P/'result.json').read_bytes()
print(json.dumps({'status':'PASS_RESTRICTED_SURVEY','visited_sequence_nodes':visits,'terminal_paths':len(term),'root_choices':root_choices,'terminal_sets':[sorted(s) for s in sorted({frozenset(p) for p in term},key=lambda x:sorted(x))],'scope':'positive displayed subtraction rows only, natural add/mul RHS, literal substitution and syntactic degree <=3; not semantic impossibility or Lean proof'},indent=2,sort_keys=True))
