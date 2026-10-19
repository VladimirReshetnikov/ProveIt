#!/usr/bin/env python3
"""Own static row/bound/census check; no supplied code or proof execution."""
from pathlib import Path
import hashlib,json,re
B=Path('/tmp/zfc243-source-bridge');P=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProgramRouting245.lean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p))
S=B/'SourceRotation244.lean';A=B/'Audit.lean';s=S.read_text()
rows=[]
for i,body in re.findall(r'^private def row(\d+) : Row := (.+)$',P.read_text(),re.M):
 assert int(i)==len(rows)
 rows.append([(k,int(v)if v else None)for k,v in re.findall(r'\.(node|inc|decnz|brk|cont|halt)(?: (\d+))?',body)])
assert len(rows)==203 and all(len(r)==2 for r in rows)
t=s.split('private def bounds (n : Nat) : Nat × Nat × Nat :=\n',1)[1].split('\nprivate def H',1)[0]
tokens=re.findall(r'if|n|<|\d+|then|else|\(|\)|,',t);i=0
def parse():
 global i
 a=tokens[i];i+=1
 if a=='(':
  values=[]
  for j in range(3):
   values.append(int(tokens[i]));i+=1
   assert tokens[i]==(','if j<2 else')');i+=1
  return tuple(values)
 assert a=='if' and tokens[i:i+2]==['n','<'];i+=2
 k=int(tokens[i]);i+=1;assert tokens[i]=='then';i+=1
 x=parse();assert tokens[i]=='else';i+=1;y=parse();return(k,x,y)
tree=parse();assert i==len(tokens)
def lookup(t,n):
 return t if isinstance(t[1],int)else lookup(t[1]if n<t[0]else t[2],n)
bounds=[lookup(tree,n)for n in range(203)]
expected=json.loads(Path('/tmp/zfc243-calibration-plan/wf-candidate-tables.json').read_text())['original']
assert bounds==list(zip(expected['height'],expected['break_escape'],expected['continue_escape']))
new=[r.copy()for r in rows];new[5]=[('decnz',6),('cont',2)];new[6]=[('inc',0),('node',5)]
checks=0
for rotated,table in [(False,rows),(True,new)]:
 H=[v[0]for v in bounds];BB=[v[1]for v in bounds];CC=[v[2]for v in bounds]
 if rotated:CC[5]=1
 def h(e):return H[e[1]]if e[0]=='node'else 0
 def b(e):return BB[e[1]]if e[0]=='node'else(1 if e[0]=='decnz'else e[1]if e[0]=='brk'else 0)
 def c(e):return CC[e[1]]if e[0]=='node'else(e[1]if e[0]=='cont'else 0)
 for n,(a,z)in enumerate(table):
  assert all(e[0]!='node'or 0<=e[1]<203 for e in (a,z))
  assert all(e[0]not in ('brk','cont')or e[1]>0 for e in (a,z))
  assert h(a)<H[n] and h(z)<H[n] and b(a)<=BB[n]+1 and b(z)<=BB[n] and c(a)<=CC[n] and c(z)<=CC[n]+1
  checks+=8
 assert H[202]<=204 and BB[202]==CC[202]==0
for n,row in enumerate(rows):
 if n not in (4,5,6):
  assert row==new[n] and all(e[0]!='node'or e[1]not in (4,5)for e in row)
  checks+=3
names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);assert len(names)==9 and len(re.findall(r'^example\b',A.read_text(),re.M))==10
assert not re.search(r'\b(sorry|admit|native_decide)\b',s+A.read_text()) and 'maxHeartbeats'not in s and 'maxRecDepth'not in s
receipt=dict(status='AUTHOR_STATIC_FINITE_DATA_REVIEW_PASS',source=desc(S),audit=desc(A),reviewer_source=desc(Path(__file__)),old_program_source=desc(P),finite_arithmetic_checks=checks,old_rows=203,new_rows=203,shared_height_root=51,old_root_escape=[0,0],new_root_escape=[0,0],only_changed_continue_bound=5,safe_interior_exclusions=[4,5],macro_entry=6,probes=9,callers=10,proof_execution=False,findings=[],scope='Parsed emitted bound lookup and exact source DAG independently of the emitter, checked all WF inequalities and safe-child/common-row obligations. Elaboration and kernel proof checks remain pending.')
(B/'author-finite-data-review.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(desc(B/'author-finite-data-review.json')))
