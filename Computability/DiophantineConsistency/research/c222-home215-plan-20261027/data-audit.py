"""Read-only literal Home-row/window cross-check; this is not a Lean proof."""
from pathlib import Path
import hashlib,json,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
H=Path(__file__).resolve().parent
B=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
p=B/'KTable215.lean'
s=p.read_text().split('def table215 : List (Row × Row) := [',1)[1].split('\ndef tm215',1)[0].strip()
pat=re.compile(r'\((none|some \((?:true|false), (?:true|false), \d+\)), (none|some \((?:true|false), (?:true|false), \d+\))\)')
def action(a):
 if a=='none':return None
 m=re.fullmatch(r'some \((true|false), (true|false), (\d+)\)',a);assert m
 return m[1]=='true',m[2]=='true',int(m[3])
rows=[]
for line in s.splitlines():
 m=pat.fullmatch(line.strip().rstrip(',]').strip());assert m,line
 rows.append(tuple(map(action,m.groups())))
assert len(rows)==226
states=[2,3,5,9,15,23,34,50]
scan=[]
for i,q in enumerate(states):
 assert rows[q][1]==(True,False,2)
 scan.append(dict(input=[q,True],action=rows[q][1]))
 if i<7:
  assert rows[q][0]==(False,False,states[i+1])
  scan.append(dict(input=[q,False],action=rows[q][0]))
assert len(scan)==15
cells={i:False for i in range(-8,1)};cells[1]=True
tape=dict(cells);q=2;head=0;trace=[]
for step in range(18):
 assert head in tape,('unspecified read',step,q,head)
 bit=tape[head];a=rows[q][int(bit)];assert a is not None
 write,right,nxt=a
 trace.append(dict(clock=step,state=q,head=head,read=bit,write=write,right=right,next=nxt))
 tape[head]=write;head+=1 if right else -1;q=nxt
assert(q,head)==(84,2)and tape==cells
scan_inputs={tuple(x['input'])for x in scan}
extra=sorted({(x['state'],x['read'])for x in trace}-scan_inputs)
assert extra==[(50,False),(75,False),(75,True)]
result=dict(status='READ_ONLY_CROSS_CHECK_NOT_A_KERNEL_PROOF',
 source=rec(p),source_rows=len(rows),scan_states=states,scan_rows=scan,
 additional_boundary_rows=[dict(input=[q,b],action=rows[q][int(b)])for q,b in extra],
 cells=sorted(cells.items()),trace=trace,clock=18,final_state=q,final_head=head,
 restored=True,scope='All finite rows must be independently checked by the proposed Lean leaf; no execution theorem is assumed from this audit.',
 contracts=[rec(B/(n+'.lean'))for n in ['KHome','KHomeReady','KZipTape','FramedWindow']],script=rec(__file__))
(H/'data-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status=result['status'],result=rec(H/'data-audit.json'))))
