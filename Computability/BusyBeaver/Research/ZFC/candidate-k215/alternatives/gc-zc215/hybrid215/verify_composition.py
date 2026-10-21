"""Standard-library exact source/table composition and local merge proof."""
from pathlib import Path
import argparse,json,hashlib
if not __debug__:raise RuntimeError('Assertions required')
H=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--baseline-source',type=Path,default=H/'zc215.reference.sites.json');p.add_argument('--baseline-table',type=Path,default=H/'zc215.reference.native.tm');p.add_argument('--source',type=Path,default=H/'gc_zc.sites.json');p.add_argument('--table',type=Path,default=H/'gc_zc215_start74.native.tm');p.add_argument('--output',type=Path,default=H/'COMPOSITION_AUDIT.json');a=p.parse_args()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 t={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert(q,b)not in t;t[q,b]=(w,1 if d=='R'else -1,z)
 return t
old=json.loads(a.baseline_source.read_text());new=json.loads(a.source.read_text());assert len(old)==len(new)==4752
expected=json.loads(json.dumps(old));assert expected[46][1:]==['CD',4]and expected[51][1:]==['CI',4];expected[46][2]=expected[51][2]=3;assert new==expected
# Addresses, primitive kinds and jump depths are all unchanged; hence both
# conditional edges and every other control-flow edge are literally unchanged.
base=table(a.baseline_table);middle=base.copy();assert middle[135,0]==(0,1,76);middle[135,0]=(0,1,303);middle[303,0]=(0,1,154);middle[303,1]=(1,1,86)
assert middle[129,0]==middle[303,0]
origins={q:[(s,b,w,d)for(s,b),(w,d,z)in middle.items()if z==q]for q in(129,303)}
assert origins=={129:[(211,1,1,1)],303:[(135,0,0,1)]}
merged={k:(w,d,129 if z==303 else z)for k,(w,d,z)in middle.items()if k[0]!=303};merged[129,1]=(1,-1,216)
assert table(a.table)==merged and len(merged)==430
assert a.table.read_text().splitlines()[0]=='#! start 74'
# Every entry writes the identifying predecessor bit then moves right.
# On reading zero the two old transitions agree. For reading one verify
# exact whole-tape local endpoints; cells beyond these two are never read.
blocks=[]
for q,marker in[(129,1),(303,0)]:
 for bit in(0,1):
  w,d,target=middle[q,bit];expected_tape={-1:marker,0:w};tape={-1:marker,0:bit};state=129;head=0;trace=[]
  for step in range(20):
   if step and(state,head)==(target,d):break
   assert head in tape
   read=tape[head];ww,dd,zz=merged[state,read];trace.append([state,head,read,ww,dd,zz]);tape[head]=ww;head+=dd;state=zz
  else:raise AssertionError('local path did not close')
  assert tape==expected_tape
  blocks.append(dict(old_role=q,left_marker=marker,read=bit,new_steps=step,target=target,head_delta=d,trace=trace))
assert 74 not in(129,303)
r=dict(status='PASS',states=215,start=74,baseline_source_sha256=sha(a.baseline_source),baseline_table_sha256=sha(a.baseline_table),source_sha256=sha(a.source),table_sha256=sha(a.table),changed_source_ordinals=[46,51],literal_CFG_preserved=True,static_incoming_edges=origins,local_blocks=blocks,scope='Exact source/table construction and universally valid conditional merge relative to unmerged216 table. Unmerged source compilation, full binary runtime, logical compiler and startup are separate obligations.')
a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items()if k!='local_blocks'},indent=2))
