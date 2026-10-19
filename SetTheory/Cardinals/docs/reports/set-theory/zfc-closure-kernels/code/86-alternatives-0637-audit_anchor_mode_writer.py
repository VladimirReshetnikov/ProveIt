#!/usr/bin/env python3
from pathlib import Path
import sys,itertools,json,hashlib
if not __debug__:raise RuntimeError('Assertions required')
OUT=Path(__file__).resolve().parent;D=OUT.parent/'native_copier';sys.path.insert(0,str(D))
import anchor_mode_writer as M
p=D/'anchor_mode_writer_11.tm';table={}
for line in p.read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n));assert(q,b)not in table;table[q,b]=w,d,n
compiled,entries,ret,names=M.compile_writer();assert table==compiled and ret==11
assert set(table)==set(itertools.product(range(11),range(2)))
guards=json.loads((D/'anchor_mode_writer_guards.json').read_text());allowed={n:set()for n in names};inv={i:n for n,i in names.items()};traces={};count=0
for old,new,origin,mask in itertools.product(range(1,5),range(1,5),(-37,0,19),range(64)):
 # Seven-cell header independently expressed by its two zero positions.
 tape={origin+j for j in range(7)if j not in(old,6)}
 for j in range(3):
  if mask>>j&1:tape.add(origin-j-1)
  if mask>>(j+3)&1:tape.add(origin+7+j)
 want=(tape-set(range(origin,origin+7)))|{origin+j for j in range(7)if j not in(new,6)}
 q=entries[new];h=origin;trace=[]
 for step in range(7):
  assert q!=ret and h==origin+step;b=int(h in tape);trace.append([q,step,b]);allowed[inv[q]].add(b)
  w,d,q=table[q,b];assert d=='R'
  if w:tape.add(h)
  else:tape.discard(h)
  h+=1
 assert q==ret and h==origin+7 and tape==want
 assert traces.setdefault((old,new),trace)==trace
 count+=1
assert{n:sorted(v)for n,v in allowed.items()}==guards['allowed_reads']
assert len(guards['traces'])==16
for tr in guards['traces']:assert tr['trace']==traces[tr['old'],tr['new']]
forced=[n for n,v in allowed.items()if v=={1}]
assert set(forced)=={'unseen4','seen0','seen1','seen2'}
result={'status':'PASS','working_states':11,'operational_states':10,'transition_rows':22,'separate_return':11,'independent_whole_tape_cases':count,'exhaustive_header_cases':16,'steps_each':7,'forced_one_states':forced,'all_saved_traces_and_guards_verified':True,
 'hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in[D/'anchor_mode_writer.py',D/'anchor_mode_writer_11.tm',D/'anchor_mode_writer_guards.json',D/'SYMBOL_PARTITION_PACKING.md']}}
(OUT/'anchor_mode_writer_independent_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
