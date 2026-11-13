#!/usr/bin/env python3
"""Independent read-only cross-check of retained import-collision evidence."""
import hashlib,json,os,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B without -O')
r=Path(__file__).resolve().parents[1];p=r/'current14-matrix-import-order-probe'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={'result.json':'914339a67b5a866cb577de5e12b79a0212cb725c4307ae87c699e539efefe20d','runner-captured.py':'c1d08e82d6a0b1a670e756b3eaddf9821f27cfbd1a0f66ae35d1e3bda77115cc','trace-result.json':'d26955072436cf2c337f084a3572297b61250591fd62d6a5fd9d4da7aada02e9','trace.py':'b8bfb62a29f6cd3868a101c8e3c13036a1d982aa568f5182d8b600e8e9f72e3f','outer-observation.json':'0cc95b049b663cd97f63dfc7c75401bd3f8a24da6704d8257f6347d2b1eabc33'}
for n,h in pins.items():
 if sha(p/n)!=h:raise RuntimeError('packet pin '+n)
data=json.loads((p/'result.json').read_text());outer=json.loads((p/'outer-observation.json').read_text());trace=json.loads((p/'trace-result.json').read_text())
if data['status']!='COMPLETED_BOTH' or data['runner_sha256']!=pins['runner-captured.py'] or outer['observed_runner_exit']!=0 or outer['result_sha256']!=pins['result.json'] or trace['status']!='PASS_SOURCE_DECLARED_EDGES' or trace['trace_sha256']!=pins['trace.py']:raise RuntimeError('receipt mismatch')
expected={'foundation_first':('Mathlib.LinearAlgebra.Matrix.Defs',"Matrix.map' from Foundation.Vorspiel.Matrix"),'mathlib_first':('Foundation.Vorspiel.Matrix',"Matrix.map.eq_1' from Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber")}
if {x['case'] for x in data['results']}!=set(expected):raise RuntimeError('case set')
for x in data['results']:
 case=x['case'];d=p/case;receipt=x['owned_receipt'];pid=receipt['pid'];src=d/'Probe.lean';out=d/'stdout.log';err=d/'stderr.log'
 if x['exit']!=1 or x['monitor_failure'] is not None or x['events'] or x['object_sha256'] is not None or receipt['exit']!=1 or not receipt['session_drained'] or not receipt['direct_child_reaped'] or receipt['initial']['pgrp']!=pid or receipt['initial']['session']!=pid:raise RuntimeError('case receipt '+case)
 if x['samples']<1 or x['peak_rss']>=7*1024**3//2 or x['min_available']<10*1024**3:raise RuntimeError('monitor bounds '+case)
 if sha(src)!=x['source_sha256'] or sha(out)!=x['stdout_sha256'] or sha(err)!=x['stderr_sha256'] or err.read_bytes() or src.read_text()!=''.join('import '+m+'\n' for m in x['imports']):raise RuntimeError('case files '+case)
 text=out.read_text();module,collision=expected[case]
 if 'error: import '+module+' failed' not in text or collision not in text:raise RuntimeError('diagnostic '+case)
 actual=Path(x['command'][-3]);realout=actual.parent/'stdout.log';realerr=actual.parent/'stderr.log'
 if not actual.is_file() or sha(actual)!=x['source_sha256'] or sha(realout)!=x['stdout_sha256'] or sha(realerr)!=x['stderr_sha256'] or (actual.parent/'Probe.olean').exists():raise RuntimeError('original outputs '+case)
for path,entry in data['provider_guards'].items():
 f=Path(path)
 if entry is None:
  if os.path.lexists(f):raise RuntimeError('unexpected provider '+path)
 elif not f.is_file() or str(f.resolve())!=entry['realpath'] or sha(f)!=entry['sha256']:raise RuntimeError('provider drift '+path)
if len(data['provider_guards'])!=20:raise RuntimeError('wrong guard cardinality')
edgecount=0
for chain in trace['chains']:
 for i,node in enumerate(chain):
  source=Path(node['source']);text=source.read_text()
  if sha(source)!=node['sha256']:raise RuntimeError('source drift '+node['module'])
  if i+1<len(chain):
   nxt=chain[i+1]['module'];pat=r'^\s*(?:(?:public|private|meta)\s+)?import\s+'+re.escape(nxt)+r'(?=\s|$)'
   if not re.search(pat,text,re.M):raise RuntimeError('edge missing '+node['module']+' -> '+nxt)
   edgecount+=1
for node in trace['colliding_source_definitions']:
 text=Path(node['source']).read_text()
 if sha(node['source'])!=node['sha256'] or 'namespace Matrix' not in text or 'def map (' not in text:raise RuntimeError('collision source')
print(json.dumps({'status':'PASS_CAPTURED_EVIDENCE','source_edges':edgecount,'direct_companion_guards':len(data['provider_guards']),'lean_exits':[1,1],'outer_runner_exit':0,'scope':'Read-only hash/receipt and raw source-edge cross-check; no Lean replay or full transitive source-object authentication.'},sort_keys=True))
