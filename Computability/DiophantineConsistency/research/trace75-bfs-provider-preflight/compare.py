#!/usr/bin/env python3
"""Compare the current trace75 project overlay against the fresh BFS union."""
from pathlib import Path
from hashlib import sha256
import json, os, sys, time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent
A=Path('/tmp/trace75-fixedcongruence-dhpg0dm5/DiophantineConsistency')
B=Path('/tmp/direct-bfs-80-coherent-8gret5ed/lib/DiophantineConsistency')
RESULT=H.parent/'direct-bfs-80-coherent-rebuild/observations/attempt01/result.json'
EXPECTED='ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559'
O=H/'observations/compare-attempt01'; suffixes=['.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash']
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def rec(p):
 if not os.path.lexists(p):return None
 need(p.is_file(),'not a file: '+str(p))
 return {'path':str(p),'real_path':str(p.resolve(strict=True)),'sha256':sha(p),'link':os.readlink(p) if p.is_symlink() else None}
need(not O.exists(),'observation exists');need(sha(RESULT)==EXPECTED,'BFS receipt drift')
start=time.time_ns(); rows={}
for a in sorted(A.rglob('*.olean')):
 b=B/a.relative_to(A)
 if not b.is_file():continue
 ra,rb=rec(a),rec(b);rows[a.relative_to(A).as_posix()]={'trace75':ra,'bfs':rb,'same':ra['sha256']==rb['sha256']}
diffs={n:r for n,r in rows.items() if not r['same']}
need(len(rows)==997 and len(diffs)==5,'unexpected comparison counts')
for name,row in diffs.items():
 stem=name[:-6]
 row['companions']={'trace75':{s:rec(A/(stem+s)) for s in suffixes},'bfs':{s:rec(B/(stem+s)) for s in suffixes}}
for name,row in rows.items():
 need(rec(A/name)==row['trace75'] and rec(B/name)==row['bfs'],'object drift '+name)
for name,row in diffs.items():
 stem=name[:-6]
 for label,root in [('trace75',A),('bfs',B)]:
  for suffix,value in row['companions'][label].items():need(rec(root/(stem+suffix))==value,'companion drift '+name+suffix)
need(sha(RESULT)==EXPECTED,'receipt drift after');O.mkdir(parents=True)
result={'status':'PASS','trace75_overlay':str(A),'bfs_union':str(B),'bfs_receipt':str(RESULT),'bfs_receipt_sha256':EXPECTED,'runner_sha256':sha(__file__),'started_ns':start,'ended_ns':time.time_ns(),'common_count':len(rows),'mismatch_count':len(diffs),'mismatches':diffs,'scope':'current overlapping namespace object hashes only; not serialized ancestry, compile-time selection, provenance or equivalence'}
(O/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','common':len(rows),'mismatches':len(diffs),'sha256':sha(O/'result.json')}))
