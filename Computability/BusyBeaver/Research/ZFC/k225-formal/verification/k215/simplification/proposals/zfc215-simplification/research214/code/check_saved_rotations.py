#!/usr/bin/env python3
"""Check the lossless shared-DAG receipt and all saved reassociation finalists."""
if not __debug__:raise RuntimeError('Assertions must be enabled.')
from pathlib import Path
import sys,json,hashlib,copy
sys.path.insert(0,str(Path(__file__).resolve().parent/'vendor'))
import source_language as s
import source_splice as sp
D=Path(__file__).resolve().parents[1]
p=D/'results/pruned3_rotations/result.json';d=json.loads(p.read_text());encoding=d.pop('rotation_tree_encoding');nodes=encoding['nodes'];memo={}
def dec(i):
 if i not in memo:
  a=nodes[i];memo[i]=a if isinstance(a[0],str)else[dec(a[0]),dec(a[1])]
 return memo[i]
for f in d['finalists']:
 f['rotations']=[{'old_tree':dec(r['old_tree_node']),'new_tree':dec(r['new_tree_node']),'direction':r['direction']}for r in f['rotations']]
raw=(json.dumps(d,indent=2)+'\n').encode();assert hashlib.sha256(raw).hexdigest()==encoding['uncompressed_original_receipt_sha256'];del raw
original=json.loads((D/'source_variants/pruned3.json').read_text());g=sp.cfg_intervals(original);assert g==sp.cfg_arithmetic(original)
for f in d['finalists']:
 raw=(p.parent/f['source']).read_bytes();assert hashlib.sha256(raw).hexdigest()==f['sha256'];rows=json.loads(raw)
 assert [x[1:]for x in rows]==[x[1:]for x in original]
 assert sp.cfg_intervals(rows)==sp.cfg_arithmetic(rows)==g
 assert s.metrics(s.tree(rows))==f['metrics']
print(json.dumps({'status':'SAVED_ROTATIONS_PASS','finalists':len(d['finalists']),'rotation_DAG_nodes':len(nodes),'lossless_expanded_receipt_hash':encoding['uncompressed_original_receipt_sha256']},indent=2))
