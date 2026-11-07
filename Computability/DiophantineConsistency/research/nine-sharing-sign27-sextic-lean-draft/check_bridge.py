#!/usr/bin/env python3
"""Check the proposed finite coordinate map and its explicit open targets."""
import hashlib,json,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=D/'research/nine-sharing-sign27-sextic-normalized-root-candidate/seed.json';assert H(p)=='5bd7f45de28980c6ac9d3974a0087b1d9f8faf9b060b8a115843ea0cc4adff3d';d=json.loads(p.read_text())
assert (d['old_root_coordinate'],d['old_product_coordinate'],d['new_predecessor_coordinate'],d['removed_norm'])==(21,22,21,'N1')
assert d['old_root_as_new']==['add',['var',21],['num',1]] and d['old_product_as_new']==['mul',['var',21],['add',['var',21],['num',2]]]
q=P/'SharingSeed27BridgeDraft.lean';s=q.read_text();assert 'SOURCE-ONLY' in s and not re.search(r'(?m)^\s*(?:theorem|lemma)\b|\b(?:sorry|admit)\b',s)
blocks=re.findall(r'!\[([^\]]+)\]',s);assert len(blocks)==2
lift=[x.strip() for x in blocks[0].split(',')];drop=[x.strip() for x in blocks[1].split(',')]
assert lift==[f'v {i}' for i in range(21)]+['v 21 + 1','v 21 * (v 21 + 2)']+[f'v {i}' for i in range(22,28)]
assert drop==[f'v {i}' for i in range(21)]+['u']+[f'v {i}' for i in range(23,29)]
assert len(lift)==29 and len(drop)==28 and '∃ u : V, v 21 = u + 1 ∧ v 22 = u * (u + 2)' in s
print(json.dumps({'status':'PASS_SOURCE_MAPPING_ONLY','source_sha256':H(q),'candidate_sha256':H(p),'lift_coordinates':len(lift),'drop_coordinates':len(drop),'scope':'Textual finite mapping and explicit targets only; no Lean elaboration, predecessor or zero-set proof.'},sort_keys=True,indent=2))
