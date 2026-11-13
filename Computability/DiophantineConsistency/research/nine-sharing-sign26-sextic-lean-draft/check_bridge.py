#!/usr/bin/env python3
"""Check finite drop/lift mapping and explicit symbolic gap target text."""
import hashlib,json,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();p=D/'research/nine-sharing-sign26-sextic-gap-congruence-candidate/seed.json';assert H(p)=='36efa7dd3b2ea06d210b8975db2cbfc4f7494549c87204ada18747a720cb1f25';d=json.loads(p.read_text());assert d['old_gap_coordinate']==22 and d['removed_gate']=='gap'
q=P/'SharingSeed26BridgeDraft.lean';s=q.read_text();assert 'SOURCE-ONLY' in s and not re.search(r'(?m)^\s*(?:theorem|lemma)\b|\b(?:sorry|admit)\b',s)
blocks=re.findall(r'!\[([^\]]+)\]',s);assert len(blocks)==2
lift=[x.strip() for x in blocks[0].split(',')];drop=[x.strip() for x in blocks[1].split(',')]
assert lift==[f'v {i}' for i in range(22)]+['gap']+[f'v {i}' for i in range(22,27)]
assert drop==[f'v {i}' for i in range(22)]+[f'v {i}' for i in range(23,28)]
assert len(lift)==28 and len(drop)==27
assert 'a * (a + 1) + (ι (v 3) + 1) - a * (ι (v 2) + 1)' in s
assert '((p 0 : ℤ) : DiffRing V) = ι beta' in s and '((p 1 : ℤ) : DiffRing V) = ι K' in s and '1 ≤ beta' in s and '∃ gap : V, ι gap = ringGap p v' in s
print(json.dumps({'status':'PASS_SOURCE_MAPPING_ONLY','source_sha256':H(q),'candidate_sha256':H(p),'lift_coordinates':len(lift),'drop_coordinates':len(drop),'scope':'Textual finite mapping and explicit target assumptions only; no Lean elaboration, gap positivity, congruence or zero-set proof.'},sort_keys=True,indent=2))
