#!/usr/bin/env python3
"""Check exact declaration text only; this does not parse or check Lean."""
import json,hashlib,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
p=Path(__file__).resolve().parent;d=p.parents[1];t=(d/'research/nine-sharing-seed38-lean-draft/SharingSeed38.lean').read_text();
start=t.index('/-- The first residual');degree=t.index('/-- Candidate syntax-degree');poly=t.index('/-- Candidate polynomial-degree');zero=t.index('/-- Jones normalization valuation');first=t.index('/-- Candidate first-residual');end=t.index('-- Unresolved: prove')
for name,pieces in {'SharingSeed38Syntax.lean':[t[start:degree],t[zero:first]],'SharingSeed38Normalize.lean':[t[first:end]],'SharingSeed38Weighted.lean':[t[degree:poly]],'SharingSeed38Degree.lean':[t[poly:zero]]}.items():
 s=(p/name).read_text()
 for piece in pieces:assert piece in s, name
 assert s.count('sorry')==0 and s.count('admit')==0
m=json.loads((p/'source-manifest.json').read_text());assert len(m['rows'])==10
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
repo=d.parents[1]
for row in m['rows']:
 name=row['module'].split('.')[-1]+'.lean'
 assert sha(repo/row['source'])==row['source_sha256'] and sha(p/'src/DiophantineConsistency'/name)==row['source_sha256'], name
print(json.dumps({'status':'PASS_SOURCE_ONLY','upstream':sha(d/'research/nine-sharing-seed38-lean-draft/SharingSeed38.lean'),'files':{r['module']:r['source_sha256'] for r in m['rows']},'manifest_sha256':sha(p/'source-manifest.json'),'scope':'Exact split text and snapshot pins only; no Lean parsing or proof'},indent=2,sort_keys=True))
