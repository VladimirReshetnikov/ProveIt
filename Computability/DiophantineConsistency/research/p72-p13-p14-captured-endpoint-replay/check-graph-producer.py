#!/usr/bin/env python3
"""Read-only P72Graph source-shim-object/log link in the prior P65 receipt."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/p65-reverse-provider';C=D/'Lean/DiophantineConsistency/Compact44/P72Graph.lean';BASE=Path('/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/Compact44/P72Graph.olean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
need(sha(P/'manifest.json')=='9cc6b449e9da05cc022386f316c88a5a1d854f21e205aab9c13a2e076fddc4e1' and sha(P/'results.json')=='d8a8c804137ab7910b62356cd398eab9f6b30742155d1e43d05f29a11203aa0a','receipt hashes')
m=json.loads((P/'manifest.json').read_bytes());r=json.loads((P/'results.json').read_bytes());n='DiophantineConsistency.Compact44.P72Graph';rows=[x for x in m['order'] if x['module']==n];need(len(rows)==1,'manifest row');x=rows[0];y=r[n]
need(x['source_sha256']==sha(C)=='fa31965a9b6c6c4937b4a27f22607a1e7e8ac4877bc8c9eb7994c28cb4fc677a','canonical source');need(x['shim_sha256']==y['shim_sha256']==sha(x['shim'])=='c015cac37af0877ad8d5f370b078557fc8007b06bd6a69ed06266465743c9754','shim source')
need(Path(x['shim']).read_text()==C.read_text().replace('import DiophantineConsistency.Compact44.FreeJSumSquares\n','import FreeJSumSquares\n',1),'shim change')
need(y['object_sha256']==sha(y['object'])==sha(BASE)=='cd9c5b6b0429a90a25d5b9ab88cde120f8e3b684045a561a90b56be0037661b7','object linkage');need(y['log_sha256']==sha(y['log'])=='bddfc4282aacd9895ad0bfc8d4d95bbecbc192380c91b8173a19422a8b64c3dc','log')
log=Path(y['log']).read_text();need('exit: 0, elapsed:' in log and 'sorryAx' not in log and 'error:' not in log,'producer log status')
print(json.dumps({'status':'PASS_INHERITED_GRAPH_PRODUCER_LINK','canonical_source_sha256':sha(C),'shim_sha256':sha(x['shim']),'object_sha256':sha(BASE),'log_sha256':sha(y['log']),'scope':'Recorded P65 producer linkage and import-only graph source change; not full package/dynamic provenance or Lean JSON semantics.'},sort_keys=True,indent=2))
