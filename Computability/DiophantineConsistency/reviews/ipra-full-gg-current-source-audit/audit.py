#!/usr/bin/env python3
"""Read-only source-declared import closure comparison; no object claim."""
import json,re,tomllib,hashlib
from pathlib import Path
R=Path(__file__).resolve().parents[4];cfg=tomllib.loads((R/'lakefile.toml').read_text());libs={x['name']:R/x.get('srcDir','.') for x in cfg['lean_lib']};m=json.loads((R/'Computability/DiophantineConsistency/reviews/ipra-full-gg-transfer-accepted-parent/manifest.json').read_text());native=json.loads((R/'Computability/DiophantineConsistency/reviews/ipra-native-theory-replay/manifest.json').read_text());seen={};ext=set();vis=set();drift=[];unmatched=[]
def go(n):
 if n in seen or n in ext:return
 top=n.split('.')[0]
 if top not in libs:ext.add(n);return
 p=libs[top]/(n.replace('.','/')+'.lean')
 if not p.is_file():
  if top=='Foundation':ext.add(n);return
  unmatched.append((n,'missing source'));return
 if n in vis:raise RuntimeError('cycle '+n)
 vis.add(n);rel=str(p.relative_to(R));sha=hashlib.sha256(p.read_bytes()).hexdigest();name=n.rsplit('.',1)[1];old=m['workspace_sources'].get(rel) or m['suffix_sources'].get(name) or native['suffix_sources'].get(name);seen[n]={'path':rel,'sha256':sha,'prior_sha256':old}
 if old is None:unmatched.append((n,'not in accepted manifest'))
 elif old!=sha:drift.append(n)
 for line in p.read_text().splitlines():
  z=re.match(r'^\s*(?:public\s+)?import\s+(.+)',line)
  if z:
   for d in z.group(1).split('--')[0].split():go(d)
 vis.remove(n)
go('DiophantineConsistency.IPRAFullGGTransfer');out={'status':'COMPLETE','scope':'current source-declared project import traversal with accepted packet source-hash comparison; not dynamic import or transitive object provenance','sources':seen,'unmatched':unmatched,'drift':drift,'external':sorted(ext)};print(json.dumps(out,indent=2))
