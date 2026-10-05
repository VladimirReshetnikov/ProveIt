"""Verify exact profile/basis completeness of the BR cone batch."""
from build_br import ROOT,profiles,BASES
import json,hashlib
from collections import Counter
records=[]
for core in profiles():
 path=ROOT/('br_%s_%s_%s_%s.json'%core)
 if not path.exists():raise RuntimeError(('missing',core))
 v=json.loads(path.read_text())
 if tuple(v['core'])!=core or v['negative'] is not None or v['basis_count']!=51:raise RuntimeError(('incomplete',core))
 if set(tuple(x['basis']) for x in v['records'])!=set(BASES):raise RuntimeError(('basis set',core))
 if v['multiplier']<=0 or any(x['negative'] or x['minimum']<0 for x in v['records']):raise RuntimeError(('bad sign',core))
 records.append(v)
counts=Counter();degrees=set();denominators=set()
for v in records:
 counts[v['core'][0]]+=sum(x['terms'] for x in v['records']);degrees.add(v['degree']);denominators.add(v['denominator'])
out={'all_profiles_pass':True,'profile_count':len(records),'profiles_by_root_size':dict(Counter(v['core'][0].bit_count() for v in records)),'basis_instances':sum(v['basis_count'] for v in records),'coefficient_entries':sum(counts.values()),'coefficient_entries_by_U':dict(counts),'degrees':sorted(degrees),'denominators':sorted(denominators),'records':records,'source_sha256':{f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in ['build_br.py','br_support_core.py','reduction.md']}}
(ROOT/'br_manifest.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))
