#!/usr/bin/env python3
"""Read-only surviving-object union audit; no original 86 compile-time ancestry claim."""
from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent;B=Path('/tmp/pra14-full-transitive-g3ull6n_');C=Path('/tmp/pra14-zfc-join-sxrfkso1');A=Path('/tmp/pra86-classical-preliminary');N=Path('/tmp/ipra14-translated-join-flph2cp_');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();roots=[B,C,A,N];anchors={str(x/'state.json'):sha(x/'state.json') for x in roots};bs,cs,aa,ns=[json.loads((x/'state.json').read_text()) for x in roots];assert all(s['status']=='PASS' for s in [bs,cs,aa,ns]);parents={r['module']:r['object_sha256'] for r in bs['records']+cs['records']};native={r['module']:r['object_sha256'] for r in ns['records'][:33]};rows=[];deps=[];collisions=[]
for n,h in parents.items():
 rel=Path(n.replace('.','/')+'.olean');z={'module':n,'expected':h}
 for label,root in [('classical86',A),('native14',N)]:
  p=root/'lib'/rel;z[label]=sha(p) if p.is_file() else None
 z['matches']=z['classical86']==h==z['native14'];rows.append(z)
for r in ns['records'][:33]:
 rel=Path(r['module'].replace('.','/')+'.olean');q=A/'lib'/rel
 if q.exists():collisions.append(r['module'])
 for d,h in r['dependency_hashes'].items():
  rel=Path(d.replace('.','/')+'.olean');p=(N/'lib'/rel) if d in native else ((A/'lib'/rel) if d in parents else (B/'package-lib'/rel));actual=sha(p) if p.is_file() else None;deps.append({'module':r['module'],'dependency':d,'expected':h,'actual':actual,'matches':actual==h})
for p,h in anchors.items():assert sha(p)==h,p
out={'status':'PASS' if all(x['matches'] for x in rows+deps) and not collisions else 'FAILED','scope':'Surviving-object byte comparison only; does not establish original 86 module dependency environment or package-transitive ancestry.','state_anchors':anchors,'parent_objects':rows,'native_direct_dependencies':deps,'native_extension_modules':len(native),'name_collisions':collisions};(P/'audit.json').write_text(json.dumps(out,indent=2)+'\n');print('status',out['status'],'parent objects',len(rows),'native modules',len(native),'dependencies',len(deps),'collisions',len(collisions),flush=True)
