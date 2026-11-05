#!/usr/bin/env python3
"""Point-in-time topology/FreshModel106 direct-provider comparison; no Lean."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];F=D/'research/normalized106-fresh-base-model-build/attempt03';S=D/'research/nine-sharing-norm38-topology-check/attempt01';FT=Path('/tmp/normalized106-fresh-model-client-20261105');ST=Path('/tmp/nine-sharing-norm38-topology-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
need(sha(F/'state.json')=='dea372080bd6380703bdf770bde887436699f7998e7927dacadb2bec66016d23','FreshModel106 state');need(sha(S/'state.json')=='ac766e23a56ec4a7c97b8c17d4703b9d20f9081a4af0681987f7c206a7f2d2a0'==sha(ST/'state.json'),'topology state');f=json.loads((F/'state.json').read_text());s=json.loads((S/'state.json').read_text());need(f['status']=='PASS' and all(r['exit']==0 for r in f['runs']) and s['status']=='PASS' and len(s['rows'])==1,'status')
need(sha(FT/'FreshModel106.lean')==f['source_sha256']=='61e64a2ef559c3da369021df2705cd76f957bc0ea971467b80d627eaa9422769' and sha(FT/'FreshModel106.olean')==f['object_sha256']=='d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942','FreshModel106 source/object')
for name,r in zip(('deps.txt','compile.txt'),f['runs']):need(sha(F/name)==r['log_sha256'],'FreshModel106 log '+name)
for path,v in f['direct_guard'].items():
 q=Path(path)
 if v is None:need(not os.path.lexists(q),'unexpected FreshModel106 candidate '+path)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'FreshModel106 guard '+path)
row=s['rows'][0];need(row['module']=='SharingTopology38' and row['deps']['exit']==0 and row['compile']['exit']==0 and sha(ST/'src/DiophantineConsistency/SharingTopology38.lean')==row['source_sha256'] and sha(ST/'lib/DiophantineConsistency/SharingTopology38.olean')==row['object_sha256']=='90661b7bf1e7be709ad2d32e67447e6e05a3d698c975a3e5632566b91fdcca38','topology producer')
for kind in ('deps','compile'):need(sha(ST/('SharingTopology38-'+kind+'.txt'))==sha(S/('SharingTopology38-'+kind+'.txt'))==row[kind]['log_sha256'],'topology log '+kind)
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:need(not os.path.lexists(q),'unexpected topology candidate '+path)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'topology guard '+path)
for path,target in s['overlay_links'].items():need(Path(path).is_symlink() and str(Path(path).resolve())==target,'topology overlay '+path)
matched=[]
for mod,r in f['dependencies'].items():
 if mod=='Init':continue
 need(mod.startswith('DiophantineConsistency.'),'unexpected project dependency '+mod);p=ST/'lib'/Path(*mod.split('.')).with_suffix('.olean');need(p.is_symlink() and str(p.resolve())==r['realpath'] and sha(p)==r['sha256'],'project provider mismatch '+mod);matched.append(mod)
need(len(matched)==6,'six direct project dependencies');need(not os.path.lexists(ST/'lib/FreshModel106.olean'),'FreshModel106 shadow');print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','matched_direct_project_modules':sorted(matched),'fresh_direct_guard_slots':len(f['direct_guard']),'topology_direct_guard_slots':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'Recorded direct project inputs and paths only. No Lean import, complete package-transitive or dynamic load trace.'},sort_keys=True,indent=2))
