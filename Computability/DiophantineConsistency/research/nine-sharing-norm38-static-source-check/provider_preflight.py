#!/usr/bin/env python3
"""Point-in-time static-carrier/FreshModel106 direct-provider comparison; no Lean."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];F=D/'research/normalized106-fresh-base-model-build/attempt03';S=D/'research/nine-sharing-norm38-static-carrier-compose-check/attempt01';FT=Path('/tmp/normalized106-fresh-model-client-20261105');ST=Path('/tmp/nine-sharing-norm38-static-carrier-compose-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
need(sha(F/'state.json')=='dea372080bd6380703bdf770bde887436699f7998e7927dacadb2bec66016d23','FreshModel106 state');need(sha(S/'state.json')=='454aa2c28427b362766346a5281ceef88d8fc8aae173dc7098032426a8ca409d'==sha(ST/'state.json'),'static-carrier state');f=json.loads((F/'state.json').read_text());s=json.loads((S/'state.json').read_text());need(f['status']=='PASS' and all(r['exit']==0 for r in f['runs']) and s['status']=='PASS' and len(s['rows'])==1,'status')
need(sha(FT/'FreshModel106.lean')==f['source_sha256']=='61e64a2ef559c3da369021df2705cd76f957bc0ea971467b80d627eaa9422769' and sha(FT/'FreshModel106.olean')==f['object_sha256']=='d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942','FreshModel106 source/object')
for name,r in zip(('deps.txt','compile.txt'),f['runs']):need(sha(F/name)==r['log_sha256'],'FreshModel106 log '+name)
for path,v in f['direct_guard'].items():
 q=Path(path)
 if v is None:need(not os.path.lexists(q),'unexpected FreshModel106 candidate '+path)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'FreshModel106 guard '+path)
row=s['rows'][0];need(row['module']=='Norm38StaticCarrierCompose' and row['deps']['exit']==0 and row['compile']['exit']==0 and sha(ST/'src/DiophantineConsistency/Norm38StaticCarrierCompose.lean')==row['source_sha256'] and sha(ST/'lib/DiophantineConsistency/Norm38StaticCarrierCompose.olean')==row['object_sha256']=='7330cef6fb69cd41cab2e9febc17bb9b356a66b68cb16e88725e9a7897712aa1','static-carrier producer')
for kind in ('deps','compile'):need(sha(ST/('Norm38StaticCarrierCompose-'+kind+'.txt'))==sha(S/('Norm38StaticCarrierCompose-'+kind+'.txt'))==row[kind]['log_sha256'],'static-carrier log '+kind)
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:need(not os.path.lexists(q),'unexpected static-carrier candidate '+path)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'static-carrier guard '+path)
for path,target in s['overlay_links'].items():need(Path(path).is_symlink() and str(Path(path).resolve())==target,'static-carrier overlay '+path)
matched=[]
for mod,r in f['dependencies'].items():
 if mod=='Init':continue
 need(mod.startswith('DiophantineConsistency.'),'unexpected project dependency '+mod);p=ST/'lib'/Path(*mod.split('.')).with_suffix('.olean');need(p.is_symlink() and str(p.resolve())==r['realpath'] and sha(p)==r['sha256'],'project provider mismatch '+mod);matched.append(mod)
need(len(matched)==6,'six direct project dependencies');need(not os.path.lexists(ST/'lib/FreshModel106.olean'),'FreshModel106 shadow');print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','matched_direct_project_modules':sorted(matched),'fresh_direct_guard_slots':len(f['direct_guard']),'static-carrier_direct_guard_slots':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'Recorded direct project inputs and paths only. No Lean import, complete package-transitive or dynamic load trace.'},sort_keys=True,indent=2))
