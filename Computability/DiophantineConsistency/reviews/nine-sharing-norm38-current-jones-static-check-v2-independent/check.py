#!/usr/bin/env python3
"""Source/provider review of current Jones/static composition v2; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-norm38-current-jones-static-check-v2';O=D/'research/nine-sharing-norm38-current-jones-static-check';BASE=Path('/tmp/nine-sharing-norm38-current-four-cast-instantiation-check-20261105');J=Path('/tmp/nine-sharing-seed38-current-jones-retry01-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for p,h in [(P/'run.py','6409649ccd18fd4feab5c80a7ef189017f65476cc069694bcbf909038d7e4cff'),(P/'source-manifest.json','cf5a9b203599b2af0d249a55699c08ef76bf57874595a2d5b1969f2df7f6df6c'),(P/'src/DiophantineConsistency/Norm38CurrentJonesStatic.lean','a70a6b65e73914d47cac0f71c4b0440f5ff53f125834c335164a3b689bfb5f10')]:need(sha(p)==h,'pin '+str(p))
need(sha(P/'source-manifest.json')==sha(O/'source-manifest.json') and sha(P/'src/DiophantineConsistency/Norm38CurrentJonesStatic.lean')==sha(O/'src/DiophantineConsistency/Norm38CurrentJonesStatic.lean'),'same source')
s=(P/'src/DiophantineConsistency/Norm38CurrentJonesStatic.lean').read_text();need('SharingSeed38.seed CurrentWindowCarry2011.ports' in s and s.count('currentNaturalPorts (V := V)')==2 and s.count('current_seed_zero_iff_static w')==2 and s.count('current_nine_iff (V := V)')==2,'same tuple and witness');need('.mp hnine' in s and ').mpr\n    exact ⟨w' in s,'forward/backward orientation')
pieces=[(BASE,D/'research/nine-sharing-norm38-current-four-cast-instantiation-check/attempt01','bad562eeca80d04d60ede99deb281686134612c3c091230a7326dd850b5deabf','Norm38CurrentFourCastInstantiation'),(J,D/'research/nine-sharing-seed38-current-jones-retry01/attempt01','ca43e7d3588626c70043b8909d6cbf2762784a3132d079ae22d9329485b32d1f','SharingSeed38CurrentJones')];guards=0
for temp,records,pin,n in pieces:
 need(sha(records/'state.json')==sha(temp/'state.json')==pin,'state '+n);v=json.loads((records/'state.json').read_text());need(v['status']=='PASS' and len(v['rows'])==1,'status '+n);r=v['rows'][0];need(r['module']==n and r['deps']['exit']==r['compile']['exit']==0 and r['compile']['stop_reason'] is None and sha(temp/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256'] and sha(temp/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256'],'object '+n)
 for phase in ('deps','compile'):need(sha(temp/(n+'-'+phase+'.txt'))==sha(records/(n+'-'+phase+'.txt'))==r[phase]['log_sha256'],'log '+n+phase)
 for path,x in r['direct_guard'].items():
  guards+=1;q=Path(path)
  if x is None:need(not os.path.lexists(q),'absence '+path)
  else:need(q.is_file() and str(q.resolve())==x['realpath'] and sha(q)==x['sha256'],'guard '+path)
 for path,target in v['overlay_links'].items():need(Path(path).is_symlink() and str(Path(path).resolve())==target,'overlay '+path)
need(not os.path.lexists(BASE/'lib/DiophantineConsistency/SharingSeed38CurrentJones.olean'),'injection collision')
r=(P/'run.py').read_text();need("dep['sha256']==expected and dep['realpath']==str(expected_path.resolve())" in r and "obs['sha256']==expected and obs['realpath']==str(expected_path.resolve())" in r and "obs=row['direct_guard'].get(dep['path'])" in r and "guard(deps)==row['direct_guard']" in r,'producer binding');need("base['rows'][0]['object_sha256']" in r and "jr['object_sha256']" in r and "jlink.symlink_to((JONES/" in r,'selected sources')
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=60);need(q.returncode==0 and json.loads(q.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT','preflight '+q.stderr)
print(json.dumps({'status':'PASS_SCOPED_PRELAUNCH_REVIEW','direct_producers':2,'producer_guard_slots':guards,'scope':'Exact theorem orientation and direct producer binding; no Lean or current-equation equivalence.'},indent=2,sort_keys=True))
