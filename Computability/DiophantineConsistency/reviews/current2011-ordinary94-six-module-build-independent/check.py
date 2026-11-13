#!/usr/bin/env python3
import ast,hashlib,json,os,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-ordinary94-six-module-build';S=D/'research/current2011-ordinary67-94-syntax-fresh';Q=D/'reviews/normalized106-fresh-base-model-independent'; overlay=Path('/tmp/current2011-ordinary94-six-overlay-20261105/lib');overlayrec=overlay.parent/'overlay.json'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
need(H(P/'survey-result-snapshot.json')=='d923d399d157acadabe033138791583b34b52c2f992e0800b04e652bb05ce821','survey pin');survey=json.loads((P/'survey-result-snapshot.json').read_text());order=survey['minimal_extra_order'];need(len(order)==6,'six order');need(H(overlayrec)=='607e33f8290b8c4338e844b59334b0ad7b635c7e7b699c40a74e3274c4714e1e','overlay receipt');ol=json.loads(overlayrec.read_text());need(len(ol['links'])==1016 and ol['syntax_sha256']=='b0a4f82738eb22627c3631b0cfc48053b8051682fb7ed5c2b958281a7e29c76b','overlay provenance')
for path,target in ol['links'].items():
 p=Path(path);need(p.is_symlink() and str(p.resolve())==target,'overlay link '+path)
inputs=[(S/'attempt01','061333b8a936cbb09fb494e9e445c3089e24db650d4ca88404be673093794130','907125a990f44180d3d926778699ce336fc5e6a070d291b90c429eb21f356d60',63168),(P/'attempt01','380405fde37344135b7cbeded449412cfdd905c1ccc04aa19e45c92274721c27','766e08ea65b0f19a74672009c054328e82d9fa1b31865d81ca7f2b8539d95a33',85683),(P/'attempt02','16ed96a09e44cbaa63c9592560dab2f340bf908b18ccd8d08097d3734782f974','6cd5e9042986d6ce8832b5da6e406695f27ed2d4aafa7e36cdf590baec196590',84629),(P/'attempt03','08a9bb766e805be1f647170080c0156bfc7fc9237d25dceeb1b079debfbb0a11','d122abf3ec5ab91b7150e5e0e7f0889b8b9208c14a10d1361793ce81c5a6c783',61025),(P/'attempt04','fd0eb4fb389ac27d1d6c42ff3b3a22e9386edff0774de6a6e85861884d571a80','29f14563baf9a769bf2b7f793640fac1a3b23d45dd7a0edd1f6e255d3eb28aff',40735),(P/'attempt05','d2848efcaa6b3aadc58dec758a33e08e5999e84ec4d1020a431a2736eac39fb3','ca02c22fe36ccf31866e792cba15c976dc44041e93c010af05b18280674d09ae',7791)]
slots=0;objects=[]
for idx,(q,rh,th,sid) in enumerate(inputs):
 need(H(q/'result.json')==rh and H(q/'outer-observation.json')==th,'receipt pin');r=json.loads((q/'result.json').read_text());t=json.loads((q/'outer-observation.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and t['session_id']==sid and t['observed_outer_exit']==0,'stage exit '+str(idx));need(H(q/'compile.log')==r['log_sha256'] and not (q/'compile.log').read_bytes(),'stage warning-free '+str(idx))
 for n,m in r['guards_after'].items():
  slots+=1;p=Path(m['path'] if m is not None and 'path' in m else n.rsplit(':',1)[-1]);
  if m is None:need(not os.path.lexists(p),'unexpected '+n)
  else:need(p.is_file() and str(p.resolve())==m['realpath'] and H(p)==m['sha256'],'guard '+n)
 name=order[idx];path=Path(r['command'][r['command'].index('-o')+1]);need(H(path)==r['object_sha256'],'stage object');installed=overlay/(name.replace('.','/')+'.olean');need(installed.is_file() and not installed.is_symlink() and H(installed)==r['object_sha256'],'installed object '+name);objects.append({'module':name,'sha256':r['object_sha256'],'session':sid})
 src=Path(r['command'][r['command'].index('-o')-1]);entry=survey['minimal_extra_sources'][name];workspace=D.parent.parent/entry['source']
 # D points at task directory; workspace paths are repository-relative.
 root=next(x for x in P.parents if (x/'lakefile.toml').is_file());workspace=root/entry['source'];need(H(workspace)==entry['source_sha256'],'pinned original source '+name)
 if idx<5:need(H(src)==entry['source_sha256'],'compiled original source '+name)
 else:
  old=workspace.read_text();variant=src.read_text();needle='mul_zero,zero_mul,mul_one,one_mul,';need(old.count(needle)==1 and variant==old.replace(needle,'mul_zero,mul_one,',1),'extraction variant exact diff')
 # Five stage drivers' direct maps are generated from source-declared imports.
 runner=(S/'check01.py') if idx==0 else P/('stage05-retry.py' if idx==5 else f'stage{idx:02d}.py');need(H(runner)==r['runner_sha256'],'runner pin')
 txt=runner.read_text().split('DIRECT = ',1)[1].split('\nOUT =',1)[0];direct=ast.literal_eval(txt);need({x.replace('/','.') for x in direct}==set(entry['imports']),'direct names '+name)
 for mod,(path,h) in direct.items():
  p=Path(path);need(p.is_file() and H(p)==h and path in r['guards_after'] and r['guards_after'][path]['sha256']==h,'direct input '+mod)
# The rejected original extraction build returned Lean exit 0 but outer failure for lint warnings.
F=P/'attempt05-failed';need(H(F/'result.json')=='0cfaf536fd770b5d4d271acbc906066c782f71d4951c2a954671d5aced019ebb' and H(F/'outer-observation.json')=='5b74dbd05622221baa2c93f7a773993c90fe2074d530cd94dc392e4f28106eb6','failed pins');f=json.loads((F/'result.json').read_text());ft=json.loads((F/'outer-observation.json').read_text());need(f['status']=='FAILED' and f['exit']==0 and ft['session_id']==9401 and ft['observed_outer_exit']==1 and H(F/'compile.log')==f['log_sha256'] and 'warning:' in (F/'compile.log').read_text(),'warning rejection')
need(H(Q/'check.py')=='2f1e8f23caabe818d51ec8f3c56f6752794c9dee755624794cc8fb154a77361f','base audit pin');z=subprocess.run([sys.executable,'-I','-S','-B',str(Q/'check.py')],capture_output=True);need(z.returncode==0 and z.stdout==(Q/'result.json').read_bytes(),'base audit rerun')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_AUDIT','six_stages':objects,'direct_and_producer_slots_rechecked':slots,'overlay_links':len(ol['links']),'warning_rejected_session':9401,'scope':'Recorded source variants, direct provider and overlay checks; no Lean replay, transitive dynamic load trace, or independent base rebuild.'},sort_keys=True,indent=2))
