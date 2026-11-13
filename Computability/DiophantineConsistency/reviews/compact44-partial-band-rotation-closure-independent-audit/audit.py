#!/usr/bin/env python3
"""Independent source and same-side inventory review; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S -B')
REPO=Path.cwd();ROOT=REPO/'Computability/DiophantineConsistency';BASE=ROOT/'research/ordinary12-ipra-bridge';PLAN=BASE/'compact44-partial-band-rotation-closure-plan';OLD=BASE/'compact44-partial-band-closure-plan';REVIEW=ROOT/'reviews/compact44-partial-band-closure-independent-audit';HERE=Path(__file__).resolve().parent;PARENT=Path('/tmp/ipra-compact-coefficient-decomposition-pair-01')
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
need(h(PLAN/'scan.json')=='0bc9f86e40d08f2d40d27b84c1cc6b4b703082b61c45003b61469decd6fbe7ae','reviewed scan drift')
p=json.loads((PLAN/'scan.json').read_bytes());b=json.loads((OLD/'scan.json').read_bytes());review=json.loads((REVIEW/'CHECK.json').read_bytes());obs=json.loads((PLAN/'terminal-observation.json').read_bytes())
need(p['status']=='PRELIMINARY_PARTIAL_BAND_ROTATION_SOURCE_CLOSURE_NOT_A_BUILD' and p['objects_per_side']==126 and obs['observed_exit']==0 and obs['optimized_observed_exit']==1 and obs['lean_launched'] is False and obs['scan_sha256']==h(PLAN/'scan.json'),'scan observation schema')
need((HERE/'observations/scan-rerun.stdout').read_bytes()==(PLAN/'scan.json').read_bytes() and not (HERE/'observations/scan-rerun.stderr').read_bytes(),'rerun mismatch')
need(h(OLD/'scan.json')==p['base_scan_sha256']=='448e3d7be056a54908a0d79f5b5e1dce186d209b96fa752b28414cc1f3abde0d' and h(REVIEW/'CHECK.json')==p['base_review_sha256']=='1950866b6ca64631c9837fce924f0e8663c345525945f9364b304454686be667','base pins')
need(review['status']=='PASS_INDEPENDENT_PARTIAL_BAND_SOURCE_CLOSURE' and review['plan_commit']=='7ae590be72','base review schema')
first=p['first_source'];second=p['second_source'];need(first['module']=='DiophantineConsistency.CompactPartialBand' and first['sha256']=='26b73b92c91baef599ab9d473965af940b9b39ae81d76f0979ed80129109ba0f' and first['source']==b['source'] and first['sha256']==b['source_sha256'] and b['source_commit']=='7dea2a8f40','first source pin')
need(second['module']=='DiophantineConsistency.CompactPartialBandRotation' and second['source_commit']=='6fde7b8487' and second['sha256']=='a74f981ea103fabce4163336233071018bbba7a445db05a67ee7207af8cc1438','second source pin')
for row,commit,imports,reports in [(first,'7dea2a8f40',['DiophantineConsistency.CompactCoefficientDecoder','DiophantineConsistency.ArithmeticCyclicWord'],['CompactPartialBand.band_decomposition']),(second,'6fde7b8487',['DiophantineConsistency.CompactPartialBand'],['CompactPartialBandRotation.band_rotation_congr','CompactPartialBandRotation.band_column'])]:
 src=Path(row['source']);need(src.is_file() and h(src)==row['sha256'],('current source',str(src)));old=subprocess.run(['git','show',f'{commit}:{src.relative_to(REPO)}'],capture_output=True,check=True,timeout=15).stdout;need(hashlib.sha256(old).hexdigest()==row['sha256'],('commit source',str(src)));text=src.read_text();need([x[7:] for x in text.splitlines() if x.startswith('import ')]==imports==row['imports'],('imports',str(src)));need(re.findall(r'^#print axioms\s+(\S+)',text,re.M)==reports==row['reports'],('reports',str(src)))
for side in ('author','peer'):
 lib=PARENT/side/'lib';items={str(x.relative_to(lib)):x for x in lib.rglob('*.olean')};need(len(items)==126 and len(b['objects'])==126,('object count',side))
 for row in b['objects']:
  obj=items.get(row['path']);need(obj is not None and h(obj)==row['sha256'] and str(obj.resolve())==row[side+'_resolved'],('object mismatch',side,row['path']))
for key,count in [('external_direct_slots',40),('first_target_slots',20),('second_target_slots',20),('init_slots',10)]:
 guards=p[key];need(len(guards)==count,('guard count',key))
 for name,old in guards.items():
  obj=Path(name)
  if old is None:need(not os.path.lexists(obj),('unexpected slot',name))
  else:need(obj.is_file() and str(obj.resolve())==old['realpath'] and h(obj)==old['sha256'],('slot drift',name))
need(all(x is None for x in p['first_target_slots'].values()) and all(x is None for x in p['second_target_slots'].values()),'target collision')
print(json.dumps({'status':'PASS_INDEPENDENT_PARTIAL_BAND_ROTATION_SOURCE_CLOSURE','reviewed_commit':'0d23719613','reviewed_scan_sha256':h(PLAN/'scan.json'),'base_source_commit':'7dea2a8f40','rotation_source_commit':'6fde7b8487','base_review_authorship':'The base reviewer authored the first Lean source; that review is independent provider/inventory checking, not an independent mathematical proof.','objects_per_side':126,'external_direct_slots':40,'first_target_slots':20,'second_target_slots':20,'init_slots':10,'report_names':first['reports']+second['reports'],'normal_scan_rerun_session':39117,'normal_scan_rerun_exit':0,'lean_launched':False,'scope':'One radix-aligned finite selector/copy band only; explicit positive period/modulus or word/index assumptions. No full graph column, other-band or fractional temporal residual elimination, Boolean or NoCarry premises, retained K binding, machine or iPRA proof.'},indent=2,sort_keys=True))
