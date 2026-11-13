#!/usr/bin/env python3
"""Independent source and same-side provider inventory review; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S -B')
REPO=Path.cwd();ROOT=REPO/'Computability/DiophantineConsistency';BASE=ROOT/'research/ordinary12-ipra-bridge';PLAN=BASE/'compact44-two-band-rotation-closure-plan';OLD=BASE/'compact44-partial-band-closure-plan';ROT=BASE/'compact44-partial-band-rotation-closure-plan';REVIEW=ROOT/'reviews/compact44-partial-band-rotation-closure-independent-audit';HERE=Path(__file__).resolve().parent;PARENT=Path('/tmp/ipra-compact-coefficient-decomposition-pair-01')
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
need(h(PLAN/'scan.json')=='01bb70c150497f2c638bb2e7537e93a3d23f6f423eac99cd38929000cca474c8','reviewed scan drift')
p=json.loads((PLAN/'scan.json').read_bytes());base=json.loads((OLD/'scan.json').read_bytes());rotation=json.loads((ROT/'scan.json').read_bytes());review=json.loads((REVIEW/'CHECK.json').read_bytes());obs=json.loads((PLAN/'terminal-observation.json').read_bytes())
need(p['status']=='PRELIMINARY_TWO_BAND_ROTATION_SOURCE_CLOSURE_NOT_A_BUILD' and p['objects_per_side']==126 and type(obs['observed_exit']) is int and obs['observed_exit']==0 and obs['optimized_observed_exit']==1 and obs['lean_launched'] is False and obs['scan_sha256']==h(PLAN/'scan.json'),'scan observation schema')
need((HERE/'observations/scan-rerun.stdout').read_bytes()==(PLAN/'scan.json').read_bytes() and not (HERE/'observations/scan-rerun.stderr').read_bytes(),'scan rerun mismatch')
need(h(ROT/'scan.json')==p['base_scan_sha256']=='0bc9f86e40d08f2d40d27b84c1cc6b4b703082b61c45003b61469decd6fbe7ae' and h(REVIEW/'CHECK.json')==p['base_review_sha256']=='b623a2d6e51d57fdb5838466cb70bcf18a7fa090c0851ad7a08697d466cecde8','base pins')
need(review['status']=='PASS_INDEPENDENT_PARTIAL_BAND_ROTATION_SOURCE_CLOSURE' and review['reviewed_commit']=='0d23719613','base review schema')
rows=p['source_order'];need(len(rows)==3 and rows[:2]==[rotation['first_source'],rotation['second_source']],'source order')
expected=[('DiophantineConsistency.CompactPartialBand','7dea2a8f40','26b73b92c91baef599ab9d473965af940b9b39ae81d76f0979ed80129109ba0f',['DiophantineConsistency.CompactCoefficientDecoder','DiophantineConsistency.ArithmeticCyclicWord'],['CompactPartialBand.band_decomposition']),('DiophantineConsistency.CompactPartialBandRotation','6fde7b8487','a74f981ea103fabce4163336233071018bbba7a445db05a67ee7207af8cc1438',['DiophantineConsistency.CompactPartialBand'],['CompactPartialBandRotation.band_rotation_congr','CompactPartialBandRotation.band_column']),('DiophantineConsistency.TwoBand','d71872eb82','6bf2dc0cf02bc32ccff07cc5cc3b66f271fc86bed01dfc151a07f39893a48908',['DiophantineConsistency.CompactPartialBandRotation'],['TwoBand.bare_congr','TwoBand.add_congr_mod','TwoBand.combined_congr'])]
for row,(module,commit,sha,imports,reports) in zip(rows,expected):
 src=Path(row['source']);need(row['module']==module and row['sha256']==sha and src.is_file() and h(src)==sha,('source',module));old=subprocess.run(['git','show',f'{commit}:{src.relative_to(REPO)}'],capture_output=True,check=True,timeout=15).stdout;need(hashlib.sha256(old).hexdigest()==sha,('commit source',module));text=src.read_text();need([x[7:] for x in text.splitlines() if x.startswith('import ')]==imports==row['imports'],('imports',module));need(re.findall(r'^#print axioms\s+(\S+)',text,re.M)==reports==row['reports'],('reports',module))
for side in ('author','peer'):
 lib=PARENT/side/'lib';items={str(x.relative_to(lib)):x for x in lib.rglob('*.olean')};need(len(items)==126 and len(base['objects'])==126,('object count',side))
 for row in base['objects']:
  obj=items.get(row['path']);need(obj is not None and h(obj)==row['sha256'] and str(obj.resolve())==row[side+'_resolved'],('object mismatch',side,row['path']))
for key,count in [('external_direct_slots',40),('first_target_slots',20),('second_target_slots',20),('third_target_slots',20),('init_slots',10)]:
 guards=p[key];need(len(guards)==count,('guard count',key))
 for name,old in guards.items():
  obj=Path(name)
  if old is None:need(not os.path.lexists(obj),('unexpected slot',name))
  else:need(obj.is_file() and str(obj.resolve())==old['realpath'] and h(obj)==old['sha256'],('slot drift',name))
for k in ('first_target_slots','second_target_slots','third_target_slots'):need(all(x is None for x in p[k].values()),('target collision',k))
print(json.dumps({'status':'PASS_INDEPENDENT_TWO_BAND_ROTATION_SOURCE_CLOSURE','reviewed_commit':'cc5cb7e35e','reviewed_scan_sha256':h(PLAN/'scan.json'),'source_commits':['7dea2a8f40','6fde7b8487','d71872eb82'],'base_review_authorship':'The reviewer of the earlier first-source closure authored that Lean source; the current review independently checks source/provider inventory, not mathematical proof.','objects_per_side':126,'external_direct_slots':40,'target_slots':60,'init_slots':10,'report_names':[n for _,_,_,_,ns in expected for n in ns],'normal_scan_rerun_session':65637,'normal_scan_rerun_exit':0,'lean_launched':False,'scope':'Two radix-aligned finite selector/copy bands and five bare terms under explicit hK, positive period/modulus and graph congruence. The w*C residual stays separate; no fractional temporal alignment, retained K binding, full graph column, machine or iPRA theorem.'},indent=2,sort_keys=True))
