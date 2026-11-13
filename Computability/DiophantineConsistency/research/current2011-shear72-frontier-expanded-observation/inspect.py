from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize
D=Path('research/current2011-shear72-frontier-expanded-observation')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
roots=['/tmp/ipra-rank17-native-n795r_ja/lib','/tmp/ipra-thirteen-endpoint-successor-pair-01/author/lib','/tmp/ipra-thirteen-endpoint-successor-pair-01/peer/lib','/tmp/current2011-ordinary94-six-overlay-20261105/lib','/tmp/current14-standard-fresh-build-20261104/lib','/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib']
names=['HAExpressionNoZeroEquiv','ModelCarrierSpheres','AdaptiveEquationSyntax2011','HAExpressionAssembly','ModelCarrierCurrent','ModelArithmetic','ModelDifferenceRing']
observed={}
for n in names:
 hits=[]
 for root in roots:
  base=Path(root)/'DiophantineConsistency'/n;obj=Path(str(base)+'.olean')
  if obj.is_file():
   companions={}
   for suffix in ['.olean.private','.olean.server','.ilean','.ir']:
    f=Path(str(base)+suffix);companions[suffix]=f.is_file()
   hits.append({'path':str(obj),'realpath':str(obj.resolve()),'sha256':sha256(obj.read_bytes()).hexdigest(),'companions_present':companions})
 observed[n]=hits
state=json.loads(Path('/tmp/ipra-rank17-native-n795r_ja/state.json').read_text())
records=[r for r in state['records'] if r.get('module')=='HAExpressionNoZeroEquiv'];assert len(records)==1
h=records[0];ha=Path('/tmp/ipra-rank17-native-n795r_ja/lib/DiophantineConsistency/HAExpressionNoZeroEquiv.olean')
hsource=Path('Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean')
assert h['exit']==0 and h['source_sha256']==sha256(hsource.read_bytes()).hexdigest() and h['object_sha256']==sha256(ha.read_bytes()).hexdigest()
progress=json.loads(Path('research/thirteen-model-endpoint-successor/progress.json').read_text())
rows=[r for r in progress if r.get('module')=='DiophantineConsistency.ModelCarrierSpheres']
assert {r['side'] for r in rows}=={'author','peer'}
source=Path('Lean/DiophantineConsistency/ModelCarrierSpheres.lean');sourcehash=sha256(source.read_bytes()).hexdigest();spheres=[]
for r in sorted(rows,key=lambda x:x['side']):
 obj=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01')/r['side']/'lib/DiophantineConsistency/ModelCarrierSpheres.olean'
 log=Path(r['log']);assert r['exit']==0 and r['deps_exit']==0 and r['source_sha256']==sourcehash and r['object_sha256']==sha256(obj.read_bytes()).hexdigest() and r['log_sha256']==sha256(log.read_bytes()).hexdigest()
 spheres.append({'side':r['side'],'source_sha256':r['source_sha256'],'object_sha256':r['object_sha256'],'log_sha256':r['log_sha256'],'log_contains_warning':'warning:' in log.read_text(),'direct_deps_stdout':r['deps_stdout']})
assert spheres[0]['object_sha256']==spheres[1]['object_sha256']
base=Path('/tmp/current2011-ordinary94-six-overlay-20261105/lib/DiophantineConsistency/ModelDifferenceRing.olean')
alt=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01/author/lib/DiophantineConsistency/ModelDifferenceRing.olean')
assert base.is_file() and alt.is_file();basehash=sha256(base.read_bytes()).hexdigest();althash=sha256(alt.read_bytes()).hexdigest();assert basehash!=althash
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'roots':roots,'observed':observed,'HA_producer':{'status':state['status'],'recorded_source_sha256':h['source_sha256'],'recorded_object_sha256':h['object_sha256'],'direct_inputs':h['direct_inputs'],'boundary':state['boundary']},'sphere_producer':spheres,'model_difference_ring_overlay_sha256':basehash,'model_difference_ring_sphere_sha256':althash,'byte_mismatch_is_proof_of_lean_incompatibility':False,'transitive_ancestry_authenticated':False,'lean_executed':False},sort_keys=True,indent=2))
