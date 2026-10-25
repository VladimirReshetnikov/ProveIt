"""Recheck just the three residual systems needed by height-one sources.
Archived builders/checkers remain byte-identical; all adapting behavior is here.
"""
from pathlib import Path
import argparse,copy,hashlib,importlib.util,json,tempfile
R=Path(__file__).resolve().parent

def need(ok,text):
 if not ok:raise ValueError(text)
def module(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
parser=argparse.ArgumentParser();parser.add_argument('--common-parent',type=Path,default=R/'common252');parser.add_argument('--bindings',type=Path,default=R/'SOURCE_BINDINGS.json');args=parser.parse_args()
common=args.common_parent.resolve()
pins=json.loads(args.bindings.read_text())
for pin in pins['files']:
 p=common/pin['path'].removeprefix('common252/') if pin['path'].startswith('common252/') else R/pin['path'];need(p.stat().st_size==pin['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==pin['sha256'],'source pin '+pin['path'])
old=R/'height_sources/round19'
checker=module('old19_check',old/'verify.py');builder=module('old19_build',old/'build.py')
routes={old/'sources/common252.json':common/'equation/equation.json',old/'sources/common252_translation.json':common/'equation/translation_certificate.json'}
def routed_read(p):return json.loads(routes.get(p,p).read_text())
checker.load=routed_read;builder.read=routed_read
result={'exposed247':checker.audit('exposed247')};rejected=[]
eq=routed_read(old/'exposed247/equation.json');bad=copy.deepcopy(eq);bad['residuals'][0]['terms'][0][0]+=1
try:checker.audit('exposed247',eq=bad)
except ValueError:rejected.append('exposed247:coefficient')
else:raise ValueError('undetected coefficient')
cert=routed_read(old/'certificates/exposed247.json');bad=copy.deepcopy(cert);next(h for st in bad['stages'] for h in st if h['kind']=='project')['replacement'][0][0]+=1
try:checker.audit('exposed247',cert=bad)
except ValueError:rejected.append('exposed247:restoration')
else:raise ValueError('undetected restoration')
e=builder.initial()
for ops in cert['stages']:e=builder.stage(e,ops)
e['variant']='exposed247';expanded,metrics=builder.result(e)
reconstructed=[]
for name,obj in [('equation.json',e),('expanded_polynomial.json',expanded),('METRICS.json',metrics)]:
 need(builder.raw(obj)==(old/'exposed247'/name).read_bytes(),'exact exposed247 rebuild '+name);reconstructed.append('exposed247/'+name)
old=R/'height_sources/round18';checker=module('old18_check',old/'check_spheres.py');builder=module('old18_build',old/'build_spheres.py')
profiles=['sphere_grouped_centered_merged_odd','sphere_sparse_centered_merged_odd']
with tempfile.TemporaryDirectory()as td:
 temp=Path(td);builder.ROOT=temp/'output';builder.PRIOR=temp/'inputs'
 for name in profiles:
  d=old/name;result[name]=checker.check(d);parent=name.replace('sphere_','strict_').replace('_merged_odd','');source=builder.PRIOR/parent;source.mkdir(parents=True)
  for output,input in [('equation.json','source_equation.json'),('translation_certificate.json','source_translation.json')]:
   (source/output).write_bytes((d/input).read_bytes())
  builder.build(parent,merged=True,odd_square=True)
  for p in (builder.ROOT/name).iterdir():
   need(p.read_bytes()==(d/p.name).read_bytes(),'exact old sphere rebuild '+name+'/'+p.name);reconstructed.append(name+'/'+p.name)
  for label in ['sphere.interval_group.0','shared.frame_definition','radix.odd_square']:
   bad=json.loads((d/'equation.json').read_text());next(r for r in bad['residuals'] if r['label']==label)['terms'][0][0]+=1
   try:checker.check(d,bad)
   except ValueError:rejected.append(name+':'+label)
   else:raise ValueError('undetected sphere corruption')
print(json.dumps({'status':'PASS','optimized':not __debug__,'source_pins':len(pins['files']),'selected':result,'byte_identical_rebuilt_files':reconstructed,'rejected_controls':rejected,'boundary':'Finite source binding/reconstruction; ordinary zero-set proof closure is retained separately.'},indent=2))
