"""Freeze the exact-machine author receipt; reads evidence, never runs Lean."""
from pathlib import Path
import hashlib,importlib.util,json,re,shutil,subprocess,zipfile
R=Path('/home/codex/.codex/worktrees/46be/Proofs');W=Path('/tmp/arithmetic215-actual-private')
B=R/'Computability/DiophantineConsistency/reviews/arithmetic-machine215-replay'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(b,s):
 if not b:raise RuntimeError(s)
def rec(p):return {'path':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
def verify(r):require(sha(r['path'])==r['sha256'],'Hash drift '+r['path'])
spec=importlib.util.spec_from_file_location('parser','/tmp/current-positive-zero2011-closure-plan/plan.py');parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
d=json.loads((W/'dependencies-current.json').read_text());prior=json.load(open('/tmp/current-positive-zero2011-closure-plan/manifest.json'))
verify(d['compiler'])
for x in d['modules']:
 require(sha(x['source'])==x['source_sha256'],'Custom source '+x['module'])
 require(parser.imports(Path(x['source']))==x['imports'],'Custom imports '+x['module'])
 for o in x['objects']:verify(o)
final=[('DecimalMachine215','narrow1'),('DecimalMachine215Checks','narrow1'),
 ('ArithmeticMachineGraph215','stage3'),('ArithmeticMachineGraph215Checks','stage2'),
 ('ArithmeticMachineStep215','stage1'),('ArithmeticMachineStep215Checks','stage2'),
 ('ArithmeticMachineRun215','stage2'),('ArithmeticMachineRun215Checks','stage1')]
records=[];all_reports=[]
for n,stage in final:
 p=W/(n+'-'+stage+'.json');x=json.loads(p.read_text());require(x['exit_code']==0,'Failed final '+n)
 require(sha(x['source'])==x['source_sha256'],'Final source '+n)
 require(sha(x['object'])==x['object_sha256'],'Final object '+n)
 require(sha(x['log'])==x['log_sha256'],'Final log '+n)
 text=Path(x['log']).read_text();require('error:' not in text and 'warning:' not in text,'Final diagnostics '+n)
 reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text,re.S)
 for name,axes in reports:
  require(set(a.strip() for a in axes.split(','))<={'propext','Classical.choice','Quot.sound'},'Unexpected axioms '+name)
 all_reports.extend(reports);records.append({'module':'DiophantineConsistency.'+n,'state':rec(p),**x})
require(len(all_reports)==24,'Expected Decimal2 plus new22 reports')
custom={x['module'] for x in d['modules']}|{x['module'] for x in records}
external=set(dep for x in d['modules'] for dep in x['imports'] if dep not in custom)
for x in records:external.update(dep for dep in parser.imports(Path(x['source'])) if dep not in custom)
boundary=[]
for n in sorted(external):
 rel=Path(*n.split('.')).with_suffix('.olean')
 obj=next((Path(p)/rel for p in prior['external_lean_path'] if (Path(p)/rel).is_file()),None);require(obj is not None,'Missing boundary '+n)
 left,marker,right=str(obj).partition('/.lake/build/lib/lean/')
 src=Path(left)/Path(right).with_suffix('.lean') if marker else Path(d['compiler']['path']).parent.parent/'src/lean'/rel.with_suffix('.lean')
 boundary.append({'module':n,'object':rec(obj),'companions':[rec(Path(str(obj)+s)) for s in ('.private','.server') if Path(str(obj)+s).exists()], 'observed_source':rec(src) if src.is_file() else None})
traces=json.load(open('/tmp/arithmetic215-foundation-trace-inputs.json'))
values=dict(line.rstrip('\n').rsplit('\t',1) for line in Path('/tmp/arithmetic215-foundation-lake-hashes.tsv').read_text().splitlines())
checked=0
for x in traces:
 require(sha(x['trace'])==x['trace_sha256'],'Trace drift')
 require(sha(x['source'])==x['source_sha256'],'Foundation source')
 require(values[x['source']]==x['expected_source_lake_hash'],'Foundation source trace mismatch');checked+=1
 require(x['compiler']==['Lean 4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35'],'Foundation compiler')
 for o in x['objects']:
  verify(o);require(values[o['path']]==o['expected_lake_hash'],'Foundation output trace mismatch');checked+=1
require(checked==475,'Foundation count')
reg=Path('/tmp/current-positive-zero2011-decimal-import-regression/state.json');rs=json.loads(reg.read_text());require(rs['status']=='PASS','Regression incomplete')
require(len(rs['completed'])==2,'Regression count')
for x in rs['completed']:
 require(x['exit_code']==0,'Regression failure');verify(x['source']);verify(x['object']);verify(x['log'])
result={'status':'PASS','scope':'Eight actual-machine leaves freshly replayed; 124 cached custom prerequisites authenticated. Separate two-leaf native regression, not a new native full closure.',
 'source_snapshot':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'compiler':d['compiler'],'dependencies':rec(W/'dependencies-current.json'),'fresh':records,'external_boundary':boundary,
 'counts':{'cached_custom':124,'fresh_machine_leaves':8,'custom_total':132,'foundation_traced':95,'foundation_hash_matches':475,'external_direct_boundary':len(boundary),'machine_axiom_reports':24,'separate_native_regression':2},
 'foundation_commit':d['foundation_commit'],'regression':rec(reg),'import_change':rec(W/'DecimalMachine215-import-only.json')}
(W/'final.json').write_text(json.dumps(result,indent=2)+'\n')
B.mkdir(parents=True,exist_ok=True)
files=[W/'finalize.py',W/'compile.py',W/'compile-before.py',W/'endpoint_regression.py',W/'final.json',W/'dependencies.json',W/'dependencies-current.json',W/'DecimalMachine215-import-only.json',Path('/tmp/FoundationTraceHashes.lean'),Path('/tmp/arithmetic215-foundation-trace-inputs.json'),Path('/tmp/arithmetic215-foundation-lake-hashes.tsv'),Path('/tmp/zfc-arithmetic-run-rotation240/run2/verification.json'),reg]
for p in files:
 name='regression-state.json' if p==reg else 'legacy-rotation240-verification.json' if p.name=='verification.json' else p.name
 q=B/name;require(not q.exists(),'Durable evidence exists '+name);shutil.copyfile(p,q)
with zipfile.ZipFile(B/'logs-and-traces.zip','w',compression=zipfile.ZIP_DEFLATED) as z:
 for p in sorted(W.glob('*')):
  if p.suffix in ['.log','.time'] or re.match(r'(ArithmeticMachine|DecimalMachine).*\.json$',p.name):z.write(p,'machine/'+p.name)
 for p in reg.parent.iterdir():
  if p.suffix in ['.log','.time']:z.write(p,'regression/'+p.name)
 for x in traces:z.write(x['trace'],'foundation-traces/'+x['module']+'.trace')
 z.write(W/'NarrowImports.lean','machine/NarrowImports.lean')
with zipfile.ZipFile(B/'logs-and-traces.zip') as z:require(z.testzip() is None,'Archive corruption')
manifest=[rec(p) for p in sorted(B.iterdir())];(B/'BUNDLE.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(result['counts']));print('final',sha(B/'final.json'));print('bundle',sha(B/'BUNDLE.json'))
