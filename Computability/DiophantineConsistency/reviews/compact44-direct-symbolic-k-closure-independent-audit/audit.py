#!/usr/bin/env python3
"""Independent no-Lean review of the direct symbolic-K source closure."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
BASE=Path(__file__).resolve().parents[2];ROOT=BASE.parents[1];R=BASE/'research/ordinary12-ipra-bridge';PLAN=R/'compact44-direct-symbolic-k-closure-plan';EVIDENCE=R/'compact44-direct-symbolic-k-prototype/evidence';AUDIT=BASE/'reviews/compact44-graph-derived-radix-independent-audit';PARENT=Path('/tmp/ipra-compact-graph-derived-radix-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
PINS={PLAN/'README.md':'ef2d212f4a036be839fb4cb297a07745afc7d02e5b773c82ab47925e06c44d21',PLAN/'scan.py':'74a038b974bae4c745dca3ae7ff6af489bc0798b09d82b4a6a93924ca9430429',PLAN/'scan.json':'e09c94bcda39978c52f920c6aa682d95c9993d0bed10628a45d2e6988ced461c',PLAN/'observation.json':'da5ec001745843f935b3b6ea3a7e5f0473e84a3603f9c5bd9052c699a456dec4',AUDIT/'CHECK.json':'2a71f758002a114db6e02b406755cb8ce5da4f4e6309ff3683aac4d681a15fdc',AUDIT/'terminal-observation.json':'111f0b17cc873126d6c55fa40387c763ccfe5a7f616e03bd87d13fe3359e4c5b',EVIDENCE/'progress.json':'6ac155a7dbd40c195f86c365c65a6f531c70ac120731c267c77626c0979dafbe',EVIDENCE/'observation.json':'7f6e3bd84e7fc522a10fe6d6913be341cc31ddba043e95a21330ec93b441544c'}
EXPECTED=[('Compact943Data',['ArithmeticWindowDigits'],[('row_bounds',{'propext','Quot.sound'}),('rows_length',set()),('row_widths',set())]),('CompactCoefficientMass',['Compact943Data'],[(x,{'propext'}) for x in ('values_in_range','selector_mass_exact','copy_mass_exact','coefficient_mass_exact','stencil_mass_exact','triple_stencil_below_half','predecessor_slack','heterogeneous_mass_slack')]),('CompactSymbolicKernel',['CompactCoefficientMass'],[('position_lt_target',{'propext','Quot.sound'}),('row_lt_target',set())]),('CompactSymbolicKernelCast',['CompactSymbolicKernel','ArithmeticStandardCasts'],[('cast_reflected_sum',{'propext','Classical.choice','Quot.sound'})]),('CompactSymbolicKernelGeneric',['CompactSymbolicKernelCast'],[('cast_kernel_generic',{'propext','Classical.choice','Quot.sound'})]),('CompactSymbolicKernelOpaque',['CompactSymbolicKernelGeneric'],[('cast_paramKernel',{'propext','Classical.choice','Quot.sound'})]),('CompactDirectParamGraphDraft',['CompactSymbolicKernelOpaque','CompactGraphDerivedRadix'],[('direct_graph_digits',{'propext','Classical.choice','Quot.sound'})])]
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,msg):
 if not c:raise ValueError(msg)
def slots(stem):
 out={}
 for suffix in SUFFIXES:
  p=Path(str(stem)+suffix)
  if os.path.lexists(p):need(p.is_file(),'invalid slot '+str(p));out[str(p)]={'sha256':H(p),'realpath':str(p.resolve())}
  else:out[str(p)]=None
 return out
for p,h in PINS.items():need(H(p)==h,'pin '+str(p))
x=json.loads((PLAN/'scan.json').read_bytes());ob=json.loads((PLAN/'observation.json').read_bytes());need(x['status']=='PRELIMINARY_DIRECT_SYMBOLIC_K_CLOSURE_NOT_A_BUILD' and ob['normal_observed_exit']==0 and ob['optimized_observed_exit']==1 and ob['lean_launched'] is False and ob['scan_sha256']==PINS[PLAN/'scan.json'],'plan observation')
a=json.loads((AUDIT/'CHECK.json').read_bytes());ao=json.loads((AUDIT/'terminal-observation.json').read_bytes());need(a['status']=='PASS_INDEPENDENT_COMPACT44_GRAPH_DERIVED_RADIX_AUDIT' and a['recorded_outer_exit']==0 and type(ao['observed_exit']) is int and ao['observed_exit']==0 and ao['check_sha256']==PINS[AUDIT/'CHECK.json'] and ao['lean_launched'] is False,'parent audit receipt')
run=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],capture_output=True,timeout=180);need(run.returncode==0 and not run.stderr and run.stdout==(PLAN/'scan.json').read_bytes(),('plan rerun',run.returncode,run.stderr))
opt=subprocess.run([sys.executable,'-O','-I','-S','-B',str(PLAN/'scan.py')],capture_output=True,timeout=30);need(opt.returncode==1 and not opt.stdout and b'requires nonoptimized' in opt.stderr,'optimized scan rejection')
libs=[PARENT/s/'lib' for s in ('author','peer')];inventories=[{p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()} for lib in libs];need(set(inventories[0])==set(inventories[1]) and len(inventories[0])==143,'inventory paths')
need(len(x['objects'])==143 and len({r['path'] for r in x['objects']})==143,'inventory rows')
for r in x['objects']:
 rel=r['path'];need(rel in inventories[0] and H(inventories[0][rel])==r['sha256']==H(inventories[1][rel]) and str(inventories[0][rel].resolve())==r['author_resolved'] and str(inventories[1][rel].resolve())==r['peer_resolved'],'inventory '+rel)
progress=json.loads((EVIDENCE/'progress.json').read_bytes());eo=json.loads((EVIDENCE/'observation.json').read_bytes());need(len(progress)==7 and eo['status']=='AUTHOR_ONLY_DIRECT_SYMBOLIC_K_GRAPH_EXPLORATION' and eo['outer_session']==60092 and eo['observed_exit']==0 and eo['progress_sha256']==PINS[EVIDENCE/'progress.json'],'author observation')
need(len(x['source_order'])==7,'source count');report_records=[]
for row,(name,imports,reports),pr in zip(x['source_order'],EXPECTED,progress):
 src=Path(row['source']);need(row['module']=='DiophantineConsistency.'+name and H(src)==row['source_sha256'] and pr['module']==name and pr['source_sha256']==row['source_sha256'],'source '+name)
 blob=subprocess.run(['git','show',row['source_commit']+':'+src.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True,timeout=30).stdout;need(hashlib.sha256(blob).hexdigest()==row['source_sha256'],'source commit '+name)
 expected_imports=['DiophantineConsistency.'+q for q in imports];need(row['imports']==expected_imports==[line[7:] for line in src.read_text().splitlines() if line.startswith('import ')],'imports '+name)
 expected_names=[name+'.'+n for n,_ in reports];actual_names=re.findall(r'^#print axioms\s+(\S+)',src.read_text(),re.M);need(actual_names==expected_names,'source reports '+name)
 log=EVIDENCE/(name+'.log');blob=subprocess.run(['git','show','8ca0d03752:'+log.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True,timeout=30).stdout
 need(hashlib.sha256(blob).hexdigest()==H(log)==pr['log_sha256'] and type(pr['exit']) is int and pr['exit']==0 and pr['stop_reason'] is None,'author log '+name)
 text=log.read_text();parsed=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",text,re.M)
 actual=[(n,{z.strip() for z in ax.split(',') if z.strip()}) for n,ax in parsed];expected=[(name+'.'+n,ax) for n,ax in reports]
 need(actual==expected and not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text),'axiom logs '+name)
 report_records.extend({'name':n,'axioms':sorted(ax)} for n,ax in actual)
direct={};targets={}
for lib in libs:
 available={str(Path(s).with_suffix('')).replace('/','.') for s in inventories[0]}
 for row in x['source_order']:
  need(all(dep in available for dep in row['imports']),'topological imports '+row['module'])
  stem=lib/Path(*row['module'].split('.'));z=slots(stem);need(all(v is None for v in z.values()),'target occupied '+str(stem));targets.update(z);available.add(row['module'])
 for name in ('ArithmeticWindowDigits','ArithmeticStandardCasts','CompactGraphDerivedRadix'):
  stem=lib/'DiophantineConsistency'/name;need(Path(str(stem)+'.olean').is_file(),'direct '+str(stem));direct.update(slots(stem))
need(len(direct)==60 and direct==x['external_direct_slots'] and len(targets)==140 and targets==x['target_slots'],'direct/target slots')
need(Path(str(PACKAGE/'Init')+'.olean').is_file() and slots(PACKAGE/'Init')==x['init_slots'] and len(x['init_slots'])==10,'Init slots')
need(len(report_records)==17,'report count')
print(json.dumps({'status':'PASS_INDEPENDENT_DIRECT_SYMBOLIC_K_CLOSURE','reviewed_commit':'d887612e55','source_modules':7,'parent_objects_per_side':143,'direct_companion_slots':60,'target_slots':140,'init_slots':10,'author_exploratory_reports':report_records,'source_scan_sha256':PINS[PLAN/'scan.json'],'parent_audit_sha256':PINS[AUDIT/'CHECK.json'],'normal_scan_exit':0,'optimized_scan_exit':1,'scope':'Point-in-time seven-source/provider closure and author-log report inspection; parent audit not rerun, no paired build, retained-byte or display binding, decoder, machine or internal iPRA proof.'},indent=2,sort_keys=True))
