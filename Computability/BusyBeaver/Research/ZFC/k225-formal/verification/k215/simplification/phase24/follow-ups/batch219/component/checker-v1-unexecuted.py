"""Owned detached component check; no canonical or accepted packet writes."""
from pathlib import Path
import hashlib,importlib.util,json,os,re
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
BASIS=Path('/tmp/k215-phase24-check-v3/candidate-build-run1')
PLAN=Path('/tmp/k215-phase24-check-v3/candidate-plan.json')
SOURCE=Path('/tmp/k215-decrement-prefix-nextlead/NeutralPrefixCompose.lean')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
DRIVER=ROOT/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py'
OUT=Path('/tmp/k215-decrement-prefix-component-check-v1')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
fixed={SOURCE:'d5cdf19ed390b4eec9302ff78790b939d37a612a6bcd34b79d30e84208f458f6',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',DRIVER:'a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd',PLAN:'4bda49c298304608bd3196d92a3c748140142e8a649708102d827e690f489505',BASIS/'result.json':'c9bcee3023ea879ad0dcc353d1435aae8aef92963a4b79f51fda1506f518c910'}
for path,h in fixed.items():assert sha(path)==h,path
result=json.loads((BASIS/'result.json').read_text());assert result['status']=='PASS'
assert sha(BASIS/'completed.json')==result['completed_sha256']
done=json.loads((BASIS/'completed.json').read_text());plan=json.loads(PLAN.read_text());rows={r['module']:r for r in plan['modules']}
assert len(done)==len(rows)==230
seen=set();bindings=dict(fixed)
def visit(m):
 if m=='Init':return
 if m in seen:return
 r=rows[m];d=done[m];assert d['status']=='PASS' and not d.get('timed_out',False)
 assert d['source_sha256']==r['source_sha256']
 source=BASIS/'workspace'/Path(*m.split('.')).with_suffix('.lean');obj=BASIS/'objects'/Path(*m.split('.')).with_suffix('.olean')
 for path,h in [(source,r['source_sha256']),(obj,d['object_sha256']),(Path(d['log']),d['log_sha256'])]:
  assert sha(path)==h,path;bindings[path]=h
 assert d['dependencies']=={p:done[p]['object_sha256'] for p in r['imports'] if p!='Init'}
 seen.add(m)
 for parent in r['imports']:visit(parent)
visit('BusyBeaver.ZFC.KHomeReady')
assert not OUT.exists() and not OUT.is_symlink();OUT.mkdir()
workspace=OUT/'workspace';workspace.mkdir();source=workspace/SOURCE.name;source.write_bytes(SOURCE.read_bytes())
obj=OUT/'NeutralPrefixCompose.olean';log=OUT/'compiler.log';record=OUT/'record.json'
argv=[str(LEAN),'-j1','-M12288','--root='+str(workspace),'-o',str(obj),str(source)]
row={'module':'NeutralPrefixCompose','source':str(source),'source_sha256':sha(source),'command':argv,'compiler_sha256':sha(LEAN),'supervisor_sha256':sha(DRIVER),'checker_sha256':sha(__file__),'timeout_seconds':120,'memory_mebibytes':12288,'basis_result_sha256':sha(BASIS/'result.json'),'direct_dependency':done['BusyBeaver.ZFC.KHomeReady']['object_sha256']}
(OUT/'before.json').write_text(json.dumps({'bindings':{str(p):h for p,h in bindings.items()},'dependency_modules':sorted(seen),'component_source_sha256':sha(source)},indent=2)+'\n')
spec=importlib.util.spec_from_file_location('owned_k215_supervisor',DRIVER);driver=importlib.util.module_from_spec(spec);spec.loader.exec_module(driver)
env=os.environ.copy();env['LEAN_PATH']=str(BASIS/'objects');env['LEAN_NUM_THREADS']='1'
assert driver.run_locked(argv,workspace,env,Path('/tmp/proveit-k215-proof-build.lock'),log,120,row,record)
text=log.read_text();assert 'warning:' not in text and 'error:' not in text and 'sorryAx' not in text
expected="'SetTheory.BusyBeaver.ZFC.DecrementPrefixNextLead.neutral_prefix_compose' depends on axioms: [propext, Classical.choice, Quot.sound]"
assert text.strip()==expected,text
for path,h in bindings.items():assert sha(path)==h,path
assert sha(source)==fixed[SOURCE]
receipt={'status':'PASS_DETACHED_COMPONENT_KERNEL_CHECK','source_sha256':sha(source),'object_sha256':sha(obj),'log_sha256':sha(log),'record_sha256':sha(record),'checker_sha256':sha(__file__),'dependency_modules':len(seen),'checked_input_files':len(bindings),'seconds':row['seconds'],'warnings':0,'axiom_profile':['propext','Classical.choice','Quot.sound'],'production_changes':0,'scope':'One new owned theorem only. No paired checker, site certificate, endpoint or performance acceptance. Phase24 frozen sources and accepted evidence unchanged.'}
(OUT/'result.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
