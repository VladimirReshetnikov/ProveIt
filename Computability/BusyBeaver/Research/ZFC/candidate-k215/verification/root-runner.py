from pathlib import Path
import shutil,sys,json,hashlib,time,subprocess,importlib.util
OUT=Path(sys.argv[1]).resolve();OUT.mkdir(parents=True,exist_ok=False)
P=Path('/tmp/k216-permuted-partial-composition')
R=Path('/tmp/zfc-intake197/fresh/parents/K218_Dominated_Rho8_2026-10-20/binary/code')
files={'code/validate_native.py':R/'validate_native.py','code/runtime/symbolic_runtime.py':R/'runtime/symbolic_runtime.py','code/runtime/independent_runtime.py':R/'runtime/independent_runtime.py','code/inputs/legacy_mapping.json':R/'inputs/legacy_mapping.json','candidate.native.tm':P/'allocation210-run2/candidate.native.tm','sites.json':P/'sites-210.json','candidate.tm':P/'held-publication/k215.tm','canonicalization.json':P/'held-publication/canonicalization.json'}
for rel,p in files.items():
 t=OUT/rel;t.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,t)
def hashes():return {rel:hashlib.sha256((OUT/rel).read_bytes()).hexdigest() for rel in files}
before=hashes();(OUT/'before.json').write_text(json.dumps(before,indent=2)+'\n')
spec=importlib.util.spec_from_file_location('v',OUT/'code/validate_native.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
st=v.startup(v.s.r.table(OUT/'candidate.native.tm'),limit=500000)
(OUT/'preflight.json').write_text(json.dumps(st,indent=2)+'\n')
print('PREFLIGHT',json.dumps({k:x for k,x in st.items() if k not in ('trace','one_cells')}),flush=True)
assert st['status']=='CALIBRATED_DIRTY_ROOT_SEED',st['status']
start=time.monotonic();cmd=[sys.executable,'-B',str(OUT/'code/validate_native.py'),str(OUT/'candidate.native.tm'),str(OUT/'sites.json'),str(OUT/'runtime')]
with (OUT/'runtime.log').open('w') as f:
 try:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=360);rc=r.returncode;timed_out=False
 except subprocess.TimeoutExpired:rc=None;timed_out=True
elapsed=time.monotonic()-start;after=hashes();report=json.loads((OUT/'runtime/runtime.json').read_text()) if (OUT/'runtime/runtime.json').exists() else {}
actual={'status':'PASS' if rc==0 and report.get('status')=='UNIVERSAL_MATHEMATICAL_PASS' and report.get('proved_cases')==6176 and report.get('working_states')==215 and not report.get('failures') and before==after else 'FAIL','argv':cmd,'returncode':rc,'timed_out':timed_out,'timeout_seconds':360,'elapsed_seconds':elapsed,'before':before,'after':after,'runtime':{k:x for k,x in report.items() if k not in ('blocks',)}}
(OUT/'actual.json').write_text(json.dumps(actual,indent=2)+'\n');print(json.dumps(actual,indent=2),flush=True)
assert actual['status']=='PASS'
