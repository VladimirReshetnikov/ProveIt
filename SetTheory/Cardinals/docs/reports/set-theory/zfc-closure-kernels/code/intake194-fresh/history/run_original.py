from pathlib import Path
import sys,subprocess,shutil,json,time,os,difflib,hashlib
P=Path(__file__).resolve().parent; packet=P/'extracted/K217_Exposed_Marker';out=P/'fresh1';out.mkdir(exist_ok=False)
copy=out/'packet';shutil.copytree(packet,copy);logs=out/'logs';logs.mkdir();results=out/'outputs';results.mkdir();hist=out/'history';hist.mkdir()
fixed=copy/'appendix/fixed_core/verify_fixed_core.py';original=fixed.read_text();old="manifest=json.loads((P/'provenance.json').read_text())\nfor r in manifest['files']:\n    assert sha((P/r['artifact']).read_bytes())==r['sha256'],('input identity',r['artifact'])\n";assert original.count(old)==1
adapted=original.replace(old,'# Intake adapter: the delivery provenance-manifest loop is not executed.\n');(hist/'verify_fixed_core.original.py').write_text(original);fixed.write_text(adapted);(hist/'manifest-loop-omitted.diff').write_text(''.join(difflib.unified_diff(original.splitlines(True),adapted.splitlines(True),fromfile='verify_fixed_core.original.py',tofile='verify_fixed_core.py')))
shutil.copyfile(Path(__file__),out/'run.py');env=dict(os.environ);env.pop('PYTHONOPTIMIZE',None);env['PYTHONDONTWRITEBYTECODE']='1'
jobs=[('construct',[sys.executable,'-B',str(copy/'code/construct217.py'),'--baseline-table',str(copy/'machine/baseline218.native.tm'),'--baseline-source',str(copy/'machine/baseline_sites218.json'),'--output',str(results/'rebuilt')]),('four-cases',[sys.executable,'-B',str(copy/'code/check_fold217_four_cases.py'),'--old',str(results/'rebuilt/prefold218.native.tm'),'--new',str(results/'rebuilt/k217.native.tm'),'--output',str(results/'four-cases.json')]),('fixed-core',[sys.executable,'-B',str(fixed),str(fixed.parent),'--output',str(results/'fixed-core.json')])]
rec={'status':'RUNNING','scope':'Three new selected leaves on copy, source-reviewed omission of provenance-manifest loop only; no runtime, startup, parent wrapper, checksum manifest or proof assistant.','jobs':[]}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name,argv in jobs:
 t=time.monotonic()
 with(logs/(name+'.stdout')).open('w')as stdout,(logs/(name+'.stderr')).open('w')as stderr:
  try:r=subprocess.run(argv,cwd=copy,stdout=stdout,stderr=stderr,timeout=60,env=env);rc=r.returncode;timed=False
  except subprocess.TimeoutExpired:rc=None;timed=True
 rec['jobs'].append({'name':name,'argv':argv,'cwd':str(copy),'code':rc,'timeout':timed,'cap_seconds':60,'seconds':time.monotonic()-t,'script_sha256':sha(Path(argv[2]))});(out/'actual.json').write_text(json.dumps(rec,indent=2)+'\n');print(name,rc,flush=True)
 if rc!=0:rec['status']='FAILED';(out/'actual.json').write_text(json.dumps(rec,indent=2)+'\n');raise SystemExit(1)
a=json.loads((results/'rebuilt/reconstruction.json').read_text());b=json.loads((results/'four-cases.json').read_text());c=json.loads((results/'fixed-core.json').read_text())
assert a['status']=='EXACT_K217_CONSTRUCTION_PASS' and a['working_states']==217 and a['transition_rows']==434
assert b['status']=='INDEPENDENT_LITERAL_FOUR_CASE_FOLD_PASS' and b['unchanged_mapped_rows']==432 and len(b['cases'])==4 and b['negative_control']['status']=='REJECTED'
assert c['status']=='EXACT_FIXED_CORE_SOURCE_RECONSTRUCTION_PASS' and [x['metrics']['dag_nodes']for x in c['reports']]==[211,210,210]
for f in ('k217.native.tm','k217.tm','sites217.json','prefold218.native.tm'):assert(results/'rebuilt'/f).read_bytes()==(packet/'machine'/f).read_bytes()
assert c==json.loads((packet/'appendix/fixed_core/source_receipt.json').read_text())
rec['status']='THREE_SELECTED_LEAVES_AND_EXPECTED_GATES_PASS';rec['checks']={'four_rebuilt_artifacts_exact':True,'four_local_cases':True,'negative_control_rejected':True,'fixed_core_entire_receipt_equals_delivered':True};(out/'actual.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec['status'])
