"""Pure data controls for recursive provider resolution, no real archive/capture/kernel."""
from pathlib import Path
import copy,importlib.util,json,sys
sys.dont_write_bytecode=True
P=Path('/tmp/k215-phase8-legacy-publication');O=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('legacy_evidence',P/'evidence.py');e=importlib.util.module_from_spec(sp);sp.loader.exec_module(e)
rs=[]
def check(name,fun,reject=False):
 try:fun()
 except (AssertionError,KeyError):assert reject,name
 else:assert not reject,name
 rs.append({'name':name,'expected':'reject'if reject else'accept','status':'PASS'})
J=lambda x:(json.dumps(x)+'\n').encode();mod='Example.A';src=b'import Init\n';log=b''
rec={'module':mod,'source_sha256':e.digest(src),'object_sha256':'0'*64,'log_sha256':e.digest(log),'dependencies':{}}
base={'execution/completed.json':J({mod:rec}),'execution/sources/Example/A.lean':src,'execution/logs/Example.A.log':log}
primary={'execution/completed.json':J({mod:rec}),'execution/sources/Example/A.lean':src,'execution/reused-log-origins.json':J({mod:{'basis_member':'execution/logs/Example.A.log','sha256':e.digest(log)}}),'review/basis-reference.json':J({'tag':'synthetic'})}
saved_reference=e.reference;e.reference=lambda *_:base
check('recursive_primary_log',lambda:e.primary_material(primary,mod,O))
for field in ['source_sha256','object_sha256','log_sha256','dependencies']:
 def bad(field=field):
  p=copy.deepcopy(primary);r={**rec,field:({'X':'0'*64}if field=='dependencies'else'1'*64)};p['execution/completed.json']=J({mod:r});e.primary_material(p,mod,O)
 check('changed_primary_'+field,bad,True)
wrong=copy.deepcopy(primary);wrong['execution/reused-log-origins.json']=J({mod:{'basis_member':'wrong','sha256':e.digest(log)}})
check('wrong_primary_log_origin',lambda:e.primary_material(wrong,mod,O),True)
check('primary_depth_bound',lambda:e.primary_material(primary,mod,O)if False else e.primary_log(primary,mod,O,8),True)
leaf={'execution/completed.json':J({mod:rec}),'execution/attempts/01-A/record.json':J(rec),'execution/attempts/01-A/A.lean':src,'execution/attempts/01-A/compiler.log':log}
legacy={'execution/completed.json':J({mod:rec}),'publication/references.json':J({'phase7_legacy':{'tag':'synthetic'}})}
e.reference=lambda *_:leaf
check('recursive_legacy_material',lambda:e.legacy_material(legacy,mod,O))
wrong=copy.deepcopy(leaf);wrong['execution/attempts/02-A/record.json']=J(rec)
check('ambiguous_legacy_origin',lambda:e.legacy_material(wrong,mod,O),True)
wrong=copy.deepcopy(leaf);wrong['execution/attempts/01-A/compiler.log']=b'changed'
check('changed_legacy_log',lambda:e.legacy_material(wrong,mod,O),True)
wrong=copy.deepcopy(legacy);wrong['execution/completed.json']=J({mod:{**rec,'object_sha256':'1'*64}})
check('changed_recursive_legacy_object',lambda:e.legacy_material(wrong,mod,O),True)
check('legacy_depth_bound',lambda:e.legacy_material(legacy,mod,O,8),True)
e.reference=saved_reference
text='\n'.join("'%s' depends on axioms: [propext, Quot.sound]"%n for n in e.CLIENTS)
check('exact_five_reports',lambda:e.reports(text))
for name,s in [('wrong_namespace',text.replace('LegacyAudit.','Other.')),('extra_axiom',text.replace('Quot.sound','Unknown')),('warning',text+'\nwarning: x'),('error',text+'\nerror: x'),('sorry',text+'\nsorryAx')]:check(name,lambda s=s:e.reports(s),True)
check('regular_text_path',lambda:None if e.safe('sources/A.lean')else(_ for _ in ()).throw(AssertionError()))
for name in ['proof.olean.private','proof.olean.server','proof.ilean','x.pyo','x.vo','x.o','x.so','x.a','x.glob','../escape','/absolute','x\\y']:
 check('forbidden_'+name,lambda name=name:None if not e.safe(name)else(_ for _ in ()).throw(AssertionError()))
record={'status':'PASS_INDEPENDENT_PURE_METADATA_CONTROLS','positive':sum(r['expected']=='accept'for r in rs),'negative':sum(r['expected']=='reject'for r in rs),'cases':rs,'evidence_sha256':e.sha(P/'evidence.py'),'script_sha256':e.sha(Path(__file__)),'scope':'Synthetic recursive provider fixtures with a temporary data-only reference stub, exact report names, and path checks. No actual capture, local predecessor archive reading, saved/live audit, compiler or canonical writes.'}
(O/'controls-result.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:v for k,v in record.items()if k!='cases'},indent=2))
