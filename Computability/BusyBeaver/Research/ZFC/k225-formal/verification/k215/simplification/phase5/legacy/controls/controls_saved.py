"""Disposable archived-record controls with fictional compiler records; no proof tools."""
from pathlib import Path
import contextlib,copy,gzip,hashlib,io,json,subprocess,sys,tarfile
with contextlib.redirect_stdout(io.StringIO()):import controls as C
import evidence as E
P=Path(__file__).resolve().parent;OUT=P/'controls-saved-run1';OUT.mkdir()
base=copy.deepcopy(C.pack);checked=E.validate(base)
manifest={n:{'sha256':E.digest(b),'bytes':len(b)}for n,b in base.items()}
live={**checked,'status':'PASS_LIVE_LEGACY_POST_AUDIT_REVIEW','all199_objects_rehashed_after_audit':True,'basis184_unchanged':True,'result_sha256':E.digest(base['execution/result.json']),'evidence_manifest':manifest}
ref={'scope':'SYNTHETIC CONTROL ONLY','files':{n:'0'*64 for n in ('execution.tar.gz','index.json','result.json','live-review.json')},'original_result_sha256':E.digest(base['execution/basis-result.json'])}
results=[]
def run(name,mutate,expected):
 d=OUT/name;d.mkdir();lr=copy.deepcopy(live);rf=copy.deepcopy(ref);mutate(lr,rf)
 m=copy.deepcopy(base)
 for label,x in [('live-review',lr),('primary-reference',rf)]:m['publication/'+label+'.json']=(json.dumps(x,indent=2)+'\n').encode();E.save(d/(label+'.json'),x)
 with tarfile.open(d/'execution.tar.gz','w:gz')as t:
  for n,b in m.items():
   x=tarfile.TarInfo(n);x.size=len(b);t.addfile(x,io.BytesIO(b))
 E.save(d/'index.json',{n:{'sha256':E.digest(b),'bytes':len(b)}for n,b in m.items()})
 E.save(d/'review.json',{**{k:v for k,v in lr.items()if k!='evidence_manifest'},'archive_sha256':E.sha(d/'execution.tar.gz')})
 p=subprocess.run([sys.executable,'-B',str(P/'review_saved.py'),'--packet',str(d),'--output',str(d/'result.json')],capture_output=True,text=True)
 (d/'stdout.log').write_text(p.stdout);(d/'stderr.log').write_text(p.stderr)
 assert (p.returncode==0)==expected,(name,p.returncode,p.stderr)
 results.append({'name':name,'expected_pass':expected,'exit_code':p.returncode,'pass':True})
run('positive',lambda l,r:None,True)
run('wrong_primary_file_keys',lambda l,r:r['files'].pop('index.json'),False)
run('wrong_original_result',lambda l,r:r.__setitem__('original_result_sha256','f'*64),False)
run('false_fresh_warning_total',lambda l,r:l.__setitem__('fresh_project_warnings',999),False)
run('false_typed_count',lambda l,r:l.__setitem__('typed_clients',4),False)
E.save(P/'controls-saved.json',{'status':'PASS_SYNTHETIC_SAVED_READER_CONTROLS','no_compiler':True,'fictional_proof_records':True,'controls':results,'review_saved_sha256':E.sha(P/'review_saved.py'),'script_sha256':E.sha(Path(__file__))})
print(json.dumps(results,indent=2))
