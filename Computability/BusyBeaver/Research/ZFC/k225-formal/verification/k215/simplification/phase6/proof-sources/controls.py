"""Mutation controls for the saved reader; never runs a proof/compiler/machine."""
from pathlib import Path
import json,hashlib,tarfile,gzip,io,tempfile,copy,importlib.util
O=Path(__file__).resolve().parent;S=O/'staged';spec=importlib.util.spec_from_file_location('saved_reader',O/'review_saved.py');reader=importlib.util.module_from_spec(spec);spec.loader.exec_module(reader)
sha=lambda b:hashlib.sha256(b).hexdigest()
with tarfile.open(S/'evidence.tar.gz','r:gz')as t:original={m.name:t.extractfile(m).read()for m in t.getmembers()}
summary=json.loads((S/'summary.json').read_text())
def mutate_json(name,key,value):
 def fn(data):
  d=json.loads(data[name]);d[key]=value;data[name]=(json.dumps(d,indent=2)+'\n').encode()
 return fn
def write(d,data,duplicate=False):
 idx={k:{'sha256':sha(v),'bytes':len(v)}for k,v in sorted(data.items())}
 p=d/'evidence.tar.gz'
 with p.open('wb')as f,gzip.GzipFile(filename='',fileobj=f,mode='wb',mtime=0)as z,tarfile.open(fileobj=z,mode='w')as t:
  items=list(sorted(data.items()))
  if duplicate:items.append(items[0])
  for k,v in items:
   i=tarfile.TarInfo(k);i.size=len(v);i.mode=0o644;t.addfile(i,io.BytesIO(v))
 (d/'index.json').write_text(json.dumps(idx,indent=2)+'\n');s=dict(summary);s.update(archive_sha256=sha(p.read_bytes()),index_sha256=sha((d/'index.json').read_bytes()),members=len(data),expanded_bytes=sum(map(len,data.values())),archive_bytes=p.stat().st_size);(d/'summary.json').write_text(json.dumps(s,indent=2)+'\n')
controls=[
 ('generic failed exit',mutate_json('generic/final/run2/result.json','exit_code',1)),
 ('generic nonstandard report',mutate_json('generic/final/run2/result.json','axiom_reports',[])),
 ('seed syntax failure hidden',mutate_json('seed/final/run2/result.json','status','PASS')),
 ('seed final warning hidden',mutate_json('seed/successor/run3/result.json','warnings',1)),
 ('wrong generic combined source',lambda d:d.__setitem__('generic/final/run2/workspace/BusyBeaver/ZFC/RMNormalizedBisim.lean',b'bad\n')),
 ('wrong normalized count',mutate_json('normalized/comparison.json','normalized_entries',1427)),
 ('wrong normalized root',mutate_json('normalized/comparison.json','root_index',1)),
 ('wrong finite branch count',mutate_json('normalized/comparison.json','local_obligations',{})),
 ('failed generator exit',lambda d: mutate_job(d)),
 ('wrong fast leaf count',mutate_json('fast/run1/result.json','physical_leaf_count',4750)),
 ('missing adoption row',lambda d: drop_adoption(d)),
 ('corrupt adopted source',lambda d: corrupt_adoption(d)),
 ('compiled object member',lambda d:d.__setitem__('accidental.olean',b'object')),
 ('compound private object',lambda d:d.__setitem__('accidental.olean.private',b'object')),
 ('compound server object',lambda d:d.__setitem__('accidental.olean.server',b'object')),
 ('optimized Python object',lambda d:d.__setitem__('accidental.pyo',b'object')),
 ('renamed generic audit client',lambda d:rename_report(d,'generic/final/run2','NormalizedCheckerAudit.default128')),
 ('renamed seed audit client',lambda d:rename_report(d,'seed/successor/run3','KSeed222.seed_of_bundle')),
 ('unsafe member path',lambda d:d.__setitem__('../escape',b'bad')),
]
def rename_report(data,folder,suffix):
 logname=folder+'/compiler.log';rn=folder+'/result.json';old='SetTheory.BusyBeaver.ZFC.'+suffix;new=old+'_renamed'
 data[logname]=data[logname].replace(old.encode(),new.encode());r=json.loads(data[rn]);r['log_sha256']=sha(data[logname])
 r['axiom_reports']=[[new if name==old else name,ax]for name,ax in r['axiom_reports']];data[rn]=(json.dumps(r,indent=2)+'\n').encode()
def mutate_job(data):
 n='fast/run1/result.json';d=json.loads(data[n]);d['jobs'][0]['exit_code']=1;data[n]=json.dumps(d).encode()
def drop_adoption(data):
 n='adoption/adoption.json';d=json.loads(data[n]);d['files'].pop();data[n]=json.dumps(d).encode()
def corrupt_adoption(data):
 a=json.loads(data['adoption/adoption.json']);paths=json.loads(data['paths.json']);data[paths[a['files'][0]['source']]]=b'corrupt\n'
results=[]
with tempfile.TemporaryDirectory(prefix='k215-feature-controls-')as tmp:
 tmp=Path(tmp);pos=tmp/'positive';pos.mkdir();write(pos,original);assert reader.review(pos)['status']=='PASS_SAVED_FEATURE_EVIDENCE';results.append({'name':'repacked positive','accepted':True})
 for i,(name,fn)in enumerate(controls):
  d=tmp/str(i);d.mkdir();data=dict(original);fn(data);write(d,data)
  try:reader.review(d)
  except (AssertionError,KeyError,ValueError,UnicodeError):results.append({'name':name,'rejected':True})
  else:raise AssertionError('accepted mutation '+name)
 d=tmp/'duplicate';d.mkdir();write(d,original,duplicate=True)
 try:reader.review(d)
 except AssertionError:results.append({'name':'duplicate member','rejected':True})
 else:raise AssertionError('accepted duplicate')
r={'status':'PASS','positive':1,'negative':20,'reader_sha256':sha((O/'review_saved.py').read_bytes()),'controls_sha256':sha(Path(__file__).read_bytes()),'archive_sha256':summary['archive_sha256'],'results':results,'compiler_invoked':False};(O/'controls.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
