"""Exact local phase9 validation; never import Python from an archive."""
from pathlib import Path
import hashlib,importlib.util,json,sys,tarfile
HERE=Path(__file__).resolve().parent
PIN='a857c33266e3089dd02541a6a40397f6be9d50544a39f6048467f1983ba3a14a'
digest=lambda b:hashlib.sha256(b).hexdigest()
def load(repo):
 raw=(HERE/'basis-reference.json').read_bytes();assert digest(raw)==PIN;ref=json.loads(raw);packet=Path(repo)/ref['repository_relative_directory']
 def pins():
  result={}
  for name,pin in ref['files'].items():
   p=packet/name;assert p.is_file()and not p.is_symlink();b=p.read_bytes();assert len(b)==pin['bytes']and digest(b)==pin['sha256'];result[name]=b
  return result
 files=pins();modules=[('basis_reference','basis_reference.py'),('evidence','evidence.py'),('auxiliary','auxiliary.py'),('_phase9_reader','review_saved.py')];old={n:sys.modules.get(n)for n,_ in modules};bytecode=sys.dont_write_bytecode
 try:
  sys.dont_write_bytecode=True
  for name,filename in modules:
   spec=importlib.util.spec_from_file_location(name,packet/filename);mod=importlib.util.module_from_spec(spec);sys.modules[name]=mod;spec.loader.exec_module(mod)
  checked=sys.modules['_phase9_reader'].review(packet,basis_repo=repo,repo=None)
  assert checked['status']=='PASS_SAVED_PHASE9_PACKET'and not checked['current_sources_checked']
  helper=sys.modules['evidence'];members={};index=json.loads(files['index.json'])
  with tarfile.open(packet/'execution.tar.gz','r:gz')as stream:
   for item in stream:
    helper.safe_name(item.name);assert item.isfile()and item.name not in members;data=stream.extractfile(item).read();assert index[item.name]=={'sha256':digest(data),'bytes':len(data)};members[item.name]=data
  assert helper.manifest(members)==index
  ancestor,_,_=sys.modules['basis_reference'].validate(repo,members['review/basis-reference.json'])
  data={'member:'+n:b for n,b in members.items()}
  for path,route in json.loads(members['path-map.json']).items():
   value=(members if route['storage']=='packet'else ancestor)[route['member']];assert digest(value)==route['sha256']and len(value)==route['bytes'];data['path:'+path]=value
  assert pins()==files
  return data,checked,helper
 finally:
  sys.dont_write_bytecode=bytecode
  for name,value in old.items():
   if value is None:sys.modules.pop(name,None)
   else:sys.modules[name]=value
