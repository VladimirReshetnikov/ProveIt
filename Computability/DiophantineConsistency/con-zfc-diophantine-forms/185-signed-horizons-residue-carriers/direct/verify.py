#!/usr/bin/env python3
"""Replay all finite construction and algebraic certificates. No zero search."""
import argparse,hashlib,importlib.util,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def loadmodule(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
comp=loadmodule('composition_checker',ROOT/'code/verify_composition.py')
v=loadmodule('projection_checker',ROOT/'inherited/verify_projections_original.py')
poolbuild=loadmodule('pool_builder',ROOT/'code/build_pooling.py')
projbuild=loadmodule('projection_builder',ROOT/'inherited/build_projections_original.py')
def load(p):return json.loads(p.read_bytes())
def enc(a):return(json.dumps(a,sort_keys=True,separators=(',',':'))+'\n').encode()
def require(b,msg):
 if not b:raise ValueError(msg)
def run(rebuild=True,corruptions=True):
 sources=[];profiles=[]
 pins=load(ROOT/'SOURCE_PINS.json')
 for entry in pins['upstream173']:
  data=(ROOT/entry['local_path']).read_bytes();require(hashlib.sha256(data).hexdigest()==entry['sha256'],'Source SHA256 mismatch');require(len(data)==entry['size'],'Source size mismatch');require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==entry['git_blob_sha1'],'Git object identity mismatch')
 for entry in pins['oriented_imports']:require(hashlib.sha256((ROOT/entry['local_path']).read_bytes()).hexdigest()==entry['sha256'],'Oriented import SHA256 mismatch')
 for anchor in ['linear219','linear221']:
  anum=int(anchor[-3:]);parentbase=ROOT/'upstream173/source'/('anchor'+str(anum));poolbuild.SOURCE=parentbase/'equation.json'
  signedparent=load(ROOT/'sources'/anchor/'signed_anchor_parent.json');ac=load(parentbase/'certificate.json')
  for variant in ['all5','staged','paired']:
   receipt=comp.audit(anchor,variant);sources.append(receipt)
   if rebuild:
    eq,cert,metrics=poolbuild.construct(signedparent,variant,ac)
    for filename,obj in [('equation.json',eq),('certificate.json',cert),('metrics.json',metrics)]:require((ROOT/'sources'/anchor/variant/filename).read_bytes()==enc(obj),'Source reconstruction differs: '+anchor+'/'+variant+'/'+filename)
 for path in sorted((ROOT/'certificates').glob('*.json')):
  selection=load(path);base=ROOT/'sources'/selection['anchor']/selection['variant'];raw=(base/'equation.json').read_bytes();pool=load(base/'certificate.json');artifactpath=ROOT/'equations'/path.name;artifact=load(artifactpath)
  receipt=v.verify(raw,pool,selection,artifact,path.stem)
  if rebuild:
   reconstructed=projbuild.build(json.loads(raw),pool,selection,hashlib.sha256(raw).hexdigest());require(enc(reconstructed)==artifactpath.read_bytes(),'Circuit reconstruction differs: '+path.name)
  if corruptions:receipt['corruption_controls']=v.corruption_checks(raw,pool,selection,artifact,path.stem)
  profiles.append(receipt)
 return {'status':'PASS','source_variants':sources,'profiles':profiles,'rebuild':rebuild,'corruption_controls':corruptions,'scope':'Exact finite sources, sixteen power bindings, fourteen canonical-pair bindings, source orientation and frame, pool identities, acyclic pivots, circuit block expansions, degree and coefficient bounds, and input occurrence; unbounded arithmetic and C222/ZF/ZFC calibration remain mathematical proof dependencies.'}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);ap.add_argument('--skip-rebuild',action='store_true');ap.add_argument('--skip-corruptions',action='store_true');a=ap.parse_args();result=run(not a.skip_rebuild,not a.skip_corruptions)
 if a.receipt:a.receipt.write_bytes(json.dumps(result,sort_keys=True,indent=2).encode()+b'\n')
 print(json.dumps({'status':result['status'],'source_variants':len(result['source_variants']),'profiles':len(result['profiles']),'profiles_metrics':[{'name':p['name'],'variables':p['variables'],'degree':p['degree'],'operations':p['binary_operations']} for p in result['profiles']]},indent=2))
