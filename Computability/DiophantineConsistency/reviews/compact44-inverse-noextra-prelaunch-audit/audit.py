#!/usr/bin/env python3
"""No-Lean exact-byte and fake-child review of corrected inverse/exclusion drivers."""
import ast,hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';R=BASE/'research/ordinary12-ipra-bridge';HERE=Path(__file__).resolve().parent
FILES=[('compact44-inverse-lookup-prototype','6c0618cf46','ec9888b8345faa873f6d419bbcedf5696f06e1f8e5ffc6ad3833353bafcac0e3'),('compact44-model-noextra-prototype','21a02e72e2','6e14d1d6f10172d84b7ca4d7abf171771a8021868a2d2f723f42e0ceb608e12e')]
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def section(code,name):return ast.dump(next(x for x in ast.parse(code).body if isinstance(x,ast.FunctionDef) and x.name==name),include_attributes=False)
def main():
 mods=[]
 for name,old,h in FILES:
  p=R/name/'replay.py';rel=p.relative_to(ROOT).as_posix();new=subprocess.run(['git','show','a2791584e3:'+rel],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;oldbytes=subprocess.run(['git','show',old+':'+rel],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(H(p)==h==hashlib.sha256(new).hexdigest(),'driver bytes '+name)
  for f in ('pins','audit'):need(section(oldbytes.decode(),f)==section(new.decode(),f),'parent preflight function drift '+name+' '+f)
  sp=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);m.pins()
  for path,digest in m.PINS.items():need(H(path)==digest,'input pin '+str(path))
  mods.append(m)
 inv,noextra=mods;need(inv.NAMES==['CompactInverseDraft.inverse_forward','CompactInverseDraft.inverse_image','CompactInverseDraft.inverseLookup_defined'],'inverse reports')
 need([x[0] for x in noextra.REPORTS['CompactForbidden']]==['CompactForbidden.no_east_five_all','CompactForbidden.west_five_extra_all','CompactForbidden.no_east_five','CompactForbidden.west_five_extra','CompactForbidden.five_cannot_have_left'] and [x[0] for x in noextra.REPORTS['CompactNoExtra']]==['CompactNoExtra.extra_forbidden_with_left','CompactNoExtra.cyclic_excludes_extra'],'exclusion report names')
 wordold=subprocess.run(['git','show','6c0618cf46:'+(R/'compact44-marked-word-prototype/replay.py').relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE,text=True).stdout;inverseold=subprocess.run(['git','show','6c0618cf46:'+(R/'compact44-inverse-lookup-prototype/replay.py').relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE,text=True).stdout;need(section(wordold,'audit')==section(inverseold,'audit'),'shared parent preflight')
 controls=[(HERE/'inverse-corrected-fake-review.py',11),(HERE/'model-noextra-fake-review.py',13),(HERE/'inverse-exclusion-guard-review.py',2)]
 observations={}
 for p,n in controls:
  q=subprocess.run([sys.executable,'-I','-S','-B',str(p)],capture_output=True,text=True,timeout=120);need(q.returncode==0 and not q.stderr and len(q.stdout.splitlines())==n,'control '+p.name+' '+q.stderr);observations[p.name]=q.stdout
 for p in (R/'compact44-inverse-lookup-prototype/object-controls.py',R/'compact44-marked-word-prototype/schema-controls.py'):
  q=subprocess.run([sys.executable,'-I','-S','-B',str(p)],capture_output=True,text=True,timeout=120);need(q.returncode==0 and not q.stderr,'author control '+p.name);observations[p.name]=json.loads(q.stdout)['status']
 print(json.dumps({'status':'PASS_INVERSE_NOEXTRA_CORRECTED_PRELAUNCH_AUDIT','correction_commit':'a2791584e3','driver_sha256':{name:h for name,_,h in FILES},'actual_pins_pass':True,'earlier_unchanged_parent_preflight_sessions':{'shared_matching':66189,'matching_and_forbidden':85491},'parent_preflight_functions_ast_unchanged':True,'fake_controls':observations,'scope':'No Lean. Inverse bounded below 943 with row 1 excluded; model exclusion assumes supplied bounded matching neighbor or cyclic matching. No construction, reverse word, graph calibration or iPRA endpoint. Stable HEAD, clean loader, provider/dynamic and sampled resource boundaries inherited.'},indent=2))
if __name__=='__main__':main()
