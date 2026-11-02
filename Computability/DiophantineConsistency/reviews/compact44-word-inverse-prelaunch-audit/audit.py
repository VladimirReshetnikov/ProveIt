#!/usr/bin/env python3
"""Independent exact-byte paired prelaunch review of matching-based clients."""
import hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';R=BASE/'research/ordinary12-ipra-bridge';HERE=Path(__file__).resolve().parent;PARENT=BASE/'reviews/compact44-row-match-independent-audit'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 records=[('compact44-marked-word-prototype','d6140fa686cdd42cdc4dc58d07c703fc39f7e4b9d1d704a71e2bc47f4d7e9d72','compact44-row-transport-prototype/CompactMarkedTransport.lean',['CompactMarkedTransport.forward_marked_word']),('compact44-inverse-lookup-prototype','da407f81bdf03d2cf7b76c199b4dd007e9b288f0706da27b6048527e4ba32cd0','compact44-inverse-lookup-prototype/CompactInverseInventory.lean',['CompactInverseDraft.inverse_forward','CompactInverseDraft.inverse_image','CompactInverseDraft.inverseLookup_defined'])]
 for name,d,source,names in records:
  driver=R/name/'replay.py';need(H(driver)==d,'driver '+name)
  for p in (driver,R/source):
   n=p.relative_to(ROOT).as_posix();b=subprocess.run(['git','show','6c0618cf46:'+n],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(b).hexdigest()==H(p),'committed bytes '+n)
  sp=importlib.util.spec_from_file_location('driver_'+name.replace('-','_'),driver);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);need(m.NAMES==names and len(m.PINS)==7,'reports/pins');m.pins()
  for p,h in m.PINS.items():need(H(p)==h,'pin '+str(p))
  source_text=(R/source).read_text()
  for n in names:need('#print axioms '+n in source_text,'source report '+n)
 schema=R/'compact44-marked-word-prototype/schema-controls.py';name=schema.relative_to(ROOT).as_posix();b=subprocess.run(['git','show','6c0618cf46:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(b).hexdigest()==H(schema),'schema control pin')
 for path,expected in [(schema,2),(HERE/'word-inverse-fake-review.py',20),(HERE/'word-inverse-guard-review.py',2)]:
  q=subprocess.run([sys.executable,'-I','-S','-B',str(path)],capture_output=True,text=True,timeout=120);need(q.returncode==0 and not q.stderr,'control '+str(path));
  if path==schema:need(all(x['negative_controls']==12 for x in json.loads(q.stdout)['results']) and len(json.loads(q.stdout)['results'])==expected,'schema controls')
  else:need(len(q.stdout.splitlines())==expected,'control output '+str(path))
 need(H(PARENT/'CHECK.json')=='db7690d62441f036f8275f5270416b015c8e0b2cc858de8b48ea19a703755df7','parent receipt')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=1200);need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((PARENT/'CHECK.json').read_bytes()),'parent audit')
 print(json.dumps({'status':'PASS_MATCHING_WORD_INVERSE_PRELAUNCH_REVIEW','correction_commit':'6c0618cf46','drivers':{x[0]:x[1] for x in records},'actual_parent_audit_rerun_exit':q.returncode,'schema_negative_controls_per_driver':12,'fake_modes_per_driver':10,'scope':'No Lean; forward transport assumes an existing cyclic marked word; inverse lookup requires bounded indices and explicit exclusion of row 1. No reverse word transport, actual extra-row exclusion, graph calibration, checker, machine, or iPRA endpoint. Parent provider, initial-loader, stable-HEAD, sampled-resource and unmonitored-dependency limits inherited.'},indent=2))
if __name__=='__main__':main()
