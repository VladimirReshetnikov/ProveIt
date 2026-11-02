#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]; BASE=ROOT/'Computability/DiophantineConsistency'; PKG=BASE/'research/ordinary12-ipra-bridge/compact44-row-transport-prototype';OUT=Path('/tmp/ipra-compact-row-transport-pair-01');PARENT=Path('/tmp/ipra-compact-table-lookup-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');AUDIT=BASE/'reviews/compact44-table-lookup-independent-audit';PRE=BASE/'reviews/compact44-row-transport-prelaunch-audit';R='a10ab9ecc787aa4ba3ff0f88a38b12eb68bbd2722a693e490b61ac14f762cdc9'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 for f in ['PAIR-RESULT.md','logs/author/CompactRowComplete.log','logs/peer/CompactRowComplete.log','replay-receipt.json','terminal-observation.json']:
  p=PKG/f;n=p.relative_to(ROOT).as_posix();b=subprocess.run(['git','show','6a6075972d:'+n],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(b).hexdigest()==sha(p),'committed bytes '+n)
 need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==R,'receipt hash')
 term=json.loads((PKG/'terminal-observation.json').read_text());need(term=={'session_id':35384,'observed_exit':0,'status':'PASS_COMPACT_ROW_TRANSPORT_PAIR','receipt_sha256':R,'protected_head':'c2d95685fc4908af36290467ebae564cc5c1005b'},'terminal')
 rec=json.loads((OUT/'receipt.json').read_bytes());need(rec['status']==term['status'] and len(rec['rows'])==2,'receipt')
 need(sha(PKG/'replay.py')==rec['driver_sha256']=='4030748893a24268b76ee70fb97164d9b9649b796acbad1a557e73a0b9feb80a','driver')
 need(sha(PKG/'CompactRowComplete.lean')==sha(OUT/'src/DiophantineConsistency/CompactRowComplete.lean')==rec['source_sha256']=='317431dd423feb4019d02c9f1164288f10506ea38cb544c8a339aa1d72d04984','frozen source')
 need(sha(PRE/'CHECK.json')=='e504b9afc359bff291262f9487829b91e3de3c63f252d6138bc734cc15d5fa9f','prelaunch audit')
 need(sha(AUDIT/'CHECK.json')=='4a08735a0496f7a975f8014f7f3ec3e9d6689f0eee110ba596610968dc27aece','parent audit pin')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,timeout=1200);need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((AUDIT/'CHECK.json').read_bytes()),'parent audit rerun')
 need(rec['parent_audit_before']==rec['parent_audit_after']==json.loads(q.stdout)['status'],'parent statuses')
 for name,v in rec['direct_guards'].items():
  p=Path(name)
  if v is None:need(not p.exists() and not p.is_symlink(),'absent companion '+name)
  else:need(p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],'guard '+name)
 need(len(rec['direct_guards'])==50,'guard count')
 names=re.findall(r'^#print axioms\s+([^\s]+)',(PKG/'CompactRowComplete.lean').read_text(),re.M);need(len(names)==12,'source report names')
 result=[]
 for row,side in zip(rec['rows'],('author','peer')):
  need(row['side']==side and row['exit']==row['deps_exit']==0 and row['stop_reason'] is None,'exits')
  lib=OUT/side/'lib';base=PARENT/side/'lib';orig={p.relative_to(base) for p in base.rglob('*.olean')};actual={p.relative_to(lib) for p in lib.rglob('*.olean')};extra=Path('DiophantineConsistency/CompactRowComplete.olean')
  need(extra not in orig and actual==orig|{extra},'overlay inventory')
  for rel in orig:need((lib/rel).resolve()==(base/rel).resolve() and sha(lib/rel)==sha(base/rel),'overlay '+str(rel))
  obj=lib/extra;log=OUT/side/'CompactRowComplete.log';need(obj.is_file() and not obj.is_symlink() and sha(obj)==row['object_sha256'] and sha(log)==sha(PKG/'logs'/side/log.name)==row['log_sha256'],'outputs')
  deps={str(PACKAGE/'Init.olean'),str(lib/'DiophantineConsistency/CompactTableLookup.olean'),str(lib/'DiophantineConsistency/MFWangTiles942Core.olean')};need(set(row['deps_stdout'].splitlines())==deps and all(Path(p).is_file() for p in deps),'dependency paths')
  out=log.read_text();reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",out,re.M)
  need([n for n,_ in reports]==names and [[n,x] for n,x in reports]==row['axiom_reports'] and all({x.strip() for x in v.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,v in reports),'report names/axioms')
  need(not re.search(r'warning:|error:|\bsorryAx\b|\bsorry\b',out),'warnings')
  cmd=row['command'];need(cmd[1:4]==['-M4000','-j1','-DElab.async=false'] and cmd[-3]==str(OUT/'src/DiophantineConsistency/CompactRowComplete.lean') and cmd[-1]==str(obj),'command')
  result.append({'side':side,'baseline_objects':len(orig),'source_sha256':row['source_sha256'],'object_sha256':row['object_sha256'],'log_sha256':row['log_sha256'],'reported_compiler_exit':row['exit'],'reported_deps_exit':row['deps_exit'],'axiom_reports':len(reports)})
 need(result[0]['object_sha256']==result[1]['object_sha256'] and result[0]['log_sha256']==result[1]['log_sha256'],'paired outputs')
 print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT_ROW_MATCH_AUDIT','evidence_commit':'6a6075972d','receipt_sha256':R,'recorded_outer_session':35384,'recorded_outer_exit':0,'recorded_protected_head':term['protected_head'],'parent_audit_rerun_exit':q.returncode,'direct_companion_guards':len(rec['direct_guards']),'runs':result,'scope':'IΣ₁ model local matching equivalences for pairs of indices below 942; no actual neighbors, wrap, tiling, machine, calibration or iPRA endpoint; external table binding and provider/axiom-inventory boundaries inherited.'},indent=2))
if __name__=='__main__':main()
