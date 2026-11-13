#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/ordinary12-ipra-bridge/compact44-marked-word-prototype';SRC=BASE/'research/ordinary12-ipra-bridge/compact44-row-transport-prototype/CompactMarkedTransport.lean';OUT=Path('/tmp/ipra-compact-marked-word-pair-01');PARENT=Path('/tmp/ipra-compact-row-transport-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');AUDIT=BASE/'reviews/compact44-row-match-independent-audit';PRE=BASE/'reviews/compact44-word-inverse-prelaunch-audit';R='ee0d82821fe4cfaa3b479105df0d6d0e1dcc4f6dc7143c59623f92c05b88fa65'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
def main():
 for f in ['PAIR-RESULT.md','logs/author/CompactMarkedTransport.log','logs/peer/CompactMarkedTransport.log','replay-receipt.json','terminal-observation.json']:
  p=PKG/f;n=p.relative_to(ROOT).as_posix();b=subprocess.run(['git','show','09e609871f:'+n],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(b).hexdigest()==sha(p),'committed bytes '+n)
 need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==R,'receipt hash')
 term=json.loads((PKG/'terminal-observation.json').read_text());need(term=={'session_id':85225,'observed_exit':0,'status':'PASS_COMPACT_MARKED_WORD_PAIR','receipt_sha256':R,'protected_head':'0819ac850a8482b3c1aef24d69edcd9d8e9a596b'},'terminal')
 rec=json.loads((OUT/'receipt.json').read_bytes());need(rec['status']==term['status'] and len(rec['rows'])==2,'receipt')
 need(sha(PKG/'replay.py')==rec['driver_sha256']=='d6140fa686cdd42cdc4dc58d07c703fc39f7e4b9d1d704a71e2bc47f4d7e9d72','driver')
 need(sha(SRC)==sha(OUT/'src/DiophantineConsistency/CompactMarkedTransport.lean')==rec['source_sha256']=='3c520db71225576edeb51f4855d42f644fb7479d4e9df634e6735b6185670fb6','frozen source')
 need(sha(PRE/'CHECK.json')=='29f725b04800f29516f66a0ede8e8a1f10dd45cb242bf3c4255b9f1200a81568','prelaunch audit')
 need(sha(AUDIT/'CHECK.json')=='db7690d62441f036f8275f5270416b015c8e0b2cc858de8b48ea19a703755df7','parent audit pin')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,timeout=1200);need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((AUDIT/'CHECK.json').read_bytes()),'parent audit rerun')
 need(rec['parent_audit_before']==rec['parent_audit_after']==json.loads(q.stdout)['status'],'parent statuses')
 for name,v in rec['direct_guards'].items():
  p=Path(name)
  if v is None:need(not p.exists() and not p.is_symlink(),'absent optional companion '+name)
  else:need(p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],'guard '+name)
 need(len(rec['direct_guards'])==50,'guard count');results=[]
 for row,side in zip(rec['rows'],('author','peer')):
  need(row['side']==side and row['exit']==row['deps_exit']==0 and row['stop_reason'] is None,'exits')
  lib=OUT/side/'lib';base=PARENT/side/'lib';orig={p.relative_to(base) for p in base.rglob('*.olean')};actual={p.relative_to(lib) for p in lib.rglob('*.olean')};extra=Path('DiophantineConsistency/CompactMarkedTransport.olean')
  need(extra not in orig and actual==orig|{extra},'overlay inventory')
  for rel in orig:need((lib/rel).resolve()==(base/rel).resolve() and sha(lib/rel)==sha(base/rel),'overlay '+str(rel))
  obj=lib/extra;log=OUT/side/'CompactMarkedTransport.log';need(obj.is_file() and not obj.is_symlink() and sha(obj)==row['object_sha256'] and sha(log)==sha(PKG/'logs'/side/log.name)==row['log_sha256'],'outputs')
  deps={str(PACKAGE/'Init.olean'),str(lib/'DiophantineConsistency/CompactRowComplete.olean'),str(lib/'DiophantineConsistency/ArithmeticWangPlane.olean')};need(set(row['deps_stdout'].splitlines())==deps,'direct dependency paths')
  for dep in deps:
   p=Path(dep);g=rec['direct_guards'].get(dep);need(p.is_file() and g is not None and sha(p)==g['sha256'] and str(p.resolve())==g['realpath'],'required direct object absent or drifted '+dep)
  out=log.read_text();reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",out,re.M);need(reports==[('CompactMarkedTransport.forward_marked_word','propext, Classical.choice, Quot.sound')] and [[n,x] for n,x in reports]==row['axiom_reports'],'named axiom report')
  need(not re.search(r'warning:|error:|\bsorryAx\b|\bsorry\b',out),'warnings')
  cmd=row['command'];need(cmd[1:4]==['-M4000','-j1','-DElab.async=false'] and cmd[-3]==str(OUT/'src/DiophantineConsistency/CompactMarkedTransport.lean') and cmd[-1]==str(obj),'command')
  results.append({'side':side,'baseline_objects':len(orig),'required_direct_objects_verified':3,'source_sha256':row['source_sha256'],'object_sha256':row['object_sha256'],'log_sha256':row['log_sha256'],'reported_compiler_exit':0,'reported_deps_exit':0})
 need(results[0]['object_sha256']==results[1]['object_sha256'] and results[0]['log_sha256']==results[1]['log_sha256'],'paired outputs')
 print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT_FORWARD_WORD_AUDIT','evidence_commit':'09e609871f','receipt_sha256':R,'recorded_outer_session':85225,'recorded_outer_exit':0,'recorded_protected_head':term['protected_head'],'parent_audit_rerun_exit':q.returncode,'direct_companion_guards':len(rec['direct_guards']),'runs':results,'scope':'Forward transport assumes existing positive cyclic marked word. No existence, reverse transport, calibration, checker, machine or iPRA endpoint. Every actual required direct object is verified at audit time; the driver did not independently reject a simulated missing required object. Historical provider, dynamic ancestry and resource bounds inherited.'},indent=2))
if __name__=='__main__':main()
