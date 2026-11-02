#!/usr/bin/env python3
"""Read-only artifact audit of generic bounded model permutation lookup."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/ordinary12-ipra-bridge/compact44-permutation-lookup-prototype'
OUT=Path('/tmp/ipra-compact-permutation-lookup-pair-01');PARENT=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');AUDIT=BASE/'reviews/thirteen-model-endpoint-successor-pair-independent-audit'
R='2efe441ae1d03f9d97fc5ab5e6a4846f26cd1c33706500eab5069ee14be1ab8d';SOURCE='73ff5a57db869957650ca6aca79442df86c03f18ed6495553be822e5e2ebaf45';OBJECT='cae55b0b18ac4ec9cfddebf5b0863064e4edb8662d7aaafa9c35c842b2057590';LOG='9a04dde718f1926528ea7876a5ff3596040a9352bf42a2c36fffd28f1e812fd1'
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 prefix=PKG.relative_to(ROOT).as_posix()+'/'
 names=subprocess.run(['git','ls-tree','-r','--name-only','f914244f1f','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
 need(len([x for x in names if '/logs/' in x and x.endswith('.log')])==2,'tracked logs')
 for name in names:
  blob=subprocess.run(['git','show','f914244f1f:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(blob).hexdigest()==sha(ROOT/name),'committed drift '+name)
 need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==R,'receipt')
 terminal=json.loads((PKG/'terminal-observation.json').read_bytes());need(terminal['session']==56475 and terminal['actual_exit_code']==0 and terminal['compiler_children']==2 and terminal['receipt_sha256']==R,'outer observation')
 rec=json.loads((PKG/'replay-receipt.json').read_bytes());need(rec['status']=='PASS_PAIRED_COMPACT_PERMUTATION_LOOKUP' and len(rec['rows'])==2,'status')
 for p,h in rec['fixed_inputs_sha256'].items():need(sha(p)==h,'input '+p)
 q=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,timeout=900)
 need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((AUDIT/'CHECK.json').read_bytes())==rec['parent_audit'],'parent audit')
 guards=rec['direct_guards'];need(len(guards)==30,'guard count');expected_guard_paths=set()
 for k,v in guards.items():
  p=Path(k)
  if v is None:need(not os.path.lexists(p),'unexpected companion '+k)
  else:need(p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],'companion '+k)
 out=[]
 for row,side in zip(rec['rows'],('author','peer')):
  lib=OUT/side/'lib';base=PARENT/side/'lib';original={p.relative_to(base) for p in base.rglob('*.olean')};actual={p.relative_to(lib) for p in lib.rglob('*.olean')};rel=Path('DiophantineConsistency/CompactPermutationInterface.olean')
  need(rel not in original and actual==original|{rel},'provider overlay')
  for x in original:need((lib/x).resolve()==(base/x).resolve() and sha(lib/x)==sha(base/x),'provider '+str(x))
  src=OUT/'src/DiophantineConsistency/CompactPermutationInterface.lean';obj=lib/rel;log=OUT/side/'CompactPermutationInterface.log';copy=PKG/'logs'/side/'CompactPermutationInterface.log'
  need(row['side']==side and row['module']=='CompactPermutationInterface' and row['exit']==row['deps_exit']==0 and row['stop_reason'] is None,'child exits')
  need(sha(src)==sha(PKG/'CompactPermutationInterface.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT and sha(log)==sha(copy)==row['log_sha256']==LOG,'artifacts')
  cmd=row['command'];need(cmd[1:4]==['-M4000','-j1','-DElab.async=false'] and cmd[-3]==str(src) and cmd[-1]==str(obj),'command')
  deps={str(PACKAGE/'Init.olean'),str(lib/'DiophantineConsistency/ArithmeticWangTable.olean')}
  need(set(row['deps_stdout'].splitlines())==deps and all(Path(x).is_file() for x in deps),'imports')
  for dep in deps:
   for suffix in SUFFIXES:expected_guard_paths.add(dep[:-6]+suffix)
  text=log.read_text();reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
  wanted=['CompactPermutationInterface.'+x for x in ('model_lookup_injective','model_lookup_surjective','lookup_preserved','range_lookup')]
  need([n for n,_ in reports]==wanted and [[n,a] for n,a in reports]==row['axiom_reports'],'report names')
  need(all({x.strip() for x in a.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,a in reports),'axiom sets')
  need(not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text),'log warning/error')
  out.append({'side':side,'source_sha256':SOURCE,'object_sha256':OBJECT,'log_sha256':LOG,'recorded_compiler_exit':0,'recorded_deps_exit':0})
 need(set(guards)==expected_guard_paths,'complete direct guards')
 print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT44_PERMUTATION_LOOKUP_AUDIT','evidence_commit':'f914244f1f','receipt_sha256':R,'recorded_outer_session':56475,'recorded_outer_exit':0,'parent_audit_rerun_exit':q.returncode,'direct_companion_guards':30,'runs':out,'scope':'Generic standard finite list permutation yields bounded model lookup injectivity/surjectivity; no compact array instantiation, omitted-index handling, adjacency, graph or iPRA endpoint; inherited provider/resource limitations.'},indent=2))
if __name__=='__main__':main()
