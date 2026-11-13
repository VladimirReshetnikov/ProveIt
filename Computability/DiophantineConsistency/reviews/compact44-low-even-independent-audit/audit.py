#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/ordinary12-ipra-bridge/compact44-low-even-prototype';OUT=Path('/tmp/ipra-compact-low-even-pair-01');PARENT=Path('/tmp/ipra-freej-concrete-digits-client-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');AUDIT=BASE/'reviews/ordinary12-freej-concrete-digits-client-independent-audit';PRE=BASE/'reviews/compact44-low-even-prelaunch-audit';R='543bc934c905cce75d76f964b63e988e5ad915748c1b06abfaec27967de0b468'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
def main():
 prefix=PKG.relative_to(ROOT).as_posix()+'/'
 names=subprocess.run(['git','ls-tree','-r','--name-only','406ceaeece','--',prefix],cwd=ROOT,check=True,stdout=subprocess.PIPE,text=True).stdout.splitlines()
 for n in names:
  b=subprocess.run(['git','show','406ceaeece:'+n],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(b).hexdigest()==sha(ROOT/n),'packet '+n)
 need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==R,'receipt')
 t=(PKG/'evidence/terminal.txt').read_text();need('session 99179 exit 0' in t and 'f748c85a02b5a822acdf162dc79624b1bbc75c5d' in t and t.rstrip().endswith('PASS_PAIRED_COMPACT_LOW_EVEN '+R),'terminal')
 rec=json.loads((OUT/'receipt.json').read_bytes());need(rec['status']=='PASS_PAIRED_COMPACT_LOW_EVEN' and len(rec['runs'])==2,'status')
 need(sha(PKG/'replay.py')==rec['driver_sha256']=='12f9f6d08e5c94f461f0d12770789594f4844f82a0b23c808340e896e2f14890','driver')
 for p,h in rec['fixed_inputs_sha256'].items():need(sha(p)==h,'fixed input '+p)
 need(sha(PRE/'CHECK.json')=='3c6558773b3e4e11fdb0147e54b11bf56979f3e6d8677c6778beb23a9e4430ea','prelaunch receipt')
 a=subprocess.run([sys.executable,'-I','-S','-B',str(PRE/'audit.py')],capture_output=True,timeout=120);need(a.returncode==0 and not a.stderr and json.loads(a.stdout)==json.loads((PRE/'CHECK.json').read_bytes()),'restored prelaunch audit')
 need(sha(AUDIT/'CHECK.json')=='5ef4ae700c1105220472fe57952929071a6c5666d1cad01a3b37c971c49d3056' and rec['parent_audit']==json.loads((AUDIT/'CHECK.json').read_bytes()),'parent receipt')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,timeout=1200);need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==rec['parent_audit'],'parent audit rerun')
 expected="'CompactLowEven.low_even' depends on axioms: [propext, Classical.choice, Quot.sound]\n";results=[]
 for row,side in zip(rec['runs'],('author','peer')):
  need(row['label']==side and row['compiler_exit']==row['deps_exit']==0,'child exits')
  run=OUT/side;src=run/'src/CompactLowEven.lean';obj=run/'CompactLowEven.olean';log=run/'compiler.log';lib=run/'lib';base=PARENT/side/'lib';seed=Path('DiophantineConsistency/CompactConcreteIncrement.olean')
  need(sha(src)==sha(PKG/'CompactLowEven.lean')==row['source_sha256']=='ae40037d5611824ad3a8b39c3b378b18e61fff82852af0dbc11eeb8960641499' and sha(obj)==row['object_sha256'],'source/object')
  need(log.read_text()==expected==row['stdout'] and sha(log)==sha(PKG/'evidence'/f'{side}.log')==row['log_sha256'],'exact log')
  originals={p.relative_to(base) for p in base.rglob('*.olean')};actual={p.relative_to(lib) for p in lib.rglob('*.olean')};need(actual==originals and len(originals)==127,'overlay inventory')
  for rel in originals:need((lib/rel).resolve()==(base/rel).resolve() and sha(lib/rel)==sha(base/rel),'overlay '+str(rel))
  need(sha(lib/seed)==sha(base/seed)==row['seed_sha256'],'seed')
  deps={str(PACKAGE/'Init.olean'),str(lib/seed)};need(set(row['deps_stdout'].splitlines())==deps and all(Path(p).is_file() for p in deps),'direct deps')
  cmd=row['command'];need(cmd[1:4]==['-M3000','-j1','-DElab.async=false'] and cmd[-3]==str(src) and cmd[-1]==str(obj),'command')
  results.append({'side':side,'baseline_objects':len(originals),'source_sha256':row['source_sha256'],'object_sha256':row['object_sha256'],'seed_sha256':row['seed_sha256'],'log_sha256':row['log_sha256'],'recorded_compiler_exit':0,'recorded_deps_exit':0})
 need(results[0]['object_sha256']==results[1]['object_sha256'] and results[0]['log_sha256']==results[1]['log_sha256'],'paired outputs')
 print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT44_LOW_EVEN_AUDIT','evidence_commit':'36d4d37635','readme_restoration_commit':'406ceaeece','receipt_sha256':R,'recorded_outer_session':99179,'recorded_outer_exit':0,'reported_launch_head':'f748c85a02b5a822acdf162dc79624b1bbc75c5d','prelaunch_audit_rerun_exit':a.returncode,'parent_audit_rerun_exit':q.returncode,'runs':results,'scope':'IΣ₁ symbolic low-mask parity only; no retained MC or graph-port equality, checker, machine or iPRA endpoint. Historical parent audit draft drift and provider/axiom-inventory/resource boundaries inherited.'},indent=2))
if __name__=='__main__':main()
