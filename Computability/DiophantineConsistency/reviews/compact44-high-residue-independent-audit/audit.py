#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/ordinary12-ipra-bridge/compact44-high-residue-prototype';OUT=Path('/tmp/ipra-compact-high-residue-pair-01');PARENT=Path('/tmp/ipra-compact-high-population-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');AUDIT=BASE/'reviews/compact44-high-population-independent-audit';PRE=BASE/'reviews/compact44-high-residue-prelaunch-audit';R='cbbfe108837e5003e8b283d6e8c165be546601ef1bdb2d34a0357e395bca042c'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
def main():
 prefix=PKG.relative_to(ROOT).as_posix()+'/'
 names=subprocess.run(['git','ls-tree','-r','--name-only','b69e068c6c','--',prefix],cwd=ROOT,check=True,stdout=subprocess.PIPE,text=True).stdout.splitlines();need(len(names)==9,'packet inventory')
 for n in names:
  b=subprocess.run(['git','show','b69e068c6c:'+n],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(b).hexdigest()==sha(ROOT/n),'packet '+n)
 need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==R,'receipt')
 t=(PKG/'evidence/terminal.txt').read_text();need('session 65209:' in t and 'PASS_PAIRED_COMPACT_HIGH_RESIDUE '+R in t and t.endswith('outer exit 0\n'),'terminal')
 rec=json.loads((OUT/'receipt.json').read_bytes());need(rec['status']=='PASS_PAIRED_COMPACT_HIGH_RESIDUE' and len(rec['runs'])==2,'status')
 need(sha(PKG/'replay.py')==rec['driver_sha256']=='20a5eadfcc0f098111ebcaa323213eb541ec8a87ed087d237d26f62605ccb764','driver')
 need(sha(PRE/'CHECK.json')=='f7192b5fcdd7ccc9abaf16f1aa9771c56b4fc1ddb687dbdb99744f024418024d','prelaunch')
 for p,h in rec['fixed_inputs_sha256'].items():need(sha(p)==h,'fixed input '+p)
 need(sha(AUDIT/'CHECK.json')=='074d5c92e0394a5b67c337e3cb89694e43a8ec47778b0b38ad814b3b7f7c281c' and rec['parent_audit']==json.loads((AUDIT/'CHECK.json').read_bytes()),'parent receipt')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,timeout=1200);need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==rec['parent_audit'],'parent audit rerun')
 logs="'CompactHighResidue.natural_mod_eight' depends on axioms: [propext]\n'CompactHighResidue.model_mod_eight' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
 results=[]
 for row,side in zip(rec['runs'],('author','peer')):
  need(row['label']==side and row['compiler_exit']==row['deps_exit']==0,'child exits')
  run=OUT/side;src=run/'src/CompactHighResidue.lean';obj=run/'CompactHighResidue.olean';log=run/'compiler.log';lib=run/'lib';base=PARENT/side/'lib';extra=Path('DiophantineConsistency/CompactHighPopulation.olean')
  need(sha(src)==sha(PKG/'CompactHighResidue.lean')==row['source_sha256']=='2e4da7f6de540be280f37214ee0f9ab8272636afff515c2a5ee6992851b6565a' and sha(obj)==row['object_sha256'],'source/object')
  need(log.read_text()==logs==row['stdout'] and sha(log)==sha(PKG/'evidence'/f'{side}.log')==row['log_sha256'],'exact log')
  originals={p.relative_to(base) for p in base.rglob('*.olean')};actual={p.relative_to(lib) for p in lib.rglob('*.olean')};need(extra not in originals and actual==originals|{extra},'overlay inventory')
  for rel in originals:need((lib/rel).resolve()==(base/rel).resolve() and sha(lib/rel)==sha(base/rel),'overlay '+str(rel))
  need(sha(lib/extra)==sha(PARENT/side/'CompactHighPopulation.olean')==row['seed_sha256'],'seed')
  deps={str(PACKAGE/'Init.olean'),str(lib/extra)};need(set(row['deps_stdout'].splitlines())==deps and all(Path(p).is_file() for p in deps),'direct deps')
  cmd=row['command'];need(cmd[1:4]==['-M3000','-j1','-DElab.async=false'] and cmd[-3]==str(src) and cmd[-1]==str(obj),'command')
  results.append({'side':side,'baseline_objects':len(originals),'source_sha256':row['source_sha256'],'object_sha256':row['object_sha256'],'seed_sha256':row['seed_sha256'],'log_sha256':row['log_sha256'],'recorded_compiler_exit':0,'recorded_deps_exit':0})
 need(results[0]['object_sha256']==results[1]['object_sha256'] and results[0]['log_sha256']==results[1]['log_sha256'],'paired outputs')
 print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT44_HIGH_RESIDUE_AUDIT','evidence_commit':'b69e068c6c','receipt_sha256':R,'recorded_outer_session':65209,'recorded_outer_exit':0,'reported_launch_head':'13c8dfab929d4a958de528f1711326ad8d1e64c7','parent_audit_rerun_exit':q.returncode,'runs':results,'scope':'Natural symbolic digit-list residue and IΣ₁-model cast only; no retained high-port equality, machine semantics or iPRA endpoint; inherited provider, axiom-inventory and dynamic-dependency limits.'},indent=2))
if __name__=='__main__':main()
