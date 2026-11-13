#!/usr/bin/env python3
"""Independent free-J ordinate index and paired artifact audit."""
import hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/free-j-main-index-unique-prototype'
SOURCE=PKG/'FreeJMainIndexUnique.lean'
TABLE=BASE/'con-zfc-diophantine-forms/36-small-tuple/coefficients/wang943_tiles.json'
PARENT=BASE/'reviews/ordinary12-freej-exact-ordinary-independent-audit'
OUT=Path('/tmp/ipra-freej-main-index-unique-pair-01')
WINDOW=Path('/tmp/ipra-freej-exact-ordinary-pair-01')
TILERUN=Path('/tmp/ipra-freej-exact-ordinary-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='b9a97d411fef45aab777788870c24db7945ac8945343e1351a0dc10c13d184c6'
SOURCE_SHA='bb930c6646519e57eb0ecd0c30669096ec0d61155e89f847edfa33cf62de4cc0'
OBJECT='697ff1f8e042959754e694a77326ad18145e50fdf573c5a3d74a2264c299f87c'
SEED='d30414abd21b28eb9a9c2d62caccc6945a3cb6d2b699d35ebc3d3ab4fe033a5e'
LOG='d8179a5f2f5e32fe382e1be26bc67c979914d45c411dab9f50413705bd4a07d1'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 prefix=PKG.relative_to(ROOT).as_posix()+'/'
 names=subprocess.run(['git','ls-tree','-r','--name-only','145e572eb1','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
 need(len(names)>=5,'packet inventory')
 for name in names:
  data=subprocess.run(['git','show','145e572eb1:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(data).hexdigest()==sha(ROOT/name),'packet drift '+name)
 source_name=SOURCE.relative_to(ROOT).as_posix()
 data=subprocess.run(['git','show','145e572eb1:'+source_name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
 need(hashlib.sha256(data).hexdigest()==sha(SOURCE)==SOURCE_SHA,'source commit')
 need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
 terminal=(PKG/'evidence/terminal.txt').read_text()
 need('session 55299' in terminal and terminal.endswith('outer exit 0\n') and 'PASS_PAIRED_FREEJ_MAIN_INDEX_UNIQUE '+RECEIPT in terminal,'outer observation')
 r=json.loads((PKG/'evidence/receipt.json').read_bytes())
 need(r['status']=='PASS_PAIRED_FREEJ_MAIN_INDEX_UNIQUE' and len(r['runs'])==2,'receipt status')
 for p,h in r['fixed_inputs_sha256'].items():need(sha(p)==h,'fixed input '+p)
 need(sha(PKG/'replay.py')==r['driver_sha256'],'driver')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=900)
 need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((PARENT/'CHECK.json').read_bytes())==r['parent_audit'],'parent audit')
 expected="""'FreeJMainIndexUnique.graph_ordinate_index_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
"""
 results=[]
 for row,side in zip(r['runs'],('author','peer')):
  run=OUT/side;src=Path(row['command'][-3]);obj=run/'FreeJMainIndexUnique.olean';log=run/'compiler.log'
  need(row['label']==side and row['compiler_exit']==row['deps_exit']==0,'child exits')
  need(sha(src)==sha(SOURCE)==row['source_sha256']==SOURCE_SHA,'source')
  need(sha(obj)==row['object_sha256']==OBJECT,'object')
  need(sha(log)==sha(PKG/'evidence'/(side+'.log'))==row['log_sha256']==LOG and log.read_text()==row['stdout']==expected,'exact axiom output')
  need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'compiler command')
  lib=run/'lib';win=WINDOW/side/'lib';seed=lib/'DiophantineConsistency/FreeJExactOrdinary.olean'
  wf={p.relative_to(win) for p in win.rglob('*.olean')};lf={p.relative_to(lib) for p in lib.rglob('*.olean')}
  need(lf==wf|{Path('DiophantineConsistency/FreeJExactOrdinary.olean')},'overlay inventory')
  for rel in wf:need((lib/rel).resolve()==(win/rel).resolve() and sha(lib/rel)==sha(win/rel),'overlay '+str(rel))
  need(sha(seed)==sha(TILERUN/side/'FreeJExactOrdinary.olean')==row['seed_sha256']==SEED,'seed')
  deps={str(PACKAGE/'Init.olean'),str(seed)}
  need(set(row['deps_stdout'].splitlines())==deps and all(Path(x).is_file() for x in deps),'direct imports')
  results.append({'side':side,'source_sha256':SOURCE_SHA,'object_sha256':OBJECT,'seed_sha256':SEED,'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
 print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_MAIN_INDEX_UNIQUE_AUDIT','source_commit':'145e572eb1','pair_commit':'145e572eb1','receipt_sha256':RECEIPT,'recorded_outer_session':55299,'recorded_outer_exit':0,'parent_audit_rerun_exit':q.returncode,'runs':results,'scope':'Conditional model-level universal main-ordinate index uniqueness; no compact44 port calibration, checker, machine simulation or iPRA proof; inherited provider/resource limitations.'},indent=2))
if __name__=='__main__':main()
