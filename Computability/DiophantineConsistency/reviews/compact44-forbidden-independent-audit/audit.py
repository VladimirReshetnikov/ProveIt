#!/usr/bin/env python3
"""Independent finite forbidden-row and paired artifact audit."""
import hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/compact44-forbidden-prototype'
SOURCE=BASE/'research/ordinary12-ipra-bridge/compact44-color-relabel/CompactForbidden.lean'
TABLE=BASE/'con-zfc-diophantine-forms/36-small-tuple/coefficients/wang943_tiles.json'
PARENT=BASE/'reviews/compact44-943-table-independent-audit'
OUT=Path('/tmp/ipra-compact-forbidden-pair-01')
WINDOW=Path('/tmp/ipra-thirteen-parent-window-pair-01')
TILERUN=Path('/tmp/ipra-compact943-table-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='8f1eadf2756320921733d832fa7f467fcfd916acd424f45ca2f63a0c3d0d1de2'
SOURCE_SHA='27786b8ec2cf08ccd81f3cdb8f0585adf76fbfacc8e993be310d4697ac01e020'
OBJECT='deee2cb5b898f6327e4e9c5a45f932d06409ae13c359f6a1def952a89834019d'
SEED='092cf01d0bf249e88f75c78a31eb69f15040dfe985f1e990b19b8d296b9bd9d4'
LOG='6f9f2ebac16434b7de58a49aa4db43381234a0739d807e4feb88775df712d8bd'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 prefix=PKG.relative_to(ROOT).as_posix()+'/'
 names=subprocess.run(['git','ls-tree','-r','--name-only','24f401be94','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
 need(len(names)>=5,'packet inventory')
 for name in names:
  data=subprocess.run(['git','show','24f401be94:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(data).hexdigest()==sha(ROOT/name),'packet drift '+name)
 source_name=SOURCE.relative_to(ROOT).as_posix()
 data=subprocess.run(['git','show','7c56dfbb7c:'+source_name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
 need(hashlib.sha256(data).hexdigest()==sha(SOURCE)==SOURCE_SHA,'source commit')
 need(sha(TABLE)=='66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f','ordered JSON')
 rows=json.loads(TABLE.read_bytes())
 need(len(rows)==943 and all(len(row)==4 for row in rows),'rows')
 need([i for i,row in enumerate(rows) if row[2]==5]==[],'east five')
 need([i for i,row in enumerate(rows) if row[0]==5]==[1] and rows[1]==[5,0,0,0],'west five')
 need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
 terminal=(PKG/'evidence/terminal.txt').read_text()
 need(terminal.startswith('Actual outer wrapper session 24468 exited 0.') and terminal.rstrip().endswith('PASS_PAIRED_COMPACT_FORBIDDEN_TILE '+RECEIPT),'outer observation')
 r=json.loads((PKG/'evidence/receipt.json').read_bytes())
 need(r['status']=='PASS_PAIRED_COMPACT_FORBIDDEN_TILE' and len(r['runs'])==2,'receipt status')
 for p,h in r['fixed_inputs_sha256'].items():need(sha(p)==h,'fixed input '+p)
 need(sha(PKG/'replay.py')==r['driver_sha256'],'driver')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=900)
 need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((PARENT/'CHECK.json').read_bytes())==r['parent_audit'],'parent audit')
 expected="""'CompactForbidden.no_east_five_all' does not depend on any axioms
'CompactForbidden.west_five_extra_all' does not depend on any axioms
'CompactForbidden.no_east_five' depends on axioms: [propext, Quot.sound]
'CompactForbidden.west_five_extra' depends on axioms: [propext, Quot.sound]
'CompactForbidden.five_cannot_have_left' depends on axioms: [propext, Quot.sound]
"""
 results=[]
 for row,side in zip(r['runs'],('author','peer')):
  run=OUT/side;src=Path(row['command'][-3]);obj=run/'CompactForbidden.olean';log=run/'compiler.log'
  need(row['label']==side and row['compiler_exit']==row['deps_exit']==0,'child exits')
  need(sha(src)==sha(SOURCE)==row['source_sha256']==SOURCE_SHA,'source')
  need(sha(obj)==row['object_sha256']==OBJECT,'object')
  need(sha(log)==sha(PKG/'evidence'/(side+'.log'))==row['log_sha256']==LOG and log.read_text()==row['stdout']==expected,'exact axiom output')
  need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'compiler command')
  lib=run/'lib';win=WINDOW/side/'lib';seed=lib/'DiophantineConsistency/Compact943Data.olean'
  wf={p.relative_to(win) for p in win.rglob('*.olean')};lf={p.relative_to(lib) for p in lib.rglob('*.olean')}
  need(lf==wf|{Path('DiophantineConsistency/Compact943Data.olean')},'overlay inventory')
  for rel in wf:need((lib/rel).resolve()==(win/rel).resolve() and sha(lib/rel)==sha(win/rel),'overlay '+str(rel))
  need(sha(seed)==sha(TILERUN/side/'Compact943Data.olean')==row['seed_sha256']==SEED,'seed')
  deps={str(PACKAGE/'Init.olean'),str(seed)}
  need(set(row['deps_stdout'].splitlines())==deps and all(Path(x).is_file() for x in deps),'direct imports')
  results.append({'side':side,'source_sha256':SOURCE_SHA,'object_sha256':OBJECT,'seed_sha256':SEED,'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
 print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT44_FORBIDDEN_AUDIT','source_commit':'7c56dfbb7c','pair_commit':'24f401be94','receipt_sha256':RECEIPT,'recorded_outer_session':24468,'recorded_outer_exit':0,'parent_audit_rerun_exit':q.returncode,'json_rows_checked':len(rows),'east_five_indices':[],'west_five_indices':[1],'runs':results,'scope':'Finite Lean table exclusion conditional on a matching left row; external JSON binding, no arbitrary-model neighbor/boundary, simulation, graph or iPRA claim; inherited provider/resource limitations.'},indent=2))
if __name__=='__main__':main()
