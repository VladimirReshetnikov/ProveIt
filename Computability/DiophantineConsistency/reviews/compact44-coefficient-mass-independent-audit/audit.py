#!/usr/bin/env python3
"""Independent finite coefficient-mass and paired artifact audit."""
import hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/compact44-coefficient-mass-prototype'
SOURCE=PKG/'CompactCoefficientMass.lean'
TABLE=BASE/'con-zfc-diophantine-forms/36-small-tuple/coefficients/wang943_tiles.json'
PARENT=BASE/'reviews/compact44-943-table-independent-audit'
OUT=Path('/tmp/ipra-compact-coefficient-mass-pair-01')
WINDOW=Path('/tmp/ipra-thirteen-parent-window-pair-01')
TILERUN=Path('/tmp/ipra-compact943-table-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='86c3ba38c4baabc6228ca95e90a9fba95b4dd749e6facb2a6f5f9aecfb6418e0'
SOURCE_SHA='ca20b0796cbdd1b6c86e6032998fec7d5577b0f775b88d8395db349c7b1b2e6e'
OBJECT='e3ac8b31bcc8605ea87030969c7eac84e5369c1be69e73805fcf3b8bfd1dfb4e'
SEED='092cf01d0bf249e88f75c78a31eb69f15040dfe985f1e990b19b8d296b9bd9d4'
LOG='68280ce606e3825f675d07b1f8cc1de098ec35e53d5e92232cd7dbcedf27090d'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 prefix=PKG.relative_to(ROOT).as_posix()+'/'
 names=subprocess.run(['git','ls-tree','-r','--name-only','49d10be3df','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
 need(len(names)>=5,'packet inventory')
 for name in names:
  data=subprocess.run(['git','show','49d10be3df:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(data).hexdigest()==sha(ROOT/name),'packet drift '+name)
 source_name=SOURCE.relative_to(ROOT).as_posix()
 data=subprocess.run(['git','show','49d10be3df:'+source_name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
 need(hashlib.sha256(data).hexdigest()==sha(SOURCE)==SOURCE_SHA,'source commit')
 need(sha(TABLE)=='66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f','ordered JSON')
 rows=json.loads(TABLE.read_bytes())
 need(len(rows)==943 and all(len(row)==4 for row in rows),'rows')
 vals=[w+2**8*n+2**17*e+2**25*t+127*2**34 for w,n,e,t in rows]
 need(all(0<v<2**41 for v in vals),'payload range')
 weights=[1+2**10*(2**41-v) for v in vals]
 copy=sum(2**(10+j) for j in range(41)); coefficient=sum(weights)+copy; stencil=2*coefficient+6
 need((sum(weights),copy,coefficient,stencil)==(12734826094758831,2251799813684224,14986625908443055,29973251816886116),'finite masses')
 need(3*stencil+1<2**66 and 3*stencil+1+2**66<2**67 and 3*stencil+(2**67-1)+1<=2*(2**67-1),'slack')
 recipe=BASE/'candidates/free-j-polarized-positive/source/positive/coefficients/recipe'
 builder=recipe/'build_coefficients.py';transitions=recipe/'k215_transitions.json'
 need(sha(builder)=='a003f26c5ef2dc1782e37be2a91abe25e59e5ff39f12bd142f2d6c1d4d8cf82b' and sha(transitions)=='880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755','recipe pins')
 sys.dont_write_bytecode=True
 spec=importlib.util.spec_from_file_location('pinned_recipe',builder);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
 data=module.recipe();need([list(x) for x in data['tiles']]==rows,'recipe table')
 need([data['ce'][i] for i in range(943)]==weights,'each selector coefficient')
 need(sorted(v for i,v in data['ce'].items() if i>=943)==[0,0]+[2**(10+j) for j in range(41)],'each copy/anchor/dummy')
 need(sum(data['ce'].values())==coefficient and sum(data['dc'].values())==2*coefficient+4 and sum(data['dc'].values())+2==stencil,'finite recipe stencil')
 need(sha(builder)=='a003f26c5ef2dc1782e37be2a91abe25e59e5ff39f12bd142f2d6c1d4d8cf82b' and sha(transitions)=='880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755','recipe post-check')
 need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
 terminal=(PKG/'evidence/terminal.txt').read_text()
 need('session 96941' in terminal and terminal.endswith('outer exit 0\n') and 'PASS_PAIRED_COMPACT_COEFFICIENT_MASS '+RECEIPT in terminal,'outer observation')
 r=json.loads((PKG/'evidence/receipt.json').read_bytes())
 need(r['status']=='PASS_PAIRED_COMPACT_COEFFICIENT_MASS' and len(r['runs'])==2,'receipt status')
 for p,h in r['fixed_inputs_sha256'].items():need(sha(p)==h,'fixed input '+p)
 need(sha(PKG/'replay.py')==r['driver_sha256'],'driver')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=900)
 need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((PARENT/'CHECK.json').read_bytes())==r['parent_audit'],'parent audit')
 expected="""'CompactCoefficientMass.values_in_range' depends on axioms: [propext]
'CompactCoefficientMass.selector_mass_exact' depends on axioms: [propext]
'CompactCoefficientMass.copy_mass_exact' depends on axioms: [propext]
'CompactCoefficientMass.coefficient_mass_exact' depends on axioms: [propext]
'CompactCoefficientMass.stencil_mass_exact' depends on axioms: [propext]
'CompactCoefficientMass.triple_stencil_below_half' depends on axioms: [propext]
'CompactCoefficientMass.predecessor_slack' depends on axioms: [propext]
'CompactCoefficientMass.heterogeneous_mass_slack' depends on axioms: [propext]
"""
 results=[]
 for row,side in zip(r['runs'],('author','peer')):
  run=OUT/side;src=Path(row['command'][-3]);obj=run/'CompactCoefficientMass.olean';log=run/'compiler.log'
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
 print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT44_COEFFICIENT_MASS_AUDIT','source_commit':'49d10be3df','pair_commit':'49d10be3df','receipt_sha256':RECEIPT,'recorded_outer_session':96941,'recorded_outer_exit':0,'parent_audit_rerun_exit':q.returncode,'json_rows_checked':len(rows),'selector_mass':sum(weights),'copy_mass':copy,'coefficient_mass':coefficient,'stencil_mass':stencil,'half_radix_margin':2**66-(3*stencil+1),'runs':results,'scope':'Finite natural-number mass/slack and external recipe interpretation; no model graph mass, rotation, carry reset, machine simulation or iPRA claim; inherited provider/resource limitations.'},indent=2))
if __name__=='__main__':main()
