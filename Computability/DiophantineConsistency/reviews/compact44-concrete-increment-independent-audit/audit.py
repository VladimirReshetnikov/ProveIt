#!/usr/bin/env python3
"""Independent paired artifact and coherent-provider audit; no Lean compilation."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]; BASE=ROOT/'Computability/DiophantineConsistency'; RESEARCH=BASE/'research/ordinary12-ipra-bridge'
PKG=RESEARCH/'compact44-concrete-increment-prototype'; AUDIT=BASE/'reviews/compact44-concrete-mask-independent-audit'
OUT=Path('/tmp/ipra-compact-concrete-increment-pair-02'); ENDPOINT=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01'); WINDOW=Path('/tmp/ipra-thirteen-parent-window-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
R='ac0892265487e9ff7fadf6d74e434f80caa5eb47ead292169ab9f591820f18e6'
SEEDS={'CompactListMask':('ipra-compact-list-mask-pair-01','1f94ce66997b99f723f9abb990ba91574d0574c10a56d0b514f210a930907c99'), 'CompactConcreteMask':('ipra-compact-concrete-mask-pair-01','741c13117025cac74b3f94eb229f88f764aa101bf3cd9e4af3d4c0c43176cd0b')}
STEPS={
 'CompactDummyBound':('compact44-dummy-bound-prototype','6acfd50bd3e4903d3cc9bbcff4f7fcbe699dd6961b5340be216352c2a52cf69e','1c3c82f68d80795ea1ae61749b1c0509b70132df723b06dafaa00fedfa67d594','10a950d0776ca8ae1fb8d520b7a09f9a05e4c432ea1747163d31edc04df16fc4',('ArithmeticWindowDigits',),('forbidden_zero','ordinary_le_one','dummy_le_three')),
 'CompactMaskSlot':('compact44-mask-slot-prototype','c06708e41c210927dd3b5aba1be721b3e48c84d1a56394f1a26ea9d23cc09ea1','a3dbd600d24333b4c6d5d454b21e532d9e8badce03f9293198a2823caae9cc5f','170c573001cd0081e2aa62a463dfd169154adfe1458907a7105ecb852e486eab',('CompactDummyBound',),('ordinary_at','forbidden_at','dummy_at')),
 'CompactMixedIncrement':('compact44-mixed-increment-prototype','056b203e0b207fb9f88893828df4d721a4aff3106fd85c503285470de9cd713d','23786f0922f76f0a45b4a86feb3f08361000b35ca25c502d5e6c100b5b706f94','ec9e3881125d54848282f6747cd035f2f2dd809ecbca5aeecc6da8bb988d26d8',('CompactMaskSlot','ArithmeticWindowBits'),('decode_mixed_increment',)),
 'CompactConcreteIncrement':('compact44-concrete-increment-prototype','91744fb88bf1f88da6c58d9311ae674ff28c2c9201e415d953a318cafe8976ac','fa69bf1223dc1c1dd6db31dd7a08f51260ae6c733025e0991250392f31670b4f','35d942b62dd6b7b532f4ddf3994ea2f47a81c0fafcc297d2d903985ce586f30e',('CompactConcreteMask','CompactMixedIncrement'),('recipe_digits','mask_eq_bit_recipe'))}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 prefix=PKG.relative_to(ROOT).as_posix()+'/'
 names=subprocess.run(['git','ls-tree','-r','--name-only','dab52dbfea','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
 need(len(names)>=20,'packet inventory')
 for name in names:
  content=subprocess.run(['git','show','dab52dbfea:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(content).hexdigest()==sha(ROOT/name),'packet drift '+name)
 need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==R,'receipt')
 terminal=(PKG/'evidence/terminal.txt').read_text()
 need(terminal.startswith('Observed paired wrapper session 22885 exit 0;') and terminal.rstrip().endswith('PASS_PAIRED_COMPACT_CONCRETE_INCREMENT '+R),'outer observation')
 receipt=json.loads((PKG/'evidence/receipt.json').read_bytes())
 need(receipt['status']=='PASS_PAIRED_COMPACT_CONCRETE_INCREMENT' and len(receipt['runs'])==2,'receipt status')
 for p,h in receipt['fixed_inputs_sha256'].items():need(sha(p)==h,'fixed input '+p)
 fail=(PKG/'observations/preflight-attempt01.txt').read_text()
 need('session 48498 exit 1' in fail and 'before output directory creation or Lean launch' in fail,'failed preflight observation')
 normal=subprocess.run([sys.executable,'-I','-S','-B',str(PKG/'schema_controls.py')],capture_output=True,text=True,timeout=30)
 optimized=subprocess.run([sys.executable,'-O','-I','-S','-B',str(PKG/'schema_controls.py')],capture_output=True,text=True,timeout=30)
 need(normal.returncode==0 and normal.stdout.strip()=='PASS_EXACT_RECEIPT_KEY_CONTROLS' and not normal.stderr,'schema controls')
 need(optimized.returncode!=0 and 'optimized Python rejected' in optimized.stderr,'optimized controls')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,timeout=900)
 need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((AUDIT/'CHECK.json').read_bytes()),'concrete-mask ancestry audit')
 # Explicitly compare common providers; do not silently mix the older six.
 provider_diffs={}
 for side in ('author','peer'):
  win=WINDOW/side/'lib'; end=ENDPOINT/side/'lib'
  a={p.relative_to(win):p for p in win.rglob('*.olean')};b={p.relative_to(end):p for p in end.rglob('*.olean')}
  diff=sorted(str(x) for x in a.keys()&b.keys() if sha(a[x])!=sha(b[x]))
  need(len(diff)==6,'six provider differences');provider_diffs[side]=diff
 need(provider_diffs['author']==provider_diffs['peer'],'provider differences differ')
 results=[]
 for run,side in zip(receipt['runs'],('author','peer')):
  need(run['label']==side and list(x['module'] for x in run['steps'])==list(STEPS),'run ordering')
  lib=OUT/side/'lib'; end=ENDPOINT/side/'lib'
  baseline={p.relative_to(end) for p in end.rglob('*.olean')}; actual={p.relative_to(lib) for p in lib.rglob('*.olean')}
  extras={Path('DiophantineConsistency')/(m+'.olean') for m in (*SEEDS,*STEPS)}
  need(actual==baseline|extras and not baseline&extras,'coherent overlay inventory')
  for rel in baseline:need((lib/rel).resolve()==(end/rel).resolve() and sha(lib/rel)==sha(end/rel),'provider overlay '+str(rel))
  for name,(folder,h) in SEEDS.items():
   seed=lib/'DiophantineConsistency'/(name+'.olean')
   need(sha(seed)==sha(Path('/tmp')/folder/side/(name+'.olean'))==run['seed_sha256'][name]==h,'seed '+name)
  checked=[]
  for step in run['steps']:
   module=step['module'];directory,src_hash,obj_hash,log_hash,imports,reports=STEPS[module]
   src=Path(step['command'][-3]);obj=lib/'DiophantineConsistency'/(module+'.olean');log=OUT/side/(module+'.log')
   need(step['compiler_exit']==step['deps_exit']==0 and step['stop_reason'] is None,'step exits')
   need(sha(src)==sha(RESEARCH/directory/(module+'.lean'))==step['source_sha256']==src_hash,'source '+module)
   need(sha(obj)==step['object_sha256']==obj_hash,'object '+module)
   need(sha(log)==sha(PKG/'evidence'/(side+'-'+module+'.log'))==step['log_sha256']==log_hash and log.read_text()==step['stdout'],'log '+module)
   need(step['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and step['command'][-1]==str(obj),'command '+module)
   expected={str(PACKAGE/'Init.olean')}|{str(lib/'DiophantineConsistency'/(name+'.olean')) for name in imports}
   need(set(step['deps_stdout'].splitlines())==expected and all(Path(x).is_file() for x in expected),'direct imports '+module)
   found=re.findall(r"^'"+module+r"\.([^']+)' depends on axioms: \[([^\]]*)\]$",step['stdout'],re.M)
   need(tuple(n for n,_ in found)==reports and step['axiom_reports']==[[module+'.'+n,a] for n,a in found],'exact reports '+module)
   need(all({x.strip() for x in a.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,a in found),'axioms '+module)
   need(not re.search(r'warning:|error:|sorryAx|\bsorry\b',step['stdout']),'warning '+module)
   checked.append({'module':module,'source_sha256':src_hash,'object_sha256':obj_hash,'recorded_compiler_exit':0,'recorded_deps_exit':0})
  results.append({'side':side,'steps':checked})
 print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT44_CONCRETE_INCREMENT_AUDIT','source_commit':'dab52dbfea','receipt_sha256':R,'recorded_outer_session':22885,'recorded_outer_exit':0,'recorded_failed_preflight_session':48498,'parent_audit_rerun_exit':q.returncode,'schema_normal_exit':normal.returncode,'schema_optimized_exit':optimized.returncode,'older_window_provider_differences':provider_diffs,'runs':results,'scope':'Conditional model decoder with explicit NoCarry and symbolic mask; no retained-MC/graph binding, NoCarry derivation, machine simulation or iPRA; inherited provider and sampled-resource limitations.'},indent=2))
if __name__=='__main__':main()
