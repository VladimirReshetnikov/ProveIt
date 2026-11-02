#!/usr/bin/env python3
"""Independent artifact audit for paired symbolic low-mask population."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';RESEARCH=BASE/'research/ordinary12-ipra-bridge';PKG=RESEARCH/'compact44-low-population-exact-prototype'
OUT=Path('/tmp/ipra-compact-low-exact-pair-01');PREFIX=Path('/tmp/ipra-compact-concrete-mask-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');PARENT=BASE/'reviews/compact44-concrete-mask-independent-audit';PRE=BASE/'reviews/compact44-low-exact-prelaunch-audit'
R='01f559aebd1807d3784b14f6cbe6092e9cef8f8b74ec35aa042a81459ed00c41';SEED='741c13117025cac74b3f94eb229f88f764aa101bf3cd9e4af3d4c0c43176cd0b'
STEPS={
 'CompactLowPopulation':('b4b052b87a8883bc5f8096aca1eb1416583a51bda277c6eee95d973f018ed32b','bb9a05b57fa6820c4fbe3795aeefc3137afa57d769748517e9ff106163379047','bb064d001978eba1fc4bfd191f4b592e878a62a75e23c885961048b200130539',('CompactConcreteMask',),('list_population','model_population')),
 'CompactSupportCard':('654b825840ffdd9deda64f6ad608d707231bae9c09b6d7d8ad125467493b73e8','efbf6e9e4079170bf4e83781e8c6de26d92828ba40ada2d9312baeeaec2196c7','5adf288fb4e9baa35219abfd48fbe9fbe958a147a5f968b928c1c63711dde2f4',('CompactConcreteMask',),('support_card',)),
 'CompactLowExact':('189d3a0d400409b26595cdaa1a7aeacf99285481cb91827d2a4f89dd769018f6','b0ce0ce2ceaa2fbcc9106840601b84096b49b60a93a5a92f1ab6ad357c0bf641','e02820bcbc7e0468b2d0abfb6982d4828b2231cd51cde2541fb47bc742367c2e',('CompactLowPopulation','CompactSupportCard'),('model_population',))}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 prefix=PKG.relative_to(ROOT).as_posix()+'/'
 names=subprocess.run(['git','ls-tree','-r','--name-only','3db369c56a','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
 need(len([x for x in names if '/evidence/' in x and x.endswith('.log')])==6,'tracked logs')
 for name in names:
  blob=subprocess.run(['git','show','3db369c56a:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(blob).hexdigest()==sha(ROOT/name),'packet bytes '+name)
 need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==R,'receipt')
 term=(PKG/'evidence/terminal.txt').read_text();need('session 67237 exit 0' in term and '0a5f299b082b2fb216c6eaaf6557ce81fb9b912e' in term and term.rstrip().endswith('PASS_PAIRED_COMPACT_LOW_EXACT '+R),'outer observation')
 rec=json.loads((PKG/'evidence/receipt.json').read_bytes());need(rec['status']=='PASS_PAIRED_COMPACT_LOW_EXACT' and len(rec['runs'])==2,'status')
 for p,h in rec['fixed_inputs_sha256'].items():need(sha(p)==h,'fixed input '+p)
 need(sha(PRE/'CHECK.json')=='cdd2fa488ea378e3b1cc4264d62700bcacb4cbce4db0a3f67e3c7211c55c8629' and json.loads((PRE/'CHECK.json').read_bytes())['status']=='PASS_CONDITIONAL_COMPACT44_LOW_EXACT_PRELAUNCH_AUDIT','prelaunch audit')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=900)
 need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((PARENT/'CHECK.json').read_bytes())==rec['parent_audit'],'parent audit')
 allruns=[]
 for run,side in zip(rec['runs'],('author','peer')):
  need(run['label']==side and [x['module'] for x in run['steps']]==list(STEPS),'order')
  lib=OUT/side/'lib';base=PREFIX/side/'lib';orig={p.relative_to(base) for p in base.rglob('*.olean')};actual={p.relative_to(lib) for p in lib.rglob('*.olean')};seedrel=Path('DiophantineConsistency/CompactConcreteMask.olean');extra={Path('DiophantineConsistency')/(n+'.olean') for n in STEPS}|{seedrel}
  need(not orig&extra and actual==orig|extra,'overlay inventory')
  for rel in orig:need((lib/rel).resolve()==(base/rel).resolve() and sha(lib/rel)==sha(base/rel),'provider '+str(rel))
  seed=lib/seedrel;need(sha(seed)==sha(PREFIX/side/'CompactConcreteMask.olean')==run['seed_sha256']==SEED,'concrete seed')
  available=set(orig)|{seedrel};steps=[]
  for row in run['steps']:
   module=row['module'];src_hash,obj_hash,log_hash,imports,wanted=STEPS[module];src=OUT/side/'src/DiophantineConsistency'/(module+'.lean');obj=lib/'DiophantineConsistency'/(module+'.olean');log=OUT/side/(module+'.log');copy=PKG/'evidence'/side/(module+'.log')
   need(row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'child exit '+module)
   need(sha(src)==sha(PKG/(module+'.lean'))==row['source_sha256']==src_hash and sha(obj)==row['object_sha256']==obj_hash and sha(log)==sha(copy)==row['log_sha256']==log_hash and log.read_text()==row['stdout'],'artifacts '+module)
   cmd=row['command'];need(cmd[1:4]==['-M3000','-j1','-DElab.async=false'] and cmd[-3]==str(src) and cmd[-1]==str(obj),'command')
   deps={str(PACKAGE/'Init.olean')}
   for dep in imports:
    rel=Path('DiophantineConsistency')/(dep+'.olean');need(rel in available,'same-side import '+dep);deps.add(str(lib/rel))
   need(set(row['deps_stdout'].splitlines())==deps and all(Path(x).is_file() for x in deps),'direct imports '+module)
   reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
   need([n for n,_ in reports]==[module+'.'+x for x in wanted] and [[n,a] for n,a in reports]==row['axiom_reports'],'report names')
   need(all({x.strip() for x in a.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,a in reports),'axiom set')
   need(not re.search(r'warning:|error:|\bsorryAx\b|\bsorry\b',row['stdout']),'warning/error')
   available.add(Path('DiophantineConsistency')/(module+'.olean'));steps.append({'module':module,'source_sha256':src_hash,'object_sha256':obj_hash,'log_sha256':log_hash,'recorded_compiler_exit':0,'recorded_deps_exit':0})
  allruns.append({'side':side,'steps':steps})
 need(allruns[0]['steps']==allruns[1]['steps'],'paired outputs')
 print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT44_LOW_EXACT_AUDIT','evidence_commit':'3db369c56a','receipt_sha256':R,'recorded_outer_session':67237,'recorded_outer_exit':0,'reported_launch_head':'0a5f299b082b2fb216c6eaaf6557ce81fb9b912e','parent_audit_rerun_exit':q.returncode,'steps_per_side':3,'runs':allruns,'scope':'Exact population 589083 for the symbolic finite-list low mask in every IΣ₁ model; no retained MC payload/graph port equality, high-mask population, machine/checker or PRA proof; inherited provider/resource limitations.'},indent=2))
if __name__=='__main__':main()
