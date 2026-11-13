#!/usr/bin/env python3
"""Independent read-only audit of compact-specific bounded model lookup."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
ROOT=Path.cwd();BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/ordinary12-ipra-bridge/compact44-table-lookup-prototype'
OUT=Path('/tmp/ipra-compact-table-lookup-pair-01');TABLE=Path('/tmp/ipra-compact-relabel-pair-01');GENERIC=Path('/tmp/ipra-compact-permutation-lookup-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
A=BASE/'reviews/compact44-relabel-pair-independent-audit';B=BASE/'reviews/compact44-permutation-lookup-independent-audit'
R='85b56599968f6be19d102b90b538c57036ef354b724612d340aefb0dc82d8f72';SOURCE='b81000a8f38984688d6ba0cef1149bf541e1f4d5321ab8a5c5baeafdd0f50510';SEED='cae55b0b18ac4ec9cfddebf5b0863064e4edb8662d7aaafa9c35c842b2057590';OBJECT='9b57a68104f2817da284dfc49d4334e6fc8366d75a7d22ec63ef863851ba626c';LOG='6b7041f00c7c701b0b6b83675f9410dbf12de42a0da7553ef71d5def81149fe7'
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 prefix=PKG.relative_to(ROOT).as_posix()+'/'
 names=subprocess.run(['git','ls-tree','-r','--name-only','0a5f299b08','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
 need(len([x for x in names if '/logs/' in x and x.endswith('.log')])==2,'committed logs')
 for name in names:
  blob=subprocess.run(['git','show','0a5f299b08:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(blob).hexdigest()==sha(ROOT/name),'committed drift '+name)
 need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==R,'receipt')
 t=json.loads((PKG/'terminal-observation.json').read_bytes());need(t['session']==33946 and t['actual_exit_code']==0 and t['compiler_children']==2 and t['receipt_sha256']==R,'outer observation')
 rec=json.loads((PKG/'replay-receipt.json').read_bytes());need(rec['status']=='PASS_PAIRED_COMPACT_TABLE_LOOKUP' and len(rec['rows'])==2,'status')
 for p,h in rec['fixed_inputs_sha256'].items():need(sha(p)==h,'fixed input '+p)
 parent_exits=[]
 for directory in (A,B):
  q=subprocess.run([sys.executable,'-I','-S','-B',str(directory/'audit.py')],capture_output=True,timeout=900)
  need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((directory/'CHECK.json').read_bytes()),'parent audit '+str(directory));parent_exits.append(q.returncode)
 need(rec['parent_audit']==[json.loads((x/'CHECK.json').read_bytes()) for x in (A,B)],'parent receipt')
 guards=rec['direct_guards'];need(len(guards)==50,'guard count');expected_guards=set();results=[]
 for k,v in guards.items():
  p=Path(k)
  if v is None:need(not os.path.lexists(p),'unexpected companion '+k)
  else:need(p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],'companion '+k)
 for row,side in zip(rec['rows'],('author','peer')):
  lib=OUT/side/'lib';table=TABLE/side/'lib';generic=GENERIC/side/'lib';tf={p.relative_to(table) for p in table.rglob('*.olean')};gf={p.relative_to(generic) for p in generic.rglob('*.olean')};of={p.relative_to(lib) for p in lib.rglob('*.olean')}
  seedrel=Path('DiophantineConsistency/CompactPermutationInterface.olean');outrel=Path('DiophantineConsistency/CompactTableLookup.olean')
  need(not tf&{seedrel,outrel} and of==tf|{seedrel,outrel},'overlay inventory')
  for rel in tf:need((lib/rel).resolve()==(table/rel).resolve() and sha(lib/rel)==sha(table/rel),'table provider '+str(rel))
  overlap=sorted(tf&gf);need(len(overlap)==row['overlap_objects']==1149,'overlap count');overlap_manifest=[]
  for rel in overlap:
   av=[];bv=[]
   for suffix in SUFFIXES:
    pa=Path(str(table/rel)[:-6]+suffix);pb=Path(str(generic/rel)[:-6]+suffix)
    if os.path.lexists(pa):need(pa.is_file(),'table companion');av.append(sha(pa))
    else:av.append(None)
    if os.path.lexists(pb):need(pb.is_file(),'generic companion');bv.append(sha(pb))
    else:bv.append(None)
   need(av==bv,'overlap companions '+str(rel));overlap_manifest.append({'object':str(rel),'companion_sha256':av})
  digest=hashlib.sha256(json.dumps(overlap_manifest,sort_keys=True,separators=(',',':')).encode()).hexdigest();need(digest==row['overlap_manifest_sha256'],'overlap digest')
  seed=lib/seedrel;source_seed=generic/seedrel;need(sha(seed)==sha(source_seed)==row['generic_seed_sha256']==SEED,'seed')
  for suffix in SUFFIXES[1:]:need(not os.path.lexists(Path(str(source_seed)[:-6]+suffix)),'generic seed companion')
  src=OUT/'src/DiophantineConsistency/CompactTableLookup.lean';obj=lib/outrel;log=OUT/side/'CompactTableLookup.log';copy=PKG/'logs'/side/'CompactTableLookup.log'
  need(row['side']==side and row['module']=='CompactTableLookup' and row['exit']==row['deps_exit']==0 and row['stop_reason'] is None,'child exits')
  need(sha(src)==sha(PKG/'CompactTableLookup.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT and sha(log)==sha(copy)==row['log_sha256']==LOG,'source/object/log')
  cmd=row['command'];need(cmd[1:4]==['-M4000','-j1','-DElab.async=false'] and cmd[-3]==str(src) and cmd[-1]==str(obj),'command')
  deps={str(PACKAGE/'Init.olean'),str(lib/'DiophantineConsistency/CompactRelabelFinal.olean'),str(seed)};need(set(row['deps_stdout'].splitlines())==deps and all(Path(x).is_file() for x in deps),'direct imports')
  for dep in deps:
   for suffix in SUFFIXES:expected_guards.add(dep[:-6]+suffix)
  text=log.read_text();reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
  wanted=['CompactTableLookup.'+x for x in ('row_injective','row_surjective','horizontal_injective','horizontal_surjective','vertical_injective','vertical_surjective')]
  need([n for n,_ in reports]==wanted and [[n,a] for n,a in reports]==row['axiom_reports'],'report names')
  need(all({x.strip() for x in a.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,a in reports),'axiom sets')
  need(not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text),'warning/error')
  results.append({'side':side,'source_sha256':SOURCE,'object_sha256':OBJECT,'log_sha256':LOG,'seed_sha256':SEED,'overlap_objects':len(overlap),'overlap_manifest_sha256':digest,'recorded_compiler_exit':0,'recorded_deps_exit':0})
 need(set(guards)==expected_guards,'complete direct guard set')
 print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT44_TABLE_LOOKUP_AUDIT','evidence_commit':'0a5f299b08','receipt_sha256':R,'recorded_outer_session':33946,'recorded_outer_exit':0,'parent_audits_rerun':parent_exits,'overlap_objects_per_side':1149,'direct_companion_guards':len(guards),'runs':results,'scope':'Concrete finite array lookup injectivity/surjectivity for bounded model values including omitted index 1; no arbitrary-model matching neighbors, tiling transport, compact44 checker calibration or iPRA; inherited provider/resource limits.'},indent=2))
if __name__=='__main__':main()
