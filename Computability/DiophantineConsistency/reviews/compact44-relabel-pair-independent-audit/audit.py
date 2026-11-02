#!/usr/bin/env python3
"""Read-only audit of the paired finite-table proof, not a Lean build."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/ordinary12-ipra-bridge/compact44-relabel-pair-prototype'
OUT=Path('/tmp/ipra-compact-relabel-pair-01');PARENT=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='97a9dc8a8806927e8b1694e1083da79d3ce5bd4f9b0af7393b9231fc810972e7';DRIVER='f2d574483b92a6648462a2700a23e2884ea5572c8f5b2162ccf6b068c9d61510';MANIFEST='7f78a6ee9c9f1e3a3e859e0be035ed31c5c3efc29f7c4fcd887881b4a043f0a0'
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 prefix=PKG.relative_to(ROOT).as_posix()+'/'
 files=subprocess.run(['git','ls-tree','-r','--name-only','b5a95621d2','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
 need(len([x for x in files if '/logs/' in x and x.endswith('.log')])==116,'tracked log count')
 for name in files:
  blob=subprocess.run(['git','show','b5a95621d2:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(blob).hexdigest()==sha(ROOT/name),'committed bytes '+name)
 need(sha(PKG/'replay.py')==DRIVER and sha(PKG/'manifest.json')==MANIFEST,'driver/manifest')
 need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
 terminal=json.loads((PKG/'terminal-observation.json').read_bytes())
 need(terminal.get('session')==43986 and terminal.get('actual_exit_code')==0 and terminal.get('compiler_children')==116 and terminal.get('all_compiler_and_dependency_exits_zero') is True and terminal.get('receipt_sha256')==RECEIPT,'outer terminal observation')
 rec=json.loads((PKG/'replay-receipt.json').read_bytes());manifest=json.loads((PKG/'manifest.json').read_bytes())
 need(rec['status']=='PASS_PAIRED_COMPACT_RELABEL' and len(rec['rows'])==116 and len(manifest)==58 and len(rec['direct_guards'])==1190,'receipt shape')
 for path,h in rec['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed input '+path)
 parent=BASE/'reviews/thirteen-model-endpoint-successor-pair-independent-audit';review=BASE/'reviews/compact44-relabel-pair-prelaunch-audit'
 need(sha(review/'CHECK.json')=='86b32446aac1250639e7853c98eb1cf4d13c30ccba41858e497f1e37814ca059','prelaunch audit pin')
 prior=json.loads((review/'CHECK.json').read_bytes());need(prior['driver_sha256']==DRIVER and prior['status']=='PASS_CONDITIONAL_COMPACT44_RELABEL_PRELAUNCH_AUDIT','prelaunch status')
 for directory in (parent,BASE/'reviews/compact44-color-relabel-independent-audit',BASE/'reviews/compact44-943-table-independent-audit'):
  q=subprocess.run([sys.executable,'-I','-S','-B',str(directory/'audit.py')],capture_output=True,timeout=900)
  need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((directory/'CHECK.json').read_bytes()),'parent audit '+str(directory))
 need(json.loads((parent/'CHECK.json').read_bytes())==rec['parent_audit'],'parent receipt')
 for item in manifest:
  source=ROOT/item['source'];frozen=OUT/'src/DiophantineConsistency'/(item['module']+'.lean')
  blob=subprocess.run(['git','show',item['anchor']+':'+item['source']],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(blob).hexdigest()==sha(source)==sha(frozen)==item['sha256'],'anchored source '+item['module'])
 guards=rec['direct_guards'];need(len(guards)==1190,'guard count')
 for k,v in guards.items():
  p=Path(k)
  if v is None:need(not os.path.lexists(p),'unexpected companion '+k)
  else:need(p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],'companion drift '+k)
 allruns=[];expected_guard_paths=set()
 for side,offset in (('author',0),('peer',58)):
  lib=OUT/side/'lib';base=PARENT/side/'lib';original={p.relative_to(base) for p in base.rglob('*.olean')};actual={p.relative_to(lib) for p in lib.rglob('*.olean')};extra={Path('DiophantineConsistency')/(i['module']+'.olean') for i in manifest}
  need(not original&extra and actual==original|extra,'parent overlay inventory')
  for rel in original:need((lib/rel).resolve()==(base/rel).resolve() and sha(lib/rel)==sha(base/rel),'parent object '+str(rel))
  available=set(original);results=[]
  for ix,item in enumerate(manifest):
   row=rec['rows'][offset+ix];name=item['module'];src=OUT/'src/DiophantineConsistency'/(name+'.lean');obj=lib/'DiophantineConsistency'/(name+'.olean');log=OUT/side/(name+'.log');copy=PKG/'logs'/side/(name+'.log')
   need(row['side']==side and row['module']==name and row['exit']==row['deps_exit']==0 and row['stop_reason'] is None,'child exit/order '+name)
   need(sha(src)==row['source_sha256']==item['sha256'] and sha(obj)==row['object_sha256'] and sha(log)==sha(copy)==row['log_sha256'],'artifact '+name)
   need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-3]==str(src) and row['command'][-1]==str(obj),'command '+name)
   imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M);deps={str(PACKAGE/'Init.olean')}
   for imp in imports:
    rel=Path(*imp.split('.')).with_suffix('.olean');need(imp.startswith('DiophantineConsistency.') and rel in available,'same-side import '+name+':'+imp);deps.add(str(lib/rel))
   need(set(row['deps_stdout'].splitlines())==deps and all(Path(p).is_file() for p in deps),'direct imports '+name)
   for dep in deps:
    stem=dep[:-6]
    for suffix in SUFFIXES:expected_guard_paths.add(stem+suffix)
   text=log.read_text();need(not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text),'warning/error '+name)
   reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",text,re.M)
   wanted=re.findall(r'^#print axioms\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M)
   need([n for n,_ in reports]==wanted and [[n,a] for n,a in reports]==row['axiom_reports'],'exact reports '+name)
   for decl,axs in reports:
    actual_axioms={x.strip() for x in axs.split(',') if x.strip()}
    if decl.endswith(('.rows_length','.row_widths')) or re.fullmatch(r'CompactRelabelDraft.forward_\d\d',decl):want=set()
    elif decl.endswith(('.row_bounds','.forward_roundtrip')):want={'propext','Quot.sound'}
    else:want={'propext','Classical.choice','Quot.sound'}
    need(actual_axioms==want,'axiom set '+decl)
   available.add(Path('DiophantineConsistency')/(name+'.olean'));results.append({'module':name,'source_sha256':row['source_sha256'],'object_sha256':row['object_sha256'],'log_sha256':row['log_sha256'],'recorded_compiler_exit':0,'recorded_deps_exit':0})
  allruns.append({'side':side,'modules':results})
 need(set(guards)==expected_guard_paths,'complete direct companion guard set')
 need(allruns[0]['modules']==allruns[1]['modules'],'paired source/object/log equality')
 print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT44_RELABEL_PAIR_AUDIT','evidence_commit':'b5a95621d2','receipt_sha256':RECEIPT,'recorded_outer_session':43986,'recorded_outer_exit':0,'recorded_expected_head':rec['expected_head'],'modules_per_side':58,'direct_companion_guards':len(guards),'parent_audits_rerun':3,'runs':allruns,'scope':'Finite Lean old-table relabeling and index/color permutations; JSON binding remains external, no all-model tiling transport, checker calibration, machine or iPRA theorem; inherited provider/resource limitations.'},indent=2))
if __name__=='__main__':main()
