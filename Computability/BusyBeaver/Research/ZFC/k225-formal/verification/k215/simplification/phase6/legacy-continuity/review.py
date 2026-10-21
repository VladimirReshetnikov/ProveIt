"""Read-only pure-reuse compatibility check after terminal phase6 acceptance.

No compiler runs and no proof object is copied or modified. The older audit
remains historical; its complete45-module import closure is byte-identical.
"""
from pathlib import Path
import argparse,json,hashlib,re

ROOTS=('Computability/BusyBeaver/Lean','Logic/FirstOrder/Lean','SetTheory/ZF/Lean','SetTheory/BoundedConsistency/Lean')
EXTRA={'BusyBeaver.ZFC.'+n for n in ('Dag219Equiv','Enum222','EnumDom','L2Axioms219','L2Axioms222','L2AxiomsDom','L2Control219','L2Dom','L2Lib219','L2Macros219','L2Root219','L2Root222','L2RootDom','RMOffsetBisim','Seed222')}
CLIENTS=['SetTheory.BusyBeaver.ZFC.LegacyAudit.'+n for n in ('root222','root219','rootDom','rootPerm','offset_checker')]
FORMAL='Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--primary-run',type=Path,required=True);p.add_argument('--legacy-run',type=Path,required=True);p.add_argument('--primary-live',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();assert not a.output.exists()
 R=a.repo.resolve();N=a.primary_run.resolve();B=a.legacy_run.resolve();mainpacket=R/FORMAL/'phase6/lean';oldpacket=R/FORMAL/'phase5/legacy'
 pins={str(q):sha(q)for q in [N/'result.json',N/'inventory.json',N/'completed.json',N/'toolchain.json',B/'result.json',B/'inventory.json',B/'completed.json',a.primary_live]}
 pr,pi,pd,tool=[read(N/n)for n in ['result.json','inventory.json','completed.json','toolchain.json']]
 lr,li,ld=[read(B/n)for n in ['result.json','inventory.json','completed.json']]
 live=read(a.primary_live)
 assert pr['status']=='PASS'and pr['primary_project_modules']==187 and pr['typed_audits']==2 and pr['axiom_reports']==10
 assert live['status']=='PASS_LIVE_POST_AUDIT_REVIEW'and live['result_sha256']==sha(N/'result.json')and live['all187_objects_rehashed_after_audits']
 assert sha(N/'inventory.json')==pr['inventory_sha256']and sha(N/'completed.json')==pr['completed_sha256']
 assert lr['status']=='PASS'and lr['project_modules']==199 and lr['fresh_legacy_modules']==15
 assert sha(B/'inventory.json')==lr['inventory_sha256']and sha(B/'completed.json')==lr['completed_sha256']
 assert (B/'result.json').read_bytes()==(oldpacket/'result.json').read_bytes()
 for name in ('inventory.json','completed.json'):assert (B/name).read_bytes()==(oldpacket/name).read_bytes()
 assert read(mainpacket/'live-review.json')==live
 summary=read(mainpacket/'result.json');assert all(summary[k]==v for k,v in pr.items())
 primary={e['module']:e for e in pi['modules']};oldrows={e['module']:e for e in li['modules']};extras=set(oldrows)-set(primary)
 assert extras==EXTRA and len(primary)==187 and set(pd)==set(primary)
 rows=list(pi['modules'])+[e for e in li['modules']if e['module']in extras]
 union={e['module']:e for e in rows};records={**pd,**{m:ld[m]for m in extras}};assert len(union)==len(records)==202
 seen=set();bindings=[];sources={};objects={};logs={}
 for e in rows:
  m=e['module'];rec=records[m];assert set(e['imports'])<=seen|{'Init'};seen.add(m)
  source=R/Path(e['source']).relative_to(R)
  found=[R/root/(m.replace('.','/')+'.lean')for root in ROOTS if(R/root/(m.replace('.','/')+'.lean')).is_file()];assert found==[source]
  assert sha(source)==e['source_sha256']==rec['source_sha256']
  assert rec['status']=='PASS'and rec['dependencies']=={d:records[d]['object_sha256']for d in e['imports']if d in records}
  cache=B if m in extras else N;obj=cache/'objects'/(m.replace('.','/')+'.olean');assert sha(obj)==rec['object_sha256']
  log=Path(rec['log']);assert sha(log)==rec['log_sha256']
  sources[str(source)]=sha(source);objects[str(obj)]=sha(obj);logs[str(log)]=sha(log)
  if m in extras:
   assert e==oldrows[m];bindings.append({'module':m,'source_sha256':e['source_sha256'],'imports':e['imports'],'object_sha256':rec['object_sha256'],'log_sha256':rec['log_sha256'],'dependencies':rec['dependencies']})
 audit=lr['audit'];src=B/'audit/LegacyAudit.lean';log=B/'audit/compiler.log';obj=B/'audit/LegacyAudit.olean'
 assert sha(src)==audit['source_sha256']and sha(log)==audit['log_sha256']and sha(obj)==audit['object_sha256']
 assert src.read_bytes()==(oldpacket/'LegacyAudit.lean').read_bytes()and log.read_bytes()==(oldpacket/'LegacyAudit.log').read_bytes()
 assert audit['status']=='PASS'and audit['exit_code']==0 and not audit['timed_out']
 text=log.read_text();named=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",text)
 assert [n for n,_ in named]==CLIENTS and all({x.strip()for x in ax.split(',')if x.strip()}<={'propext','Classical.choice','Quot.sound'}for _,ax in named)
 assert not any(x in text for x in ['error:','warning:','sorryAx'])
 imports=[x for l in src.read_text().splitlines()if l.startswith('import ')for x in l[7:].split()];reachable=set()
 def visit(m):
  if m=='Init'or m in reachable:return
  reachable.add(m)
  for d in union[m]['imports']:visit(d)
 for m in imports:visit(m)
 assert len(reachable)==45
 for m in reachable:assert union[m]==oldrows[m]and records[m]['object_sha256']==ld[m]['object_sha256']
 for key in ('lean','lake','Init.olean','project_toolchain'):assert sha(tool[key]['path'])==tool[key]['sha256']
 # All202 providers/selected logs and all original record files are reread after the historical audit object.
 for paths in (sources,objects,logs,pins):
  for path,h in paths.items():assert sha(path)==h
 references={}
 for tag,packet in [('phase6_primary',mainpacket),('phase5_legacy',oldpacket)]:
  names=('execution.tar.gz','index.json','result.json','live-review.json','evidence.py','review_saved.py')
  references[tag]={'repository_relative_directory':packet.relative_to(R).as_posix(),'files':{n:sha(packet/n)for n in names}}
 r={'status':'PASS_LIVE_PURE_REUSE_LEGACY_CONTINUITY','primary_modules':187,'legacy_only_modules':15,'union_modules':202,'fresh_legacy_modules':0,'new_legacy_audit_executed':False,'primary_result_sha256':sha(N/'result.json'),'primary_live_review_sha256':sha(a.primary_live),'old_legacy_result_sha256':sha(B/'result.json'),'legacy_bindings':bindings,'historical_audit':{'source_sha256':sha(src),'log_sha256':sha(log),'object_sha256':sha(obj),'reports':named,'direct_imports':imports,'unchanged_transitive_project_provider_hashes':{m:records[m]['object_sha256']for m in sorted(reachable)},'new_execution':False},'references':references,'records_before_and_after':pins,'all202_provider_objects_and_selected_logs_rehashed_after_historical_audit':True,'toolchain_unchanged':True,'reviewer_sha256':sha(__file__),'scope':'Terminal187 primary plus15 retained phase5 legacy proofs, all exact source/import/direct-dependency/object/log bindings. Historical five-client proof and its complete45-module import closure unchanged. No new compiler, legacy module compilation or typed-audit execution; no202-module fresh replay.'}
 a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items()if k in ['status','primary_modules','legacy_only_modules','union_modules','fresh_legacy_modules','new_legacy_audit_executed','primary_result_sha256','reviewer_sha256']},indent=2))
if __name__=='__main__':main()
