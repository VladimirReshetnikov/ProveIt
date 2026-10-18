#!/usr/bin/env python3
"""Source-only cut42 refinement; copy every other v2 source byte, reuse the actual passed cut43."""
from pathlib import Path
import argparse,hashlib,json,re
HERE=Path(__file__).resolve().parent
V2_MANIFEST_SHA='70a67b42ca63d8c363e7e100e3621ee5c332fa7c50c4735dbce3d61cb316ac48'
V2_GUARD_SHA='ac8761cc41db43183f72846fc6078d943a390c9eec3ab4c0b1d5d37c6bde527c'
V2_GENERATOR_SHA='2aa18532c04bc991ddef938c51df0cf08988a614a0278ea9f2261226a7e95576'
FAILED_SHA='e4c402e883fe27e58e7caba2542a51adfee9cf97a33fdcc293b4fff8e723bab5'
ROOT_REVIEW_SHA='221101c650e30bfb581f4003ad0f4000d7d110b4e3ef7e3fc27352d374fa3c94'
CUT43_RECORD_SHA='4ae32a10f2da423204bc04b50a8609f9a6fc2495cb99831135c53496af1aafc7'
CUT43_ROOT_REVIEW_SHA='d62723f952a5b5ec19015a56a3f96f891340bb4e97b0b6ae2ce2988cab6a35af'
NS='SetTheory.BusyBeaver.ZFC.SitesRouting245'
BASE_IMPORTS=['BusyBeaver.ZFC.ProgramRouting245','BusyBeaver.ZFC.SiteCoverage','BusyBeaver.ZFC.SiteRouting245']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def desc(p):return dict(path=str(Path(p).resolve()),sha256=sha(p))
def need(c,m):
 if not c:raise ValueError(m)
def bits(p):return '['+', '.join('true'if c=='1'else'false'for c in p)+']'
def goal(p):return 'allSites SiteRouting245.checkSite '+bits(p[::-1])+'\n      (descend TreeRouting245.tree '+bits(p)+') = true'
def imports(s):return re.findall(r'^import (\S+)',s,re.M)
def audit(module,name,g):
 return ('import BusyBeaver.ZFC.'+module+'\n\nopen SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC\n'
         'open RegisterPath RMBisim SiteCoverage SitesRouting245\n\n#print axioms '+NS+'.'+name+
         '\n\nexample : '+g+' := '+name+'\n')
def checked_cut43(record,u,manifest):
 p=record.resolve();need(sha(p)==CUT43_RECORD_SHA,'Changed actual cut43 PASS.');d=json.loads(p.read_text());need(d['status']=='PASS'and d['prepare_only']is False and
  d['before']==d['after'] and all(d[k]for k in ('only_standard_axioms','all_input_provider_postchecks',
  'all_fresh_objects_unchanged_after_audit','source_object_recorded_before_audit')),'Cut43 is not a complete actual PASS.')
 need(d['manifest']['sha256']==V2_MANIFEST_SHA and d['unit_index']==1 and d['module']==u['module'] and
  (d['named_axiom_probes'],d['callers'])==(1,1),'Wrong passed cut43 identity.')
 need([c['label']for c in d['commands']]==['source','audit']and all(c['exit_code']==0 and not c.get('timed_out',False)
  and c['command'][1:3]==['-j1','-M4096']for c in d['commands']),'Cut43 commands failed.')
 for c in d['commands']:need(Path(c['log']).read_text()==c['output'],'Cut43 raw log differs.')
 for p0,h in d['before'].items():need(sha(p0)==h,'Cut43 input changed '+p0)
 for role in ('source','audit'):
  q=d[role];need(sha(q['path'])==sha(q['snapshot'])==q['sha256']==u[role+'_sha256'],'Cut43 source/audit differs.')
 f=d['fresh_modules'];need(len(f)==1 and f[0]['module']==u['module'],'Wrong cut43 fresh module.');f=f[0]
 need(all(f[k]==d['source_pass_object'][k]for k in ('module','path','sha256','source_sha256')),'Cut43 pre-audit object differs.')
 a=d['fresh_first_provider_before_audit'];ap=a.get('actual_first',a.get('path'))
 need(Path(ap).resolve()==Path(f['path']).resolve() and a['module']==u['module'] and sha(ap)==f['sha256']==a['sha256'],'Cut43 actual provider differs.')
 prep=d['preparation'];need(sha(prep['path'])==prep['sha256'],'Cut43 preparation changed.')
 need(d['actual_axiom_sets'][0]['name']==NS+'.block_43'and set(d['actual_axiom_sets'][0]['axioms'])<={'propext','Quot.sound','Classical.choice'},'Wrong cut43 axiom report.')
 return dict(module=u['module'].rsplit('.',1)[1],full_module=u['module'],record=desc(p),source=desc(d['source']['path']),
  audit=desc(d['audit']['path']),fresh_object=desc(f['path']),source_sha256=f['source_sha256'],probes=1,callers=1,
  probe_names=['block_43'],origin='v2_single_cut',original_unit_index=1,cuts=[43],theorem=NS+'.block_43',
  proof_replay=False,source_seconds=d['commands'][0]['seconds'],audit_seconds=d['commands'][1]['seconds'])
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--v2-manifest',type=Path,required=True)
 ap.add_argument('--output',type=Path,required=True);ap.add_argument('--successful-cut43',type=Path,required=True);a=ap.parse_args()
 m=a.v2_manifest.resolve();need(sha(m)==V2_MANIFEST_SHA,'Changed exact v2 manifest.');old=json.loads(m.read_text())
 need(old['generated_units']==208 and old['reused_unit_count']==16 and old['generated_probes']==430,'Wrong v2 scope.')
 need(old['generator']['sha256']==V2_GENERATOR_SHA==sha(old['generator']['path']),'Changed v2 emitter.')
 guard=m.parent.parent/'check-production-v2.py';need(sha(guard)==V2_GUARD_SHA,'Changed executed v2 guard.')
 failed=m.parent.parent/'cut42-run1/unit000/verification.json';need(sha(failed)==FAILED_SHA,'Changed actual cut42 failure.')
 f=json.loads(failed.read_text());need(f['status']=='FAIL'and f['fresh_modules']==[]and len(f['commands'])==1 and
  f['commands'][0]['exit_code']==1 and not f['commands'][0]['timed_out'],'Cut42 failed scope differs.')
 log=Path(f['commands'][0]['log']);need(log.read_text()==f['commands'][0]['output'] and
  'Error pretty printing: maximum recursion depth has been reached'in log.read_text(),'Wrong failure diagnostic.')
 root=m.parent.parent/'root-cut42-failure-review.json';need(sha(root)==ROOT_REVIEW_SHA,'Changed root cut42 receipt.')
 for q in old['inputs']:need(sha(q['path'])==q['sha256'],'V2 metadata input changed.')
 for u in old['units']:
  for role in ('source','audit'):need(sha(m.parent/u[role])==u[role+'_sha256'],'Changed v2 family.')
 cut=old['cut_frontier'][42];need((cut['lo'],cut['hi'],cut['guards'],cut['leaves'])==(970,1017,61,47),'Wrong cut42.')
 cert=next(Path(q['path'])for q in old['inputs']if Path(q['path']).name=='68-route245-certificate-sites_logical.json')
 sites=json.loads(cert.read_text());children=[]
 for side in '01':
  p=cut['path']+side;xs=[(i,q)for i,q in enumerate(sites)if q[0].startswith(p)]
  need(xs and [i for i,_ in xs]==list(range(xs[0][0],xs[-1][0]+1)),'Noncontiguous actual child.')
  children.append(dict(side=side,path=p,lo=xs[0][0],hi=xs[-1][0]+1,leaves=len(xs),
   guards=sum(2 if q[1]=='CD'else 1 for _,q in xs),height=max(len(q[0])-len(p)for _,q in xs)))
 need([(c['lo'],c['hi'],c['leaves'],c['guards'])for c in children]==[(970,990,20,26),(990,1017,27,35)],'Wrong actual children.')
 oldunit=old['units'][0];need(oldunit['cuts']==[42],'Wrong first v2 unit.')
 original=(m.parent/oldunit['source']).read_text();prefix=original[:original.index('/-- Cut 42:')]
 need(imports(prefix)==BASE_IMPORTS and 'theorem block_42 :\n    '+goal(cut['path'])+' := by decide +kernel'in original,'Original proposition differs.')
 footer='\nend SetTheory.BusyBeaver.ZFC.SitesRouting245\n';files={};units=[]
 def add(module,s,au,name,metadata):
  files[module+'.lean']=s.encode();files[module+'.audit.lean']=au.encode()
  units.append(dict(module='BusyBeaver.ZFC.'+module,source=module+'.lean',audit=module+'.audit.lean',
   source_sha256=hashlib.sha256(s.encode()).hexdigest(),audit_sha256=hashlib.sha256(au.encode()).hexdigest(),
   probe_names=[name],probes=1,callers=1,imports=imports(s),**metadata))
 for c,suffix in zip(children,['Left','Right']):
  module='SitesRouting245Cut042'+suffix;name='block_42_'+suffix.lower()
  c.update(module=module,theorem=NS+'.'+name)
  s=prefix+f"/-- Actual cut42 child {c['side']}: {c['leaves']} leaves / {c['guards']} guards. -/\ntheorem {name} :\n    {goal(c['path'])} := by decide +kernel\n"+footer
  add(module,s,audit(module,name,goal(c['path'])),name,dict(kind='closed_refined_child',cuts=[42],refined_child=c['side'],guards=c['guards'],leaves=c['leaves']))
 p=cut['path'];module='SitesRouting245Cut042'
 s=''.join('import BusyBeaver.ZFC.'+c['module']+'\n'for c in children)
 # Preserve the three base imports first, as required by the unchanged guard execution contract.
 pos=prefix.index('\n\n');s=prefix[:pos+1]+s+prefix[pos+1:]
 s+='theorem block_42 :\n    '+goal(p)+' :=\n  allSites_join SiteRouting245.checkSite '+bits(p[::-1])+'\n'
 s+='    (descend TreeRouting245.tree '+bits(p+'0')+')\n    (descend TreeRouting245.tree '+bits(p+'1')+')\n'
 s+='    '+children[0]['theorem']+' '+children[1]['theorem']+'\n'+footer
 add(module,s,(m.parent/oldunit['audit']).read_text(),'block_42',dict(kind='refined_cut_composition',cuts=[42],guards=61,leaves=47,refinement_children=[c['module']for c in children]))
 reused=list(old['reused_units'])
 r=checked_cut43(a.successful_cut43,old['units'][1],m);reused.append(r)
 root43=m.parent.parent/'root-cut43-pass-review.json';need(sha(root43)==CUT43_ROOT_REVIEW_SHA,'Cut43 root review changed.')
 extra=[desc(a.successful_cut43),desc(root43)]
 for u in old['units'][1:]:
  if u.get('cuts')==[43]:continue
  units.append(u)
  for role in ('source','audit'):files[u[role]]=(m.parent/u[role]).read_bytes()
 extra_count=1;need(len(units)==209 and len(reused)==17,'Wrong successor unit count.')
 need(sum(u['probes']for u in units)==432-extra_count and sum(u['callers']for u in units)==432-extra_count,'Wrong new audit census.')
 report=dict(old);report.update(status='GENERATED_SOURCE_ONLY_UNBUILT',generator=desc(Path(__file__)),
  inputs=old['inputs']+[desc(m),desc(Path(old['generator']['path'])),desc(guard),desc(failed),desc(log),desc(root)]+extra,
  generated_units=len(units),reused_units=reused,reused_unit_count=len(reused),units=units,
  generated_probes=432-extra_count,generated_callers=432-extra_count,complete_probes=476,complete_callers=479,
  refinement=dict(original_cut=42,original_proposition=goal(p),children=children,join_module=module,join_theorem=NS+'.block_42'),
  effective_frontier_cuts=237,effective_binary_joins=236,
  scope='Exact v2 coverage with cut42 proved from both actual children. Every other source body is copied unchanged; all prior successful modules remain directly reused. Extra two child probes produce complete476/479. No complete result until every new unit passes; no bootstrap or PA claim.')
 out=a.output.resolve();need(not out.exists()or not any(out.iterdir()),'Use fresh output; never overwrite attempts.')
 out.mkdir(parents=True,exist_ok=True)
 for n,b in files.items():(out/n).write_bytes(b)
 (out/'generation.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:report[k]for k in ['status','generated_units','reused_unit_count','generated_probes','complete_probes','complete_callers']},indent=2))
if __name__=='__main__':main()
