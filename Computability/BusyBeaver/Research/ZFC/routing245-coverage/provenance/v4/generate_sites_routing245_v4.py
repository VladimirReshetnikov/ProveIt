#!/usr/bin/env python3
"""Source-only cap32 refinement of remaining unchecked cuts; preserve all actual successes."""
from pathlib import Path
import argparse,hashlib,json,re
HERE=Path(__file__).resolve().parent
V3_MANIFEST_SHA='ca70be3402b6a0b1c33708970ac6400bcba7843382dd43e77fe09c9523e7db6b'
V3_GUARD_SHA='8b86edb49eb4bf9e8f82e6e5f10d012671a804bb4bd8743ab55d710bf3082ec5'
V3_GENERATOR_SHA='2c385ee00333bc4dec8a3b257ff7042de309368140f8b8eb536a6bce06e82f21'
FIRST_BATCH_SHA='a568c1e2f0eb3facd607585864e9c2173d458ed61a70cded24eab43233d7192b'
SECOND_BATCH_SHA='c673e3e4cd5efb5bed419af295b39dd39c8e91312567729e1842e3e62f4e10eb'
FAILED_SHA='c000fe17683398cfedc53f5d692fa556087d5974f0316d1b96d13ee40ac173cc'
PROGRAM_SHA='060a95566e6162b845b3ee734b4134aefeeb3e9c079de705c2d094ca9119ef0b'
SITES_SHA='f77a3fb9729382a0b8cd24d480639862b63ecb76bbc205542d1fc7077c025745'
NS='SetTheory.BusyBeaver.ZFC.SitesRouting245'
BASE_IMPORTS=['BusyBeaver.ZFC.ProgramRouting245','BusyBeaver.ZFC.SiteCoverage','BusyBeaver.ZFC.SiteRouting245']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def desc(p):return dict(path=str(Path(p).resolve()),sha256=sha(p))
def need(c,m):
 if not c:raise ValueError(m)
def bits(p):return '['+', '.join('true' if c=='1' else 'false' for c in p)+']'
def goal(p):return 'allSites SiteRouting245.checkSite '+bits(p[::-1])+'\n      (descend TreeRouting245.tree '+bits(p)+') = true'
def imports(s):return re.findall(r'^import (\S+)$',s,re.M)
def audit(module,names,goals):
 text='import BusyBeaver.ZFC.'+module+'\n\nopen SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC\nopen RegisterPath RMBisim SiteCoverage SitesRouting245\n\n'
 for n in names:text+='#print axioms '+NS+'.'+n+'\n'
 for n,g in zip(names,goals):text+='\nexample : '+g+' := '+n+'\n'
 return text

def actual_tree(old):
 program=next(Path(q['path']) for q in old['inputs'] if q['path'].endswith('/ProgramRouting245.lean'))
 cert=next(Path(q['path']) for q in old['inputs'] if q['path'].endswith('/68-route245-certificate-sites_logical.json'))
 need(sha(program)==PROGRAM_SHA and sha(cert)==SITES_SHA,'Actual tree/certificate bytes changed.')
 text=program.read_text();pat=re.compile(r'^private def row(\d{3}) : Row := \((\(\.[a-z]+ \d+\)|\.halt), (\(\.[a-z]+ \d+\)|\.halt)\)$',re.M)
 def edge(s):
  v=s.strip('()').removeprefix('.').split();return(v[0],int(v[1]) if len(v)>1 else None)
 matches=list(pat.finditer(text));rows={int(m[1]):(edge(m[2]),edge(m[3])) for m in matches}
 need(len(matches)==203 and set(rows)==set(range(203)),'Wrong literal DAG.')
 need('root := 202' in text and 'nnodes := 203' in text and 'def tree : Tree := t202' in text,'Wrong root.')
 expanded=[]
 def expand(i,p):
  for b,e in zip('01',rows[i]):
   if e[0]=='node':need(0<=e[1]<i,'Nontopological child.');expand(e[1],p+b)
   else:need(e[0] in ('inc','decnz','brk','cont','halt'),'Unknown edge.');expanded.append((p+b,e))
 expand(202,'');kind={'CI':'inc','CD':'decnz','CB':'brk','CC':'cont','CH':'halt'}
 need(expanded==[(p,(kind[k],a)) for p,k,a in json.loads(cert.read_text())],'Full actual tree/certificate mismatch.')
 leaf={p:(i,e) for i,(p,e) in enumerate(expanded)};need(len(leaf)==6460,'Duplicate leaf address.')
 meta={}
 def build(p):
  if p in leaf:
   i,e=leaf[p];m=dict(lo=i,hi=i+1,nodes=0,leaves=1,guards=2 if e[0]=='decnz' else 1,height=0)
  else:
   a,b=build(p+'0'),build(p+'1');need(a['hi']==b['lo'],'Nonadjacent intervals.')
   m=dict(lo=a['lo'],hi=b['hi'],nodes=1+a['nodes']+b['nodes'],leaves=a['leaves']+b['leaves'],guards=a['guards']+b['guards'],height=1+max(a['height'],b['height']))
  meta[p]=m;return m
 need(build('')==dict(lo=0,hi=6460,nodes=6459,leaves=6460,guards=8391,height=51),'Wrong full census.')
 return meta

def checked_v3(row,u,index):
 p=Path(row['record']['path']).resolve();need(sha(p)==row['record']['sha256'],'V3 success record changed.')
 d=json.loads(p.read_text());need(row['unit_index']==index and row['module']==u['module'] and row['status']=='PASS','Wrong successful unit.')
 need(d['status']=='PASS' and d['prepare_only'] is False and d['before']==d['after'] and
  all(d[k] for k in ('only_standard_axioms','all_input_provider_postchecks','all_fresh_objects_unchanged_after_audit','source_object_recorded_before_audit')),'Incomplete v3 success.')
 need(d['manifest']['sha256']==V3_MANIFEST_SHA and d['unit_index']==index and d['module']==u['module'] and
  (d['named_axiom_probes'],d['callers'])==(u['probes'],u['callers']),'Wrong actual scope.')
 need([c['label'] for c in d['commands']]==['source','audit'],'Wrong source/audit sequence.')
 for c in d['commands']:
  need(c['exit_code']==0 and not c['timed_out'] and c['command'][1:3]==['-j1','-M4096'],'Failed command.')
  need(Path(c['log']).read_text()==c['output'],'Raw log differs.')
 for p0,h in d['before'].items():need(sha(p0)==h,'Stale actual input '+p0)
 for role in ('source','audit'):
  q=d[role];need(sha(q['path'])==sha(q['snapshot'])==q['sha256']==u[role+'_sha256'],'Source/audit changed.')
 fs=d['fresh_modules'];need(len(fs)==1 and fs[0]['module']==u['module'],'Wrong fresh object.');f=fs[0]
 need(all(f[k]==d['source_pass_object'][k] for k in ('module','path','sha256','source_sha256')),'Missing pre-audit capture.')
 actual=d['fresh_first_provider_before_audit'];ap=actual.get('actual_first',actual.get('path'))
 need(Path(ap).resolve()==Path(f['path']).resolve() and actual['module']==u['module'] and sha(ap)==f['sha256']==actual['sha256'],'Fresh first provider differs.')
 prep=d['preparation'];need(sha(prep['path'])==prep['sha256']==row['preparation']['sha256'],'Preparation changed.')
 pd=json.loads(Path(prep['path']).read_text());need(pd['status']=='PREPARED_NOT_BUILT' and pd['commands']==[] and pd['fresh_modules']==[] and pd['before']==pd['after']==d['before'],'Wrong preparation.')
 need([q['name'] for q in d['actual_axiom_sets']]==[NS+'.'+n for n in u['probe_names']] and
  all(set(q['axioms'])<={'propext','Quot.sound','Classical.choice'} for q in d['actual_axiom_sets']),'Wrong axiom reports.')
 return dict(module=u['module'].rsplit('.',1)[1],full_module=u['module'],record=desc(p),source=desc(d['source']['path']),
  audit=desc(d['audit']['path']),fresh_object=desc(f['path']),source_sha256=f['source_sha256'],probes=u['probes'],callers=u['callers'],
  probe_names=u['probe_names'],origin='v3_production',original_unit_index=index,cuts=u.get('cuts',[]),proof_replay=False,
  source_seconds=d['commands'][0]['seconds'],audit_seconds=d['commands'][1]['seconds'])

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 for n in ('v3-manifest','first-batch','second-batch','output'):ap.add_argument('--'+n,type=Path,required=True)
 a=ap.parse_args();m=a.v3_manifest.resolve();need(sha(m)==V3_MANIFEST_SHA,'Changed v3 manifest.');old=json.loads(m.read_text())
 need((old['generated_units'],old['reused_unit_count'],old['generated_probes'])==(209,17,431),'Wrong predecessor scope.')
 need(old['generator']['sha256']==V3_GENERATOR_SHA==sha(old['generator']['path']),'V3 emitter changed.')
 guard=m.parent.parent/'check-production-v3.py';need(sha(guard)==V3_GUARD_SHA,'V3 actual guard changed.')
 for q in old['inputs']:need(sha(q['path'])==q['sha256'],'Predecessor input changed.')
 for u in old['units']:
  for role in ('source','audit'):need(sha(m.parent/u[role])==u[role+'_sha256'],'V3 family changed.')
 first=a.first_batch.resolve();second=a.second_batch.resolve()
 need(sha(first)==FIRST_BATCH_SHA and sha(second)==SECOND_BATCH_SHA,'Actual v3 batch history changed.')
 b1=json.loads(first.read_text());b2=json.loads(second.read_text())
 for d in (b1,b2):need(d['prepare_only'] is False and d['manifest']['sha256']==V3_MANIFEST_SHA and d['guard']['sha256']==V3_GUARD_SHA,'Wrong batch bindings.')
 need(b1['status']=='PASS_SELECTED_UNITS' and [q['unit_index'] for q in b1['completed_units']]==[0,1,2],'Wrong first actual batch.')
 need(b2['status']=='FAIL' and b2['failed_unit']==8 and [q['unit_index'] for q in b2['completed_units']]==[3,4,5,6,7],'Wrong remaining attempt.')
 failed=Path(b2['failed_record']['path']);need(sha(failed)==b2['failed_record']['sha256']==FAILED_SHA,'Failed record changed.')
 fd=json.loads(failed.read_text());need(fd['status']=='FAIL' and fd['fresh_modules']==[] and len(fd['commands'])==1 and
  fd['commands'][0]['exit_code']==1 and not fd['commands'][0]['timed_out'],'Failure scope changed.')
 log=Path(fd['commands'][0]['log']);need(log.read_text()==fd['commands'][0]['output'] and 'Error pretty printing: maximum recursion depth has been reached' in log.read_text(),'Wrong actual diagnostic.')
 reused=list(old['reused_units'])
 for i,row in enumerate(b1['completed_units']+b2['completed_units']):reused.append(checked_v3(row,old['units'][i],i))
 need(len(reused)==25 and len({u['full_module'] for u in reused})==25,'Wrong reused family.')
 meta=actual_tree(old)
 for c in old['cut_frontier']:need(all(c[k]==meta[c['path']][k] for k in ('lo','hi','nodes','leaves','guards','height')),'Original cut not actual.')
 files={};units=[];refinements=[];footer='\nend '+NS+'\n'
 def add(module,text,names,paths,metadata,aud=None):
  au=audit(module,names,[goal(p) for p in paths]) if aud is None else aud
  files[module+'.lean']=text.encode();files[module+'.audit.lean']=au.encode()
  units.append(dict(module='BusyBeaver.ZFC.'+module,source=module+'.lean',audit=module+'.audit.lean',
   source_sha256=hashlib.sha256(text.encode()).hexdigest(),audit_sha256=hashlib.sha256(au.encode()).hexdigest(),
   probe_names=names,probes=len(names),callers=len(names),imports=imports(text),**metadata))
 for u in old['units'][8:]:
  if u['kind']!='closed_cuts' or u['guards']<=32:
   units.append(u)
   for role in ('source','audit'):files[u[role]]=(m.parent/u[role]).read_bytes()
   continue
  i=u['cuts'][0];c=old['cut_frontier'][i];p=c['path'];original=(m.parent/u['source']).read_text()
  prefix=original[:original.index(f'/-- Cut {i}:')]
  need(imports(prefix)==BASE_IMPORTS and 'theorem block_'+str(i)+' :\n    '+goal(p)+' := by decide +kernel' in original,'Wrong original cut proposition.')
  parts=[];joins=[]
  def split(q):
   if meta[q]['guards']<=32:
    j=len(parts);x=dict(index=j,path=q,**meta[q],module=f'SitesRouting245Cut{i:03d}Part{j:03d}',name=f'part_{i}_{j}')
    parts.append(x);return x['name']
   left=split(q+'0');right=split(q+'1');j=len(joins)
   name=f'block_{i}' if q==p else f'refine_{i}_{j}'
   joins.append(dict(index=j,path=q,left=left,right=right,name=name));return name
  need(split(p)==f'block_{i}' and len(joins)==len(parts)-1 and 2<=len(parts)<=3,'Unexpected local split shape.')
  need(parts[0]['lo']==c['lo'] and parts[-1]['hi']==c['hi'] and all(x['hi']==y['lo'] for x,y in zip(parts,parts[1:])) and
   sum(x['guards'] for x in parts)==c['guards'],'Incomplete refined partition.')
  for x in parts:
   text=prefix+f"/-- Cut {i} actual part {x['index']}: {x['leaves']} leaves / {x['guards']} guards. -/\ntheorem {x['name']} :\n    {goal(x['path'])} := by decide +kernel\n"+footer
   add(x['module'],text,[x['name']],[x['path']],dict(kind='closed_refined_part',cuts=[i],part=x['index'],path=x['path'],guards=x['guards'],leaves=x['leaves']))
  pos=prefix.index('\n\n');text=prefix[:pos+1]+''.join('import BusyBeaver.ZFC.'+x['module']+'\n' for x in parts)+prefix[pos+1:]
  for j in joins:
   q=j['path'];text+='theorem '+j['name']+' :\n    '+goal(q)+' :=\n'
   text+='  allSites_join SiteRouting245.checkSite '+bits(q[::-1])+'\n'
   text+='    (descend TreeRouting245.tree '+bits(q+'0')+')\n    (descend TreeRouting245.tree '+bits(q+'1')+')\n'
   text+='    '+NS+'.'+j['left']+' '+NS+'.'+j['right']+'\n\n'
  text+=footer
  add(u['module'].rsplit('.',1)[1],text,[j['name'] for j in joins],[j['path'] for j in joins],
      dict(kind='refined_cut_composition',cuts=[i],guards=c['guards'],leaves=c['leaves'],refinement_parts=[x['module'] for x in parts]))
  refinements.append(dict(original_cut=i,original_path=p,original_proposition=goal(p),parts=parts,joins=joins,join_module=u['module'],join_theorem=NS+f'.block_{i}'))
 need(len(refinements)==157 and sum(len(x['parts']) for x in refinements)==398 and sum(len(x['joins']) for x in refinements)==241,'Wrong full refinement census.')
 need(len(units)==599 and len(files)==1198 and sum(u['probes'] for u in units)==905 and sum(u['callers'] for u in units)==905,'Wrong generated census.')
 need(sum(u['probes'] for u in reused)==53 and sum(u['callers'] for u in reused)==56,'Wrong retained audit census.')
 available={u['full_module'] for u in reused}
 for u in units:
  need(u['module'] not in available and all(n in available or n in BASE_IMPORTS for n in u['imports']),'Duplicate or forward generated import.')
  available.add(u['module'])
 report=dict(old);report.update(status='GENERATED_SOURCE_ONLY_UNBUILT',generator=desc(Path(__file__)),
  inputs=old['inputs']+[desc(m),desc(Path(old['generator']['path'])),desc(guard),desc(first),desc(second),desc(failed),desc(log)],
  generated_units=599,reused_units=reused,reused_unit_count=25,units=units,generated_probes=905,generated_callers=905,
  complete_probes=958,complete_callers=961,max_guards_per_new_closed_proof=32,
  previous_refinement=old['refinement'],refinements=refinements,effective_frontier_cuts=478,effective_binary_joins=477,
  scope='Every remaining unchecked cut above32 guards is recursively refined along actual tree children and structurally rejoined to its unchanged original block proposition. Eight actual v3 successes and all seventeen earlier modules are reused without replay. Smaller remaining cuts and all outer joins/final are byte-identical. No complete coverage, bootstrap or PA claim before every new unit passes.')
 report.pop('refinement',None)
 out=a.output.resolve();need(not out.exists() or not any(out.iterdir()),'Use a fresh output; never overwrite attempts.')
 out.mkdir(parents=True,exist_ok=True)
 for name,data in files.items():(out/name).write_bytes(data)
 (out/'generation.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:report[k] for k in ('status','generated_units','reused_unit_count','generated_probes','complete_probes','complete_callers')},indent=2))
if __name__=='__main__':main()
