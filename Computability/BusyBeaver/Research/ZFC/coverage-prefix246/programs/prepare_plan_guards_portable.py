#!/usr/bin/env python3
"""Freeze per-unit exact source/audit/provider guards; source generation only.
The site PASS pin is optional only for drafting. A pending plan cannot execute.
No compiler, guard, version query or dependency build is invoked here.
"""
from pathlib import Path
import argparse,ast,hashlib,json,re
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--plan',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--site-evidence',type=Path);a=p.parse_args()
P=a.plan.resolve();O=a.output.resolve();assert not O.exists() or not any(O.iterdir());O.mkdir(parents=True,exist_ok=True)
plan=json.loads((P/'generation.json').read_text());units=plan['units'];by_module={u['module']:u for u in units};assert len(by_module)==len(units)
sitepin='PENDING_EXACT_SITE246_PASS'
if a.site_evidence:
 j=json.loads(a.site_evidence.read_text());assert j['status']=='PASS' and j['fresh_modules'][0]['module']=='BusyBeaver.ZFC.SitePrefix246';sitepin=sha(a.site_evidence)
base=Path(__file__).with_name('coverage-guard-template.py').read_text().replace('Prefix250','Prefix246').replace('exact250','exact246')
def ancestors(m):
 ans=set()
 for n in by_module[m]['imports']:
  if n in by_module:ans|={n}|ancestors(n)
 return ans
manifest=[]
for u in units:
 m=u['module'];short=m.split('.')[-1];S=P/u['source'];A=P/u['audit'];assert sha(S)==u['source_sha256'] and sha(A)==u['audit_sha256']
 deps={n:dict(source_sha256=by_module[n]['source_sha256'],audit_sha256=by_module[n]['audit_sha256'])for n in u['imports'] if n in by_module}
 assert all(n in {x['module']for x in manifest} for n in deps),'Units must be topologically ordered'
 count=24+len(ancestors(m));g=base
 g=re.sub(r'""".*?"""',f'"""Bounded exact246 coverage unit {short}; {count} exact project prerequisites.\nFresh source/audit only, default proof limits, -j1 -M4096, shared120seconds.\nBoth-child coverage composition; no compiler/version/dependency action in prepare-only.\n"""',g,count=1,flags=re.S)
 for key,value in [('MODULE',m),('SOURCE_SHA',sha(S)),('AUDIT_SHA',sha(A))]:g=re.sub(rf"{key}='[^']+'",f"{key}='{value}'",g)
 g=re.sub(r"PARENTS=\{'site':\('[0-9a-f]+'",f"PARENTS={{'site':('{sitepin}'",g)
 g=re.sub(r'^PROBES=.*$',f"PROBES={u['probe_names']!r}",g,flags=re.M);g=g.replace('CALLERS=1',f"CALLERS={u['callers']}")
 g=g.replace("p.add_argument('--prepare-only',action='store_true')",f"p.add_argument('--dependencies',type=Path)\np.add_argument('--prepare-only',action='store_true')\nDEPENDENCY_PINS={deps!r}")
 g=g.replace("Path('/tmp/zfc-prefix250-lean/coverage/pilot/SitesPrefix246Chunk000.lean')",f'Path({str(S)!r})').replace("Path('/tmp/zfc-prefix250-lean/coverage/pilot/SitesPrefix246Chunk000.audit.lean')",f'Path({str(A)!r})')
 g=g.replace("assert imports(S)==['BusyBeaver.ZFC.ActualTree254', 'BusyBeaver.ZFC.SiteCoverage', 'BusyBeaver.ZFC.SitePrefix246']",f"assert imports(S)=={u['imports']!r}")
 extra='''# Every generated direct predecessor must carry its own exact successful source/audit record.
if DEPENDENCY_PINS:
 assert a.dependencies is not None
 D=a.dependencies.resolve();deprefs=json.loads(D.read_text());assert set(deprefs)==set(DEPENDENCY_PINS)
 evidence[str(D)]=sha(D)
else:
 assert a.dependencies is None or json.loads(a.dependencies.read_text())=={}
 deprefs={}
for module,ref in deprefs.items():
 E=Path(ref['path']).resolve();assert sha(E)==ref['sha256'];parent=json.loads(E.read_text());passed(parent);evidence[str(E)]=sha(E)
 expected=DEPENDENCY_PINS[module]
 assert parent['source']['sha256']==expected['source_sha256'] and parent['audit']['sha256']==expected['audit_sha256']
 assert sha(parent['source']['path'])==sha(parent['source']['snapshot'])==expected['source_sha256']
 assert sha(parent['audit']['path'])==sha(parent['audit']['snapshot'])==expected['audit_sha256']
 assert parent['source_object_recorded_before_audit'] and len(parent['fresh_modules'])==1
 fresh=parent['fresh_modules'][0];assert fresh['module']==module and fresh['source_sha256']==expected['source_sha256']
 assert parent['source_pass_object']==fresh and sha(fresh['path'])==fresh['sha256']
 for q in parent['reused_modules']:add_provider(q,E)
 add_provider(dict(module=module,source=parent['source']['path'],source_sha256=expected['source_sha256'],object=fresh['path'],object_sha256=fresh['sha256']),E)
 parent_snapshots.extend([Path(parent['source']['snapshot']),Path(parent['audit']['snapshot']),Path(parent['audit']['path'])])
 parent_summaries.append(dict(label='generated_direct_dependency',module=module,evidence=str(E),source_sha256=expected['source_sha256'],object_sha256=fresh['sha256'],source_object_recorded_before_audit=True))
'''
 g=g.replace("visiting, closure, tool_names = set(), [], {'Init'}",extra+"visiting, closure, tool_names = set(), [], {'Init'}")
 g=g.replace('len(closure) == 24',f'len(closure) == {count}').replace('project_module_count=24',f'project_module_count={count}')
 ast.parse(g);guard=O/(short+'.check.py');guard.write_text(g)
 manifest.append(dict(u,guard=str(guard),guard_sha256=sha(guard),source_path=str(S),audit_path=str(A),generated_direct_dependencies=list(deps),generated_transitive_dependencies=sorted(ancestors(m)),expected_provider_count=count))
r=dict(status='GUARDS_FROZEN_READY' if a.site_evidence else 'GUARDS_PENDING_SITE_PASS',plan=str(P/'generation.json'),plan_sha256=sha(P/'generation.json'),site_evidence=str(a.site_evidence.resolve())if a.site_evidence else None,site_evidence_sha256=sitepin,units=manifest,full_plan=not plan['representatives_only'],compiler_invoked=False,guard_invoked=False,version_queried=False,scope='Exact independent source/audit checks and generated dependency records; no proof run. All3 final theorem probes and typed callers present.')
(O/'pipeline-manifest.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'units':len(units),'manifest':str(O/'pipeline-manifest.json'),'sha256':sha(O/'pipeline-manifest.json'),'status':r['status']},indent=2))
