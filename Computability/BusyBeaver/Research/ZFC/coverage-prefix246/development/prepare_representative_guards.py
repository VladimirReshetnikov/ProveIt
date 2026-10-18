"""Source-only representative guard preparation; does not invoke generated guards."""
from pathlib import Path
import argparse,ast,difflib,hashlib,json,re
B=Path('/tmp/zfc-prefix246-lean/coverage');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--site-evidence',type=Path);a=p.parse_args()
base=Path('/tmp/zfc-prefix250-lean/coverage/check.py');t=base.read_text().replace('Prefix250','Prefix246').replace('exact250','exact246')
parent_pin='PENDING_EXACT_SITE246_PASS'
if a.site_evidence:
 j=json.loads(a.site_evidence.read_text());assert j['status']=='PASS';assert j['fresh_modules'][0]['module']=='BusyBeaver.ZFC.SitePrefix246';parent_pin=sha(a.site_evidence)
t=re.sub(r"PARENTS=\{'site':\('[0-9a-f]+'",f"PARENTS={{'site':('{parent_pin}'",t)
report=json.loads((B/'representatives/generation.json').read_text());rows=[]
for u in report['units']:
 module=u['module'].split('.')[-1];index=u['cuts'][0];source=B/'representatives'/u['source'];audit=B/'representatives'/u['audit'];g=t.replace('SitesPrefix246Chunk000',module)
 g=g.replace('The first actual subtree has 10 leaves/13 guards; no all-sites claim.',f"Actual cut{index} has {u['leaves']} leaves/{u['guards']} guards; no all-sites claim.")
 g=re.sub(r"SOURCE_SHA='[^']+'",f"SOURCE_SHA='{sha(source)}'",g);g=re.sub(r"AUDIT_SHA='[^']+'",f"AUDIT_SHA='{sha(audit)}'",g)
 g=g.replace("PROBES=['block_0']",f"PROBES=['block_{index}']")
 g=g.replace('/tmp/zfc-prefix250-lean/coverage/pilot/'+module+'.lean',str(source)).replace('/tmp/zfc-prefix250-lean/coverage/pilot/'+module+'.audit.lean',str(audit))
 ast.parse(g);guard=B/'representatives'/f'check-cut{index:03d}.py';guard.write_text(g)
 rows.append(dict(index=index,module=u['module'],source=str(source),source_sha256=sha(source),audit=str(audit),audit_sha256=sha(audit),guard=str(guard),guard_sha256=sha(guard),guards=u['guards'],leaves=u['leaves'],path=report['cut_frontier'][index]['path']))
r=dict(status='GUARDS_SOURCE_ONLY_READY'if a.site_evidence else 'GUARDS_SOURCE_ONLY_PENDING_SITE_PASS',site_record=dict(path=str(a.site_evidence),sha256=parent_pin)if a.site_evidence else None,project_provider_count_expected=24,toolchain_boundaries_expected=['Init','Lean.Elab.Tactic.Omega'],source_only=True,compiler_invoked=False,version_queried=False,guard_invoked=False,root_owned_execution=True,representatives=rows)
(B/'representatives/guard-inventory.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
