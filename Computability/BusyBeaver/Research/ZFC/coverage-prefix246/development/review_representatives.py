from pathlib import Path
import ast,hashlib,json,re
B=Path('/tmp/zfc-prefix246-lean/coverage');R=Path('/home/codex/.codex/worktrees/ec20/Proofs');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();P=B.parent/'site/run1/verification.json';MP=R/'Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-mp254-verification.json'
j=json.loads(P.read_text());mp=json.loads(MP.read_text());inventory=json.loads((B/'representatives/guard-inventory.json').read_text());template=(B/'representatives/check-cut000.py').read_text();expected=ast.literal_eval(re.search(r'EXPECTED=(\{.*?\})\nPROBES',template,re.S).group(1));pool={q['module']:q for q in mp['reused_modules']};selected={q['module']:q for q in j['reused_modules']};f=j['fresh_modules'][0];selected[f['module']]=dict(module=f['module'],source=j['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])
for m,(s,o)in expected.items():
 q=pool[m];assert q['source_sha256']==s and q['object_sha256']==o;selected[m]=dict(q,source=str(R/'Computability/BusyBeaver/Lean'/Path(m.replace('.','/')).with_suffix('.lean')))
order=[];tools={'Init'}
def visit(m):
 if m in order:return
 q=selected[m];assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['object_sha256']
 for n in re.findall(r'^import (\S+)',Path(q['source']).read_text(),re.M):
  if n=='Init'or n.startswith(('Lean.','Std.')):tools.add(n)
  else:visit(n)
 order.append(m)
for m in ['BusyBeaver.ZFC.ActualTree254','BusyBeaver.ZFC.SiteCoverage','BusyBeaver.ZFC.SitePrefix246']:visit(m)
assert set(order)==set(selected)and len(order)==24
commands=[]
for u in inventory['representatives']:
 s=Path(u['source']).read_text();a=Path(u['audit']).read_text();g=Path(u['guard']).read_text();ast.parse(g)
 assert sha(u['source'])==u['source_sha256'] and sha(u['audit'])==u['audit_sha256'] and sha(u['guard'])==u['guard_sha256']
 assert re.findall(r'^import (\S+)',s,re.M)==['BusyBeaver.ZFC.ActualTree254','BusyBeaver.ZFC.SiteCoverage','BusyBeaver.ZFC.SitePrefix246']
 assert re.findall(r'^#print axioms (\S+)',a,re.M)==['SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_'+str(u['index'])]and len(re.findall(r'^example\b',a,re.M))==1
 assert 'PENDING_'not in g and sha(P)in g and u['source']in g and u['audit']in g and f"PROBES=['block_{u['index']}']"in g
 # Exact source differs from the frozen250 pilot guard only in declared identifiers,
 # pins, explicit source/audit paths and scope wording; runtime protocol is retained.
 commands.append(['python3','-B',u['guard'],'--repo',str(R),'--site-evidence',str(P),'--output',str(B/f"cut{u['index']:03d}-run1")])
r=dict(status='AUTHOR_FULL_SOURCE_AND_GUARD_REVIEW_NO_EXECUTION',scope='Full three representative sources, focused audits, finite path directions, exact guard delta and24currentsource/objectproviders checked. No claim of independent author review or proof acceptance.',representatives=inventory['representatives'],site_parent=dict(path=str(P),sha256=sha(P)),project_provider_count=24,providers=[selected[m]for m in order],toolchain_boundaries=sorted(tools),commands_in_order=commands,proof_limits='Lean defaults',source_audit_wall_seconds=120,threads=1,memory_mebibytes=4096,findings=[],remaining=['Root-run representative acceptance and timings','Measured grouping choice and full-tree kernel coverage','Blank bootstrap and exact246 runtime/source consistency bridge'],compiler_invoked=False,version_queried=False,guard_invoked=False)
(B/'representatives/source-review.json').write_text(json.dumps(r,indent=2)+'\n')
(B/'representatives/commands.md').write_text('Run in order: pilot0, heavy42, deep210. Each command uses a new output and exact pinned Site246 PASS; root owns execution. Stop on failure and preserve its output.\n\n'+''.join('```sh\n'+' '.join(cmd)+'\n```\n\n'for cmd in commands))
print(sha(B/'representatives/source-review.json'),sha(B/'representatives/commands.md'))
