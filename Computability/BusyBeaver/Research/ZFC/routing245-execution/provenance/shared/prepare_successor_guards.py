#!/usr/bin/env python3
"""Emit pending Instruction/Runtime guards only; never execute a proof guard."""
from pathlib import Path
import ast,difflib,hashlib,json,re
B=Path('/tmp/zfc-routing245-lean');T=B/'site/check-pending.py';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();assert sha(T)=='b5430ba40f0b9fc87492a1fadddeb4e3821dcbd0bc244204779663fd4c19e8b3'
original=T.read_text()
configs=[
 dict(key='instruction',module='InstructionRouting245',parent='frame',parent_module='Routing245Simulation',parent_probes=14,parent_callers=15,legacy='instruction',legacy_pin='8893e5481a545dec0dbfb49cc64b1e6c00d7c4422ba2082243520982b3063469',probes=7,callers=7,projects=22,extras=[],full_prints=False,scope='Positive whole-tape instruction segments, conditional on accepted sites; coverage, startup and PA remain separate.'),
 dict(key='runtime',module='RuntimeInstanceRouting245',parent='instruction',parent_module='InstructionRouting245',parent_probes=7,parent_callers=7,legacy='runtime',legacy_pin='1965fff0430079cec4e3bb067a22ca05ef2d526fe97fae1e7c74fab1e7fa506f',probes=11,callers=12,projects=26,extras=['BusyBeaver.ZFC.RuntimePerm252','BusyBeaver.ZFC.RMBisim','BusyBeaver.ZFC.SiteCoverage'],full_prints=True,scope='Whole-tape halting equivalence conditional on Covered or exact allSites acceptance; coverage, startup and PA remain separate.')]
manifest=[]
for cfg in configs:
 D=B/cfg['key'];S=D/(cfg['module']+'.lean');A=D/'Audit.lean';inv=json.loads((D/'source-inventory.json').read_text());bp=json.loads((D/'boundary-plan.json').read_text())
 assert sha(S)==inv['source']['sha256'] and sha(A)==inv['audit']['sha256'];assert(inv['named_probes'],inv['typed_callers'],inv['expected_projects'])==(cfg['probes'],cfg['callers'],cfg['projects'])
 s=original;st=s.index('"""');en=s.index('"""',st+3)+3
 desc=f"Bounded exact245 {cfg['key']} proof with {cfg['projects']} exact prerequisite providers.\nReuses the actual {cfg['parent_module']} PASS closure and {len(cfg['extras'])} unchanged generic\nproviders from the checked246 {cfg['legacy']} record. Source and audit share120s,\n-j1 -M4096, default proof limits. No dependency rebuild, download or version query.\n{cfg['scope']}\n"
 s=s[:st]+'"""'+desc+'"""'+s[en:]
 probes=[x.rsplit('.',1)[-1]for x in re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)];assert len(probes)==cfg['probes']
 expected={q['module']:(q['source_sha256'],q['object_sha256'])for q in bp['providers']if q['module']in cfg['extras']};assert set(expected)==set(cfg['extras'])
 assignments={'MODULE':repr('BusyBeaver.ZFC.'+cfg['module']),'PREFIX':repr('SetTheory.BusyBeaver.ZFC.'+cfg['module']+'.'),'SOURCE_SHA':repr(sha(S)),'AUDIT_SHA':repr(sha(A)),'LEGACY_SHA':repr(cfg['legacy_pin']),'EXPECTED':repr(expected),'PROBES':repr(probes),'PARENTS':repr({cfg['parent']:(str(B/cfg['parent']/'run1/verification.json'),'PENDING_'+cfg['parent'].upper()+'_PASS','BusyBeaver.ZFC.'+cfg['parent_module'],cfg['parent_probes'],cfg['parent_callers'])}),'CALLERS':str(cfg['callers'])}
 for name,value in assignments.items():s,n=re.subn(r'^'+name+'=.*$',name+'='+value,s,flags=re.M);assert n==1
 changes=[
  ("Freeze the actual successful Symbolic record before preparation or proof.",f"Freeze the actual successful {cfg['parent_module']} record before preparation or proof."),
  ("HERE/'SiteRouting245.lean'",'HERE/'+repr(cfg['module']+'.lean')),
  ("results/prefix246-site-verification.json",'results/prefix246-'+cfg['legacy']+'-verification.json'),
  ("passed(legacy);assert(legacy['named_axiom_probes'],legacy['callers'])==(12,13)",f"passed(legacy);assert(legacy['named_axiom_probes'],legacy['callers'])==({cfg['probes']},{cfg['callers']})"),
  ("assert imports(S)==['BusyBeaver.ZFC.SymbolicRouting245','BusyBeaver.ZFC.Permutation252Frame']",'assert imports(S)=='+repr(bp['direct_imports'])),
  ("assert re.search(r'^def minDistance : Nat := 64$',S.read_text(),re.M) and re.search(r'^def fuel : Nat := 4000$',S.read_text(),re.M)\n",''),
  ("['SiteRouting245.'+n for n in PROBES]",'[PREFIX+n for n in PROBES]'if cfg['full_prints']else'['+repr(cfg['module']+'.')+'+n for n in PROBES]'),
  ("len(closure)==17",f"len(closure)=={cfg['projects']}"),
  ("project_module_count=17",f"project_module_count={cfg['projects']}"),
 ]
 for old,new in changes:assert s.count(old)==1,(cfg['key'],old,s.count(old));s=s.replace(old,new)
 ast.parse(s);G=D/'check-pending.py';assert not G.exists();G.write_text(s)
 (D/'guard-from-site.diff').write_text(''.join(difflib.unified_diff(original.splitlines(True),s.splitlines(True),fromfile=str(T),tofile=str(G))))
 manifest.append(dict(key=cfg['key'],module=cfg['module'],guard=dict(path=str(G),sha256=sha(G)),source=dict(path=str(S),sha256=sha(S)),audit=dict(path=str(A),sha256=sha(A)),legacy_evidence=cfg['legacy_pin'],parent='PENDING_'+cfg['parent'].upper()+'_PASS',project_providers=cfg['projects'],named_probes=cfg['probes'],typed_callers=cfg['callers'],extra_providers=expected,scope=cfg['scope']))
 print(cfg['key'],sha(G))
O=B/'successor-guards-preparation.json';assert not O.exists();O.write_text(json.dumps(dict(status='SOURCE_ONLY_PENDING_PARENTS',template=dict(path=str(T),sha256=sha(T)),guards=manifest,shared_seconds=120,lean_flags=['-j1','-M4096'],source_audit_bytes_unchanged=True,guard_execution=False,compiler_execution=False),indent=2)+'\n')
