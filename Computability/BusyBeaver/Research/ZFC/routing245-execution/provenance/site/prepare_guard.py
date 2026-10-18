#!/usr/bin/env python3
"""Source-only guard adaptation. Does not execute guards, Lean or supplied programs."""
from pathlib import Path
import ast,hashlib,json,re,difflib
B=Path('/tmp/zfc-routing245-lean/site')
T=Path('/tmp/zfc-routing245-lean/symbolic/check.py')
assert hashlib.sha256(T.read_bytes()).hexdigest()=='02a34d7d5cc5942b9ba2729fe558297c4c09534cd3a2522ffbc9227d4c73ddfb'
s=T.read_text(); original=s
start=s.index('"""');end=s.index('"""',start+3)+3
s=s[:start]+'''"""Bounded exact245 per-site soundness with17 exact prerequisite providers.
Reuses the actual SymbolicRouting245 PASS closure and only four generic frame
providers from the checked246 Site record. Source and audit share120s,
-j1 -M4096, default proof limits. No dependency rebuild, download or version
query. All-site acceptance, runtime/startup and PA comparison remain separate.
"""'''+s[end:]
source=B/'SiteRouting245.lean';audit=B/'Audit.lean'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert h(source)=='d05562d7a17c58a45089903977a074ea36559d39a2c5f854d63af5874c951021'
assert h(audit)=='4ec1de96e4c0fb1bcb8a6e498de707b08b75edd8da912f75523088b90cc5b2dd'
bound=json.loads((B/'boundary-plan.json').read_text())
names=['BusyBeaver.ZFC.Table253','BusyBeaver.ZFC.RegisterBoxes253','BusyBeaver.ZFC.RegisterPath','BusyBeaver.ZFC.Permutation252Frame']
expected={q['module']:(q['source_sha256'],q['object_sha256']) for q in bound['providers'] if q['module'] in names}
probes=re.findall(r'^#print axioms SiteRouting245\.(\S+)$',audit.read_text(),re.M)
assert len(probes)==12
assignments={'MODULE':repr('BusyBeaver.ZFC.SiteRouting245'),'PREFIX':repr('SetTheory.BusyBeaver.ZFC.SiteRouting245.'),'SOURCE_SHA':repr(h(source)),'AUDIT_SHA':repr(h(audit)),'LEGACY_SHA':repr('ed4586b081e531b08e17827f04e0ad31730a8a73c19426cf5d927e207f4714cd'),'EXPECTED':repr(expected),'PROBES':repr(probes),'PARENTS':repr({'symbolic':('/tmp/zfc-routing245-lean/symbolic/run1/verification.json','PENDING_SYMBOLIC_PASS','BusyBeaver.ZFC.SymbolicRouting245',15,15)}),'CALLERS':'13'}
for name,value in assignments.items():
 s,n=re.subn(r'^'+name+r'=.*$',name+'='+value,s,flags=re.M);assert n==1,name
replacements=[
 ("BOUNDARY_SHA='f204aaa9fa2c167cb5c1ab078b619bf997fe2df67d4ad36421af7e8f4de819c6'\n",''),
 ("p.add_argument('--boundary',type=Path,default=HERE/'resolved-boundary.json')\n",''),
 ("if not __debug__:p.error('Assertions must remain enabled.')", "if not __debug__:p.error('Assertions must remain enabled.')\nassert all(not spec[1].startswith('PENDING_')for spec in PARENTS.values()), 'Freeze the actual successful Symbolic record before preparation or proof.'"),
 ("HERE/'SymbolicRouting245.lean'","HERE/'SiteRouting245.lean'"),
 ("results/prefix246-symbolic-verification.json","results/prefix246-site-verification.json"),
 ("BP=a.boundary.resolve();assert sha(E0)==LEGACY_SHA and sha(BP)==BOUNDARY_SHA\nlegacy=json.loads(E0.read_text());boundary=json.loads(BP.read_text())","assert sha(E0)==LEGACY_SHA\nlegacy=json.loads(E0.read_text())"),
 ("passed(legacy);assert(legacy['named_axiom_probes'],legacy['callers'])==(15,15)","passed(legacy);assert(legacy['named_axiom_probes'],legacy['callers'])==(12,13)"),
 ("assert imports(S)==['BusyBeaver.ZFC.Routing245Boxes','BusyBeaver.ZFC.FastTableRouting245','BusyBeaver.ZFC.RegisterMarkRouting245','BusyBeaver.ZFC.WritingRuns']","assert imports(S)==['BusyBeaver.ZFC.SymbolicRouting245','BusyBeaver.ZFC.Permutation252Frame']\nassert re.search(r'^def minDistance : Nat := 64$',S.read_text(),re.M) and re.search(r'^def fuel : Nat := 4000$',S.read_text(),re.M)"),
 ("['SymbolicRouting245.'+n for n in PROBES]","['SiteRouting245.'+n for n in PROBES]"),
 ("assert boundary['source']['sha256']==SOURCE_SHA and boundary['audit']['sha256']==AUDIT_SHA\nassert boundary['project_count']==12 and boundary['named_probes']==15 and boundary['typed_callers']==15\nassert len(boundary['providers'])==len(selected)==12\nfor row in boundary['providers']:\n q=selected[row['module']];assert all(q[k]==row[k]for k in('source','source_sha256','object','object_sha256'))\n",''),
 ("len(closure)==12","len(closure)==17"),
 ("assert boundary['toolchain_providers']==legacy['toolchain_providers']\n",''),
 ("S,A,E0,BP,C,ss,aa","S,A,E0,C,ss,aa"),
 (" resolved_boundary=dict(path=str(BP),sha256=sha(BP)),reused_modules="," reused_modules="),
 ("project_module_count=12","project_module_count=17"),
]
for old,new in replacements:
 assert s.count(old)==1,(old,s.count(old));s=s.replace(old,new)
ast.parse(s)
out=B/'check-pending.py';assert not out.exists();out.write_text(s)
(B/'guard-from-symbolic.diff').write_text(''.join(difflib.unified_diff(original.splitlines(True),s.splitlines(True),fromfile=str(T),tofile=str(out))))
receipt={'status':'SOURCE_ONLY_PENDING_PARENT','template':{'path':str(T),'sha256':h(T)},'guard':{'path':str(out),'sha256':h(out)},'source':{'path':str(source),'sha256':h(source)},'audit':{'path':str(audit),'sha256':h(audit)},'legacy_parent':'ed4586b081e531b08e17827f04e0ad31730a8a73c19426cf5d927e207f4714cd','named_probes':12,'typed_callers':13,'expected_projects':17,'known_legacy_providers':expected,'parent':'PENDING_SYMBOLIC_PASS','guard_execution':False,'compiler_execution':False,'note':'The prospective source boundary remains historical. Runtime provider selection uses exact actual parent records and DFS; old pending Boxes source metadata is not consumed.'}
(B/'guard-preparation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(out);print(h(out))
