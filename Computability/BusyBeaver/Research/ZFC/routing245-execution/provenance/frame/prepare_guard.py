"""Author a source-only Frame guard from exact passed parent metadata."""
from pathlib import Path
import ast,difflib,hashlib,json,re
B=Path('/tmp/zfc-routing245-lean/frame');R=Path('/home/codex/.codex/worktrees/ec20/Proofs');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
T=Path('/tmp/zfc-routing245-lean/site/check.py');assert sha(T)=='88f50f68eff40c90aa497b42c177e86b3b6d8a49225490b07d1d198f8b74fef6';old=T.read_text()
E=Path('/tmp/zfc-routing245-lean/site/run1/verification.json');d=json.loads(E.read_text());assert d['status']=='PASS'and d['before']==d['after']and(d['named_axiom_probes'],d['callers'])==(12,13)
for p,h in d['before'].items():assert sha(p)==h
for q in d['fresh_modules']:assert sha(q['path'])==q['sha256']
L=R/'Computability/BusyBeaver/Research/ZFC/results/prefix246-frame-verification.json';ld=json.loads(L.read_text());assert sha(L)=='8aef18790d7553f3f2c68899bae800d16adf6454979df56352c1a3ec9da394b8';assert ld['status']=='PASS'and(ld['named_axiom_probes'],ld['callers'])==(14,14)
expected={}
for m in ['BusyBeaver.ZFC.RMDag','BusyBeaver.ZFC.RMEquiv','BusyBeaver.ZFC.RegisterPathClean']:
 q=next(x for x in ld['reused_modules']if x['module']==m);expected[m]=(q['source_sha256'],q['object_sha256']);assert(sha(q['source']),sha(q['object']))==expected[m]
probes=[n.rsplit('.',1)[1]for n in re.findall(r'^#print axioms (\S+)$',(B/'Audit.lean').read_text(),re.M)];assert len(probes)==14
text=old.replace('Bounded exact245 per-site soundness with17 exact prerequisite providers.\nReuses the actual SymbolicRouting245 PASS closure and only four generic frame\nproviders from the checked246 Site record.','Bounded exact245 whole-tape frame adapters with21 exact prerequisite providers.\nReuses the actual SiteRouting245 PASS closure and only three generic path\nproviders from the checked246 Frame record.')
text=text.replace('All-site acceptance, runtime/startup and PA comparison remain separate.','Accepted-site/representation premises remain explicit; coverage/startup/PA are separate.')
values={'MODULE':'BusyBeaver.ZFC.Routing245Simulation','PREFIX':'SetTheory.BusyBeaver.ZFC.Routing245Simulation.','SOURCE_SHA':sha(B/'Routing245Simulation.lean'),'AUDIT_SHA':sha(B/'Audit.lean'),'LEGACY_SHA':sha(L),'EXPECTED':expected,'PROBES':probes,'PARENTS':{'site':(str(E),sha(E),'BusyBeaver.ZFC.SiteRouting245',12,13)},'CALLERS':15}
for k,v in values.items():
 text,n=re.subn(r'^'+k+r'=.*$',lambda _:k+'='+repr(v),text,flags=re.M);assert n==1,k
text=text.replace('Freeze the actual successful Symbolic record','Freeze the actual successful Site record').replace("HERE/'SiteRouting245.lean'","HERE/'Routing245Simulation.lean'").replace('results/prefix246-site-verification.json','results/prefix246-frame-verification.json')
text=text.replace("passed(legacy);assert(legacy['named_axiom_probes'],legacy['callers'])==(12,13)","passed(legacy);assert(legacy['named_axiom_probes'],legacy['callers'])==(14,14)")
text=text.replace("assert imports(S)==['BusyBeaver.ZFC.SymbolicRouting245','BusyBeaver.ZFC.Permutation252Frame']","assert imports(S)==['BusyBeaver.ZFC.RegisterPathClean','BusyBeaver.ZFC.SiteRouting245']")
text=text.replace("assert re.search(r'^def minDistance : Nat := 64$',S.read_text(),re.M) and re.search(r'^def fuel : Nat := 4000$',S.read_text(),re.M)","assert 'def DispatchFrame64 {states : Nat}' in S.read_text() and '64 ≤ logical.path.length + gap' in S.read_text()")
text=text.replace("==['SiteRouting245.'+n for n in PROBES]","==[PREFIX+n for n in PROBES]")
text=text.replace('len(closure)==17','len(closure)==21').replace('project_module_count=17','project_module_count=21')
assert text[text.index('def save():'):]==old[old.index('def save():'):]
ast.parse(text);G=B/'check.py';assert not G.exists();G.write_text(text)
(B/'guard-from-site.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),text.splitlines(True),fromfile=str(T),tofile=str(G))))
print(json.dumps({'guard':str(G),'sha256':sha(G),'site_record':sha(E),'source':values['SOURCE_SHA'],'audit':values['AUDIT_SHA'],'probes':14,'callers':15,'projects':21},indent=2))
