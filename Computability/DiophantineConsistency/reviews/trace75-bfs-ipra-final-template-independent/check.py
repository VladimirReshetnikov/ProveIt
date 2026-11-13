from pathlib import Path
import ast,hashlib,json,re,shutil,subprocess,sys,tempfile
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-bfs-ipra-final-assembly-plan';run=h/'run-template.py';test=h/'test-template-policy.py';receipt=h/'observations/template-policy-attempt01/terminal.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(run)=='fb88752365bd40230f660f959c60b6943e065b73145ad5cec80b51c32362ad99' and sha(test)=='36d8ddda5b675c0a45f8088bf2a2b4c4b2252d60f5d9e08e08466a6ca23ce59f' and sha(receipt)=='d46ebbb5e2217fa5bdfcfc80485282466bce385bb3828c13c91831e0c680bde5'
with tempfile.TemporaryDirectory(prefix='trace75-final-template-audit-') as d:
 p=Path(d);shutil.copyfile(run,p/'run-template.py');shutil.copyfile(test,p/'test-template-policy.py');r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'test-template-policy.py')],capture_output=True,text=True);assert r.returncode==0;z=json.loads(r.stdout);assert z['status']=='PASS' and len(z['tests'])==20 and all(z['tests'].values());print('actual copied 20 policy controls PASS')
tree=ast.parse(run.read_text());nodes=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'diag','stage_reports_ok'}];box={'re':re};exec(compile(ast.Module(body=nodes,type_ignores=[]),'policy','exec'),box);fn=box['stage_reports_ok']
for module,names in [('Trace75BFSIPRA',['positive_bridge','native_consistency','standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency']),('Trace75BFSFixedIPRA',['native_consistency','standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency'])]:
 lines=["'"+module+'.'+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in names];text=''.join(lines);assert fn(module,text,'')
 for line in lines:assert not fn(module,text.replace(line,''),'')
 assert not fn(module,text+lines[0],'') and not fn(module,text.replace(lines[0],lines[0].replace('Quot.sound','sorryAx')),'') and not fn(module,text,'bad');print(module,'all',len(names),'omissions, duplicates, forbidden axiom and stderr rejected')
b=json.loads((root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/result.json').read_text())['closure'];g=b['project'];outside=json.loads((root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json').read_text());assert len(outside)==80
for start in ('PositiveModelIPRAReferenceTranslated','DiophantineConsistency.WeightedExpressionDegree','CompactSymbolicBetaCast','CompactSymbolicMaskData'):
 seen=set();ext=set();todo=[start]
 while todo:
  n=todo.pop()
  if n in seen or n in ext:continue
  if n not in g:ext.add(n);continue
  seen.add(n);todo.extend(g[n]['imports'])
 assert start in g and not ext-set(outside);print(start,'captured project',len(seen),'outside',len(ext),'outside absent',len(ext-set(outside)))
print('PASS static copied controls and captured adapter-outside check; no live forward output or Lean')
