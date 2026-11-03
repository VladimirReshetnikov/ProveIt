from pathlib import Path
import ast,hashlib,json,os,re
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-bfs-ipra-draft';src=h/'Trace75BFSIPRA.lean';run=h/'run.py';inventory=h/'overlay-inventory.json';iff=root/'research/trace75-bfs-model-iff-prototype/observations/modeliff-attempt02/terminal.json';lib=Path('/tmp/trace75-fresh-rebuild-yn60cw_0/lib');pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');overlay=Path('/tmp/trace75-bfs-ipra-overlay-78hgnvd6')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(src)=='8f80194ef34f3031bb60b603cc8cd18c8e487083df85957fe846cc2b72a75f89' and sha(run)=='45c1e512f3307ebaabdf0ca0b86fd0213cb8b463a425f1d1c027dc1dbce84c7e' and sha(inventory)=='e946d50e281d5d6326f7e5d1824dbd69deac215def46e148ed0c5923fb6bb028'
tree=ast.parse(run.read_text());node=next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='pins' for x in n.targets));env={'inventory':inventory,'iff_record':iff,'lib':lib,'pkg':pkg,'lean':Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')}
def path(n):
 if isinstance(n,ast.Name):return env[n.id]
 if isinstance(n,ast.BinOp) and isinstance(n.op,ast.Div):return path(n.left)/ast.literal_eval(n.right)
 assert isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='Path';return Path(ast.literal_eval(n.args[0]))
assert len(node.keys)==14
for k,v in zip(node.keys,node.values):assert path(k).is_file() and sha(path(k))==ast.literal_eval(v),path(k)
inv=json.loads(inventory.read_text());ns=overlay/'DiophantineConsistency';entries=dict(inv['entries']);base=Path(inv['base']);assert inv['overlay']==str(overlay) and len(entries)==1508 and {p.name for p in ns.iterdir()}==set(entries)
for n,target in entries.items():
 p=ns/n;assert p.is_symlink() and os.readlink(p)==target and p.is_file()
 if n!='TenPositiveTrace75Syntax.olean':assert target==str(base/n)
assert entries['TenPositiveTrace75Syntax.olean']=='/tmp/trace75-syntax-ql2wu2mb/DiophantineConsistency/TenPositiveTrace75Syntax.olean'
paths=['/tmp/trace75-bfs-modeliff-tybefjkq','/tmp/trace75-modelsyntax-i60jel9j',str(overlay)]+json.loads(iff.read_text())['lean_path'].split(':')
mods={'Trace75BFSModelIff':'e97639a427341e14bea30db3fed307556bedff7e9dfa50c6710f89f5bbe5c863','Trace75BFSSyntax':'15c89721715979a0071a7e5fa1bfca8d4188fd38b22480f4008532a09b5e3e9c','PositiveModelIPRAReferenceTranslated':'d285f286b99912f7936f004d9a2472b6d6cce2935db2285522561f987aa6e65b'}
for n,d in mods.items():
 candidates=[Path(p)/(n+'.olean') for p in paths if os.path.lexists(Path(p)/(n+'.olean'))];first=candidates[0];assert first.is_file() and sha(first)==d;print(n,'first',first,'target',first.resolve())
names=['positive_bridge','native_consistency','standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency']; source=src.read_text();assert re.findall(r'^theorem\s+(\w+)',source,re.M)==names and re.findall(r'^#print axioms Trace75BFSIPRA\.(\w+)',source,re.M)==names
output=''.join("'Trace75BFSIPRA."+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in names)
def policy(s):
 if re.search(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b',s):return False
 return all(len(r:=re.findall(r"'Trace75BFSIPRA\."+n+r"' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",s,re.S))==1 and set(x.strip() for x in r[0].split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'} for n in names)
assert policy(output)
for n in names:assert not policy(output.replace("'Trace75BFSIPRA."+n+"'", "'other'"))
assert not policy(output+output) and not policy(output+'warning(lean.test): x\n') and not policy(output.replace('Quot.sound','sorryAx',1))
print('PASS source/runner, 14 pins, 1508 links, three direct selections, six named report omission controls; no Lean run')
