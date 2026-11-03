from pathlib import Path
import ast,hashlib,json,os,re
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-bfs-ipra-draft';src=h/'Trace75BFSFixedIPRA.lean';run=h/'run-fixed.py';inventory=h/'overlay-inventory.json';client=h/'observations/attempt01/terminal.json';iff=root/'research/trace75-bfs-model-iff-prototype/observations/modeliff-attempt02/terminal.json';lib=Path('/tmp/trace75-fresh-rebuild-yn60cw_0/lib');pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');overlay=Path('/tmp/trace75-bfs-ipra-overlay-78hgnvd6')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(src)=='4a9f03a96a10bd2b52cb828506c4d89d97524e06e6180476547554a72262fa8d' and sha(run)=='6aec6a4c13a94ae410209ddbcf379627bab736598921a97219923879279ca622' and sha(inventory)=='e946d50e281d5d6326f7e5d1824dbd69deac215def46e148ed0c5923fb6bb028'
tree=ast.parse(run.read_text());node=next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='pins' for x in n.targets));env={'inventory':inventory,'iff_record':iff,'client_record':client,'lib':lib,'pkg':pkg,'lean':Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')}
def path(n):
 if isinstance(n,ast.Name):return env[n.id]
 if isinstance(n,ast.BinOp) and isinstance(n.op,ast.Div):return path(n.left)/ast.literal_eval(n.right)
 assert isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='Path';return Path(ast.literal_eval(n.args[0]))
assert len(node.keys)==16
for k,v in zip(node.keys,node.values):assert path(k).is_file() and sha(path(k))==ast.literal_eval(v),path(k)
inv=json.loads(inventory.read_text());ns=overlay/'DiophantineConsistency';entries=dict(inv['entries']);base=Path(inv['base']);assert len(entries)==1508 and {p.name for p in ns.iterdir()}==set(entries)
for n,target in entries.items():
 p=ns/n;assert p.is_symlink() and os.readlink(p)==target and p.is_file()
 if n!='TenPositiveTrace75Syntax.olean':assert target==str(base/n)
paths=['/tmp/trace75-bfs-ipra-tpj8nxvp']+json.loads(client.read_text())['lean_path'].split(':')
mods={'Trace75BFSIPRA':'75d2988695d143e0e26035d0d977197c4aa1c43d29b671f525c823ec323b6212','Trace75BFSModelIff':'e97639a427341e14bea30db3fed307556bedff7e9dfa50c6710f89f5bbe5c863','Trace75BFSSyntax':'15c89721715979a0071a7e5fa1bfca8d4188fd38b22480f4008532a09b5e3e9c','PositiveModelIPRAReferenceTranslated':'d285f286b99912f7936f004d9a2472b6d6cce2935db2285522561f987aa6e65b'}
for n,d in mods.items():
 candidates=[Path(p)/(n+'.olean') for p in paths if os.path.lexists(Path(p)/(n+'.olean'))];first=candidates[0];assert first.is_file() and sha(first)==d;print(n,'first',first,'target',first.resolve())
names=['native_consistency','standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency'];text=src.read_text();assert re.findall(r'^#print axioms Trace75BFSFixedIPRA\.(\w+)',text,re.M)==names and re.findall(r'^theorem\s+(\w+)',text,re.M)==['port_zero','port_one','port_two','port_three']+names
print('PASS source/runner, 16 pins, 1508 overlay links, four checked first selections, five requested reports; no Lean run')
