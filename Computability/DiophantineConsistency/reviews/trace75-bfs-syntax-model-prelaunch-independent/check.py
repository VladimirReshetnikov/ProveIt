from pathlib import Path
import ast,hashlib,json,os,re
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-bfs-syntax';src=h/'Trace75BFSSyntax.lean';run=h/'run-model.py';invp=h/'overlay-inventory.json';overlay=Path('/tmp/trace75-syntax-union-ozt2ez4r');lib=Path('/tmp/trace75-fresh-rebuild-yn60cw_0/lib');pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(src)=='a43038e641d94e3e670973cba40ee92551ceddf866cd2c6372c2ac473bb6f904' and sha(run)=='aa368b858432b6b68b1fdad86b1220b3f4f2c289224f08ab3cdd6c0e3adc3ee3' and sha(invp)=='43f46b4876d7d269212f473746dd5079760d6c20188c575049ed1bf03dc6bcc5'
tree=ast.parse(run.read_text());node=next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='pins' for x in n.targets));env={'inventory':invp,'lib':lib,'pkg':pkg,'lean':Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')}
def path(n):
 if isinstance(n,ast.Name):return env[n.id]
 if isinstance(n,ast.BinOp) and isinstance(n.op,ast.Div):return path(n.left)/ast.literal_eval(n.right)
 assert isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='Path';return Path(ast.literal_eval(n.args[0]))
for k,v in zip(node.keys,node.values):assert path(k).is_file() and sha(path(k))==ast.literal_eval(v),path(k)
inv=json.loads(invp.read_text());ns=overlay/'DiophantineConsistency';entries=dict(inv['entries']);assert inv['overlay']==str(overlay) and inv['base']==str(lib/'DiophantineConsistency') and len(entries)==999 and set(p.name for p in ns.iterdir())==set(entries)
for n,target in entries.items():
 p=ns/n;assert p.is_symlink() and os.readlink(p)==target and p.is_file()
 if n!='TenPositiveTrace75Syntax.olean':assert target==str(lib/'DiophantineConsistency'/n)
assert entries['TenPositiveTrace75Syntax.olean']=='/tmp/trace75-syntax-ql2wu2mb/DiophantineConsistency/TenPositiveTrace75Syntax.olean'
mods=re.findall(r'^import\s+([^\s]+)',src.read_text(),re.M);assert mods==['DiophantineConsistency.TenPositiveTrace75Syntax','Trace75Factors']
for mod in mods:
 candidates=[p/(mod.replace('.','/')+'.olean') for p in (overlay,lib,pkg) if os.path.lexists(p/(mod.replace('.','/')+'.olean'))];assert candidates and candidates[0].is_file(); print(mod,'first',candidates[0],'target',candidates[0].resolve())
assert sha(overlay/'DiophantineConsistency/TenPositiveTrace75Syntax.olean')=='8349c9a4d22b2bdd2b3cb475570430b1df30a8e7f4e5e8ede9f40fb13a361d68'
assert sha(lib/'Trace75Factors.olean')=='1bae9331cfbca4e35cb48916f135b63eedc8b5c827f8f24ae6f12b2dff111975'
print('PASS candidate/runner/eight pins, 999-link overlay and two direct first selections; no Lean run')
