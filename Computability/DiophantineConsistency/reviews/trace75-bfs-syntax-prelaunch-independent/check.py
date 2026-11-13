from pathlib import Path
import ast,hashlib,os,re
root=Path(__file__).resolve().parents[2]; h=root/'research/trace75-bfs-syntax'; src=h/'TenPositiveTrace75Syntax.lean'; run=h/'run.py'; canonical=root/'Lean/DiophantineConsistency/TenPositiveTrace75Syntax.lean'; lib=Path('/tmp/trace75-fresh-rebuild-yn60cw_0/lib');pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(src)=='46aacc7b43fc5e42095a36265e6ba34853b7aeae70f053b289553ed4dcb18068' and sha(run)=='d0bc3a6b30e82d5860d8bdfc35abb0025dfa7704e2a739504201283047c8948b'
assert sha(canonical)=='6c18ae1ceff5815d4093e6f014fbeaed4ba8de45a1624d88cc9a3ee54306487f' and src.read_bytes()==canonical.read_bytes()+b'\n#print axioms DiophantineConsistency.TenPositiveTrace75.evalRing_expression\n'
tree=ast.parse(run.read_text()); node=next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='pins' for x in n.targets)); env={'canonical':canonical,'lib':lib,'pkg':pkg,'lean':Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')}
def path(n):
 if isinstance(n,ast.Name):return env[n.id]
 if isinstance(n,ast.BinOp) and isinstance(n.op,ast.Div):return path(n.left)/ast.literal_eval(n.right)
 raise ValueError(ast.dump(n))
for k,v in zip(node.keys,node.values):assert path(k).is_file() and sha(path(k))==ast.literal_eval(v),path(k)
mods=re.findall(r'^import\s+([^\s]+)',src.read_text(),re.M);assert mods==['DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.WeightedExpressionDegree']
for mod in mods:
 candidates=[p/(mod.replace('.','/')+'.olean') for p in (lib,pkg) if os.path.lexists(p/(mod.replace('.','/')+'.olean'))];assert candidates and candidates[0].is_file() and candidates[0].is_relative_to(lib);print(mod,'first',candidates[0], 'target',candidates[0].resolve())
print('PASS canonical source plus report, runner, seven provider/source pins and direct first selections; no Lean run')
