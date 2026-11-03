from pathlib import Path
import ast,hashlib,os,re
root=Path(__file__).resolve().parents[2]; h=root/'research/trace73-gauge-model'; source=h/'Trace73GaugeModel.lean'; runner=h/'run.py'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(source)=='0087bbf34dcd43083ebf730c43a2f1a5ac8a081a9182c59757b4937a09f2997f'
assert sha(runner)=='5369625f82d04877f969d32791b31dec31ecc515028d58651e9f34c36817ed50'
src=runner.read_text(); tree=ast.parse(src); node=next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='pins' for x in n.targets)); assert isinstance(node,ast.Dict)
env={'lean':Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'),'lib':Path('/tmp/trace75-fresh-rebuild-yn60cw_0/lib'),'pkg':Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')}
def path(n):
 if isinstance(n,ast.Name): return env[n.id]
 if isinstance(n,ast.BinOp) and isinstance(n.op,ast.Div): return path(n.left)/ast.literal_eval(n.right)
 assert isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='Path'; return Path(ast.literal_eval(n.args[0]))
for k,v in zip(node.keys,node.values): assert path(k).is_file() and sha(path(k))==ast.literal_eval(v),str(path(k))
roots=list(map(Path,['/tmp/trace73-gaugesign-h910a9nh','/tmp/trace73-model-caa17ucr','/tmp/trace73-gauge-r0w9s5ez','/tmp/trace73-literal-1adlrevr','/tmp/trace73-center-r4z617bq',str(env['lib']),str(env['pkg'])]))
mods=re.findall(r'^import\s+([^\s]+)',source.read_text(),re.M); assert mods==['Trace73GaugeSign','Trace73ModelTransfer']
expected=['/tmp/trace73-gaugesign-h910a9nh/Trace73GaugeSign.olean','/tmp/trace73-model-caa17ucr/Trace73ModelTransfer.olean']
for mod,want in zip(mods,expected):
 candidates=[p/(mod+'.olean') for p in roots if os.path.lexists(p/(mod+'.olean'))]; assert candidates and candidates[0].is_file() and str(candidates[0])==want; print(mod,'first',candidates[0])
for mod in ('Mathlib/Tactic/Linarith.olean','Mathlib/Algebra/Order/Ring/Basic.olean'):
 candidates=[p/mod for p in roots if os.path.lexists(p/mod)]; assert candidates and candidates[0].is_file() and candidates[0]==env['pkg']/mod
print('PASS source, runner, 12 pinned provider hashes and first selected direct/mathlib objects; no Lean run')
