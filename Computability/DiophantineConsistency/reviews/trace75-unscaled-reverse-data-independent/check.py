from pathlib import Path
import ast, hashlib, json, os, re
root=Path(__file__).resolve().parents[2]; h=root/'research/trace75-unscaled-reverse-data-prototype'; a=h/'observations/data-attempt02'
t=json.loads((a/'terminal.json').read_text()); s=h/'Trace75UnscaledReverseData.lean'; runner=h/'run-v2.py'; obj=Path(t['output_root'])/'Trace75UnscaledReverseData.olean'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'terminal.json')=='1f552b8260ebae0c28db5e7ce6286d9163f148e9a217981f48685c31f307f7b5'
assert t['exit']==0 and t['reason'] is None and t['pins']==t['after']
assert sha(s)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))==t['pins']['source']=='ba0ef403b5834e1896ff1684bd6dbe1329a06b64947227eb76bd53ac0a0d8244'
assert sha(runner)==t['pins']['runner']=='355387c7b5870a871e34ef44dccfa15dea0c8c614a9ca653d22ec2a633b31fe0'
assert obj.is_file() and not obj.is_symlink() and sha(obj)==t['object_sha256']=='3ef7b82ef551100f48e1f932c0663f786eb4218f100ab8fa154890525baffc80'
for n in ('stdout','stderr'): assert sha(a/n)==t[n+'_sha256']
assert (a/'stdout').read_text()=="'Trace75UnscaledReverseData.reverse_data' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (a/'stderr').read_bytes()
mods=re.findall(r'^import\s+([^\s]+)',s.read_text(),re.M)
assert mods==['ScaledReverseStart','ScaledAuxiliarySeed','Trace75GenericCarrier','Trace75SeedOffset']
for mod in mods:
    candidates=[Path(p)/(mod.replace('.','/')+'.olean') for p in t['lean_path'].split(':') if os.path.lexists(Path(p)/(mod.replace('.','/')+'.olean'))]
    first=candidates[0]; entry=t['pins']['direct_imports'][mod]
    assert first.is_file() and str(first)==entry['path'] and str(first.resolve())==entry['real_path'] and sha(first)==entry['sha256']
    print(mod,'first',first)
tree=ast.parse(runner.read_text()); extra=[]
def collect(node):
    if isinstance(node, ast.ListComp):
        names=ast.literal_eval(node.generators[0].iter)
        return [str(Path('/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency')/(n+'.olean')) for n in names]
    if isinstance(node, ast.List):
        return [ast.literal_eval(x.args[0]) for x in node.elts if isinstance(x,ast.Call) and isinstance(x.func,ast.Name) and x.func.id=='Path']
    raise ValueError('unexpected list')
for node in tree.body:
    if isinstance(node,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='extra' for x in node.targets): extra=collect(node.value)
    if isinstance(node,ast.AugAssign) and isinstance(node.target,ast.Name) and node.target.id=='extra': extra+=collect(node.value)
    if isinstance(node,ast.Expr) and isinstance(node.value,ast.Call) and isinstance(node.value.func,ast.Attribute) and isinstance(node.value.func.value,ast.Name) and node.value.func.value.id=='extra':
        call=node.value
        if call.func.attr=='append': extra.append(ast.literal_eval(call.args[0].args[0]))
        elif call.func.attr=='extend': extra+=collect(call.args[0])
assert [sha(p) for p in extra]==t['pins']['extra']
assert sha('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')==t['pins']['lean']
assert sha('/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/ArithmeticGcdNormalization.olean')==t['pins']['direct_provider']
for snap in [t['preflight'],*t['samples']]: assert snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2
failed=json.loads((h/'observations/data-attempt01/terminal.json').read_text()); assert failed['exit']!=0 and 'sorryAx' in (h/'observations/data-attempt01/stdout').read_text()
print('PASS terminal, source/copy, object, exact report,',len(extra),'historical extra pins, four direct selections and failed attempt')
