from pathlib import Path
import ast,hashlib,json,os,re
root=Path(__file__).resolve().parents[2]; h=root/'research/trace75-packing-reverse-graph-prototype'; a=h/'observations/data-attempt01'; om=root/'research/trace75-unscaled-reverse-graph-prototype/observations/overlay-attempt01/result.json'
t=json.loads((a/'terminal.json').read_text()); overlay=json.loads(om.read_text()); s=h/'Trace75PackingReverseGraph.lean'; runner=h/'run.py'; obj=Path(t['output_root'])/'Trace75PackingReverseGraph.olean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'terminal.json')=='d5b4ac7a73e7879fad3095cec2a2148ba893343cec4aba84bbd0b0c589113c4d'
assert sha(om)==t['pins']['overlay_manifest']=='60f41f892354d0fb1fab6b07e15c1881a34a1e1fc9d3e9da6f2c5079d33e6845'
assert t['exit']==0 and t['reason'] is None and t['pins']==t['after']
assert sha(s)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))==t['pins']['source']=='f2df75f3095931d210c271b312b07c737dd7dfe35dfaaf430480d5c0980eeb98'
assert sha(runner)==t['pins']['runner']=='d1aaf764daf8f5f768fd7e8a3c802f1bfb5ae5777aa6a27f43d81fc9cf449936'
assert obj.is_file() and not obj.is_symlink() and sha(obj)==t['object_sha256']=='e41a9a3876c2204ee885e9a46cff630289ff6ae023303860227e6bff3498e047'
for n in ('stdout','stderr'): assert sha(a/n)==t[n+'_sha256']
assert (a/'stdout').read_text()=="'Trace75PackingReverseGraph.packing_seed_zero' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (a/'stderr').read_bytes()
mods=re.findall(r'^import\s+([^\s]+)',s.read_text(),re.M); assert mods==['Trace75UnscaledReverseGraph','CompactHaltFirstSeed']
for mod in mods:
    candidates=[Path(p)/(mod+'.olean') for p in t['lean_path'].split(':') if os.path.lexists(Path(p)/(mod+'.olean'))]; first=candidates[0]; e=t['pins']['direct_imports'][mod]
    assert first.is_file() and str(first)==e['path'] and str(first.resolve())==e['real_path'] and sha(first)==e['sha256']; print(mod,'first',first)
old,fresh=overlay['old'],overlay['fresh']; assert (len(old),len(fresh),len(set(old)&set(fresh)))==(1506,998,997)
diff=sorted(n for n in set(old)&set(fresh) if old[n]['sha256']!=fresh[n]['sha256']); assert diff==overlay['differences'] and len(diff)==5
assert set(overlay['selected'])==set(old)|set(fresh)
for label in ('old','fresh'):
    rec=overlay[label]; base=Path(overlay[label+'_root']); assert {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file() or p.is_symlink()}==set(rec)
    for n,x in rec.items():
        p=base/n; assert str(p)==x['path'] and str(p.resolve(strict=True))==x['target'] and sha(p)==x['sha256']
base=Path(overlay['root'])/'DiophantineConsistency'; assert {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file() or p.is_symlink()}==set(overlay['selected'])
for n,x in overlay['selected'].items():
    assert x==old.get(n,fresh.get(n)); p=base/n; assert p.is_symlink() and str(p.resolve(strict=True))==x['target'] and sha(p)==x['sha256']
tree=ast.parse(runner.read_text()); extra=[]
def collect(node):
    if isinstance(node,ast.ListComp): return [str(Path('/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency')/(n+'.olean')) for n in ast.literal_eval(node.generators[0].iter)]
    assert isinstance(node,ast.List); return [ast.literal_eval(x.args[0]) for x in node.elts if isinstance(x,ast.Call) and isinstance(x.func,ast.Name) and x.func.id=='Path']
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
print('PASS receipt/source/object/report,',len(extra),'extra input pins, two direct selections, overlay inventories and five old-first differences')
print('differences',', '.join(diff))
