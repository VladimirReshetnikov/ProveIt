#!/usr/bin/env python3
"""Independent receipt, direct-import and theorem-scope audit; no Lean replay."""
import ast
import json
import re
import sys
from hashlib import sha256
from pathlib import Path

if sys.flags.optimize:
    raise RuntimeError('optimized Python refused')
D = Path(__file__).resolve().parents[2]
B = D / 'research'
L = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
LIB = Path('/tmp/direct90-ipra-join-b66u_qqo/lib')
PROVIDER = LIB / 'DiophantineConsistency/ArithmeticGcdNormalization.olean'

def h(p):
    return sha256(Path(p).read_bytes()).hexdigest()

def need(ok, what):
    if not ok:
        raise RuntimeError(what)

E = [
 ('direct-bfs-80-cell-shift-prototype','DirectBFS80CellShift','directbfs80cell-attempt03','4682d9a03b8616128f926dfdb9aae1705f61f54b02d5927751c44362e7a53890'),
 ('direct-bfs-80-uniform-reset-prototype','DirectBFS80UniformReset','directbfs80reset-attempt03','a696b693525bc47f0097f6176d635a9c0edfd5b70a291d6492b53e5ba607effc'),
]

def expression(n, variables):
    if isinstance(n, ast.Constant):
        return n.value
    if isinstance(n, ast.Name):
        return variables[n.id]
    if isinstance(n, ast.List):
        return [expression(x, variables) for x in n.elts]
    if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == 'Path':
        return Path(expression(n.args[0], variables))
    if isinstance(n, ast.BinOp):
        a, b = expression(n.left, variables), expression(n.right, variables)
        if isinstance(n.op, ast.Div): return a / b
        if isinstance(n.op, ast.Add): return a + b
    if isinstance(n, ast.ListComp):
        need(len(n.generators) == 1 and isinstance(n.generators[0].target, ast.Name)
             and not n.generators[0].ifs, 'unsupported comprehension')
        g = n.generators[0]
        return [expression(n.elt, {**variables, g.target.id: v}) for v in expression(g.iter, variables)]
    raise RuntimeError('unsupported runner expression ' + ast.dump(n))

def runner_extras(path):
    result = []
    for node in ast.parse(path.read_text()).body:
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'extra' for t in node.targets):
            result = expression(node.value, {'lib': LIB})
        elif isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name) and node.target.id == 'extra':
            result.extend(expression(node.value, {'lib': LIB}))
        elif isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
            f = node.value.func
            if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.value.id == 'extra':
                values = expression(node.value.args[0], {'lib': LIB})
                if f.attr == 'append': result.append(values)
                elif f.attr == 'extend': result.extend(values)
                else: raise RuntimeError('unsupported extra method')
    return result

out, imports, history = {}, {}, {}
sample_count = 0
for directory, module, attempt, terminal_pin in E:
    root = B / directory
    obs = root / 'observations' / attempt
    terminal = obs / 'terminal.json'
    src, runner = root / (module + '.lean'), root / 'run-v3.py'
    need(h(terminal) == terminal_pin, 'terminal ' + module)
    receipt = json.loads(terminal.read_text())
    pins = receipt['pins']
    need(receipt['exit'] == 0 and receipt['reason'] is None and pins == receipt['after'], 'status ' + module)
    need(h(src) == h(obs / 'source.txt') == pins['source'], 'source ' + module)
    need(h(runner) == pins['runner'] and h(L) == pins['lean'] and h(PROVIDER) == pins['direct_provider'], 'tool/runner/provider ' + module)
    need(h(obs / 'stdout') == receipt['stdout_sha256'] and h(obs / 'stderr') == receipt['stderr_sha256'], 'logs ' + module)
    stdout = (obs / 'stdout').read_text()
    need(not (obs / 'stderr').read_bytes() and not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:', stdout) and 'sorryAx' not in stdout, 'diagnostics ' + module)
    axioms = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", stdout, re.M)
    need(axioms and all(set(a.strip() for a in ax.split(',')) <= {'propext','Classical.choice','Quot.sound'} for _, ax in axioms), 'axioms ' + module)
    printed = re.findall(r'^#print axioms\s+(\S+)', src.read_text(), re.M)
    need(sorted(printed) == sorted(name for name, _ in axioms), 'axiom targets ' + module)
    obj = Path(receipt['output_root']) / (module + '.olean')
    need(h(obj) == receipt['object_sha256'], 'object ' + module)
    extras = runner_extras(runner)
    need([h(x) for x in extras] == pins['extra'], 'extra input objects ' + module)
    roots = [Path(x) for x in receipt['lean_path'].split(':')]
    for name in re.findall(r'^import\s+(\S+)', src.read_text(), re.M):
        rel = Path(name.replace('.', '/') + '.olean')
        selected = next((r / rel for r in roots if (r / rel).is_file()), None)
        need(selected is not None, 'missing import ' + name)
        if '.' in name:
            namespace = next((r for r in roots if (r / name.split('.')[0]).is_dir()), None)
            need(namespace and (namespace / rel).is_file(), 'namespace shadow ' + name)
        need(selected in extras, 'unpinned direct import ' + module + ':' + name)
        imports[module + ':' + name] = {'path': str(selected), 'sha256': h(selected)}
    pre = receipt['preflight']
    need(pre['mem_available_kib'] >= 8*1024**2 and len(pre['lean']) < 2, 'preflight ' + module)
    for sample in receipt['samples']:
        need(sample['mem_available_kib'] >= 8*1024**2 and len(sample['lean']) <= 2, 'sample ' + module)
        sample_count += 1
    out[module] = {'source': pins['source'], 'object': receipt['object_sha256'], 'object_path': str(obj),
                   'terminal': terminal_pin, 'direct_extra_count': len(extras), 'axioms': axioms}
    for path in sorted((root / 'observations').glob('*/terminal.json')):
        old = json.loads(path.read_text())
        archived = path.parent
        need(h(archived / 'source.txt') == old['pins']['source'] and h(archived / 'stdout') == old['stdout_sha256'] and h(archived / 'stderr') == old['stderr_sha256'], 'archive ' + str(path))
        history[str(path.relative_to(D))] = {'terminal': h(path), 'exit': old['exit'], 'reason': old['reason'], 'object': old['object_sha256']}

for key, row in imports.items():
    name = key.split(':', 1)[1]
    if name in out:
        need(row['sha256'] == out[name]['object'], 'cross-producer mismatch ' + key)

def contains(module, *fragments):
    entry = next(x for x in E if x[1] == module)
    src = (B / entry[0] / (module + '.lean')).read_text()
    need(all(x in src for x in fragments), 'scope/witness ' + module)

contains('DirectBFS80CellShift', '(hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)',
         'E%67=0 ∧ s<N ∧ (E/67)%n=8807*s',
         'DirectBFS80AlignedShift.graph_aligned_shift p v hp0 hp1 hp2 hp3 hv hz',
         'have hNNa : Na=N', "have hNN : N'=N", 'have hNNb : Nb=N')
contains('DirectBFS80UniformReset', '(hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)',
         'E%67=0 ∧ s<N ∧ (E/67)%n=8807*s',
         'DirectBFS80CellShift.graph_cell_shift p v hp0 hp1 hp2 hp3 hv hz',
         'DirectBFS80Support.graph_support_carry p v hp0 hp1 hp2 hp3 hv hz',
         "have hNN : N'=N", "exp_inj (hq'.symm.trans hq)",
         'dig 67 T (cyc n k 1)=0 ∧ carry 67 n a X (cyc n k 1)=0')
for directory,module,attempt,_ in E:
    j=json.loads((B/directory/'observations'/attempt/'terminal.json').read_text())
    direct=j['direct_imports']
    need(direct==j['direct_imports_after'], 'v3 direct import snapshots changed '+module)
    names=re.findall(r'^import\s+(\S+)',(B/directory/(module+'.lean')).read_text(),re.M)
    need([x['module'] for x in direct]==names, 'v3 direct import list '+module)
    for row in direct:
        ours=imports[module+':'+row['module']]
        need(Path(ours['path']).resolve()==Path(row['path']) and ours['sha256']==row['sha256'],
             'v3 recorded import does not match independent resolution '+module+':'+row['module'])
    old_name='directbfs80cell-attempt01' if module=='DirectBFS80CellShift' else 'directbfs80reset-attempt01'
    oldj=json.loads((B/directory/'observations'/old_name/'terminal.json').read_text())
    need(oldj['exit']==0 and oldj['reason'] is None and oldj['pins']['source']==out[module]['source'] and
         oldj['object_sha256']==out[module]['object'], 'old source/object '+module)
r=imports['DirectBFS80CellShift:DiophantineConsistency.SymbolicKBandDraft']
need(r['sha256']=='90516e7b8ec94eb0f4b917979e0c2800c4e8b2c1c3362ea5131baa631415402f', 'corrected cell import')
r=imports['DirectBFS80UniformReset:DirectBFS80CellShift']
need(r['path']=='/tmp/direct-bfs-80-cell-11aqwvq4/DirectBFS80CellShift.olean' and
     r['sha256']==out['DirectBFS80CellShift']['object'],'v3 cell selection')

print(json.dumps({'status':'PASS', 'modules':out, 'imports':imports, 'resource_samples':sample_count,
                  'historical_receipts':history, 'scope':'selected receipts and direct imports; no Lean replay or full ancestry'}, indent=2, sort_keys=True))
