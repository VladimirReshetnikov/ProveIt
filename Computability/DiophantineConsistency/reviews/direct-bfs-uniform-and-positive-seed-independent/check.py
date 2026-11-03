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
 ('ten-positive-pell-positive-seed-prototype','PellPositiveSeed','seed-attempt04','bbec5db6d76a94d7b1dbd96c5bb464426a0cf152854258560d3a3181b37cc34a'),
 ('direct-bfs-lean-uniform-decoder-prototype','DirectBFSUniformDecoder','directbfsuniformdecoder-attempt01','63b5e358b90dbf6843d0acc7de06fd13edd0e96890b23f2258a66d27641f90ea'),
 ('direct-bfs-80-uniform-decoder-prototype','DirectBFS80UniformDecoder','directbfs80uniformdecoder-attempt01','b58cca2f3a9e0c330cf7d9873aa9cb66053fa8cd6e6bff776fe0b8d1be618bae'),
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
    src, runner = root / (module + '.lean'), root / 'run.py'
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
        individual = selected in extras
        if name in pins.get('direct_imports', {}):
            item=pins['direct_imports'][name]
            need(item['path']==str(selected) and item['real_path']==str(selected.resolve()) and item['sha256']==h(selected), 'seed direct pin '+name)
            individual=True
        need(individual, 'unpinned direct import ' + module + ':' + name)
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

contains('PellPositiveSeed', '(a R : V) (hphase : R%4=3)', '∃ f i T u y t n : V, 1 < f',
         '0 < t ∧ 0 < n', 'f=1+t ∧ n=D*i+(y-u) ∧ (y-u)+u=y', 'auxiliary_seed a R hphase',
         'positive_auxiliary_witness I u y hy2 haux')
contains('DirectBFSUniformDecoder', 'theorem decode', '(hin : UniformBandInputs.Inputs n C k T)',
         '(hnc : NoCarry (decoderBand n C k T) (Exp.exp 51-2))', 'theorem at4393', 'theorem at5495',
         '(hT : dig 67 T k=0) (hpred : dig 67 T (cyc (8807*N) k 1)=0)')
contains('DirectBFS80UniformDecoder', '(hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)',
         'DirectBFS80UniformReset.graph_uniform_reset p v hp0 hp1 hp2 hp3 hv hz',
         'DirectBFS80Support.graph_support_carry p v hp0 hp1 hp2 hp3 hv hz',
         'Direct80FixedSlots.graph_fixed_slots p v hp0 hp2 hp3 hv hz',
         "have hNN1 : N'=N", "have hNN2 : N''=N", 'E%67=0 ∧ s<N ∧ (E/67)%n=8807*s',
         '(∀ k<n,k%8807=4393 →', '(∀ k<n,k%8807=5495 →',
         'DirectBFSUniformDecoder.decode n (Cnat p v) k 4393 hin hnc',
         'DirectBFSUniformDecoder.decode n (Cnat p v) k 5495 hin hnc')
for directory,module,attempt,_ in E:
    j=json.loads((B/directory/'observations'/attempt/'terminal.json').read_text())
    names=re.findall(r'^import\s+(\S+)',(B/directory/(module+'.lean')).read_text(),re.M)
    if module=='PellPositiveSeed':
        direct=j['pins']['direct_imports']
        need(set(direct)==set(names) and direct==j['after']['direct_imports'], 'seed direct snapshot')
    else:
        direct=j['direct_imports']
        need(direct==j['direct_imports_after'] and [x['module'] for x in direct]==names, 'direct snapshot '+module)
        for row in direct:
            ours=imports[module+':'+row['module']]
            need(Path(ours['path']).resolve()==Path(row['path']) and ours['sha256']==row['sha256'], 'direct resolution '+module)
r=imports['DirectBFS80UniformDecoder:DirectBFS80UniformReset']
need(r['path']=='/tmp/direct-bfs-80-reset-cnoxbcwf/DirectBFS80UniformReset.olean' and
     r['sha256']=='c77bbcc0452ddb98ffdc47a82f8ce13bf1feea7f4b19ec5c67084750c8f97288','corrected reset provider')

print(json.dumps({'status':'PASS', 'modules':out, 'imports':imports, 'resource_samples':sample_count,
                  'historical_receipts':history, 'scope':'selected receipts and direct imports; no Lean replay or full ancestry'}, indent=2, sort_keys=True))
