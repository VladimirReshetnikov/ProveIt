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
 ('direct-bfs-80-aligned-shift-prototype','DirectBFS80AlignedShift','directbfs80aligned-attempt01','4da331dfad78dadffdc9ec63e0c0807ef9f87257ca810b5191db28eb67e51a8b'),
 ('direct-bfs-80-cell-shift-prototype','DirectBFS80CellShift','directbfs80cell-attempt01','f16a5a25077a889e40afde678b971d84cd17ef539d311bc44810f5a799b5149f'),
 ('ten-positive-80-to-90-source-data-prototype','Direct80To90SourceData','source-attempt01','2cf134f527a9fa8f0439da113854a76792365c10cf8c8b8657435815a4ac562a'),
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
        imports[module + ':' + name] = {'path': str(selected), 'sha256': h(selected), 'individually_pinned': selected in extras}
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

contains('DirectBFS80AlignedShift', '(hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)',
         'DirectBFS80SimpleParity.graph_simple_parity p v hp0 hp1 hp2 hp3 hv hz',
         'DirectBFS80Support.graph_support_carry p v hp0 hp1 hp2 hp3 hv hz',
         'DirectBFS80Occupied.graph_occupied p v hp0 hp1 hp2 hp3 hv hz',
         "have hNN : N'=N", "exp_inj (hq'.symm.trans hq)", 'E%67=0')
contains('DirectBFS80CellShift', '(hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)',
         'DirectBFS80AlignedShift.graph_aligned_shift p v hp0 hp1 hp2 hp3 hv hz',
         'have hNNa : Na=N', "have hNN : N'=N", 'have hNNb : Nb=N',
         'E%67=0 ∧ s<N ∧ (E/67)%n=8807*s')
contains('Direct80To90SourceData', '(hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)',
         '∃ r eta zeta gamma h s : V, 0 < r ∧ 0 < eta ∧ 0 < zeta ∧ 0 < gamma ∧ 0 < s',
         'rankNat p v=2*r+1', 'C=K*Y p v+eta ∧ K=eta+zeta',
         '∀ t0 T n : V, 0 < t0 → 0 < T → 0 < n →',
         '((FreeJDirectMainGraph.graph (integerPorts p)).first).evalRing',
         '((FreeJDirectMainGraph.graph (integerPorts p)).main).evalRing',
         'graph_fresh_first_coordinate p v hp0 hp2 hp3 hv hz')
for key,row in imports.items():
    if key.endswith(':Direct80FreshFirstCoordinate'):
        need(row['path']=='/tmp/tenpositive-80freshfirstcoordinate-v0hdfs98/Direct80FreshFirstCoordinate.olean' and
             row['sha256']=='a3a1cc1e97e3d59ecf0be7481ed1762e411e8a800349244827066897dc514d19','corrected first coordinate provider')
    if key.endswith(':DirectBFS80Occupied'):
        need(row['sha256']=='9f01077536671ab1bf8bac92d7731276a8f3e094ffd42223742589d3d9edd2c2','occupied provider')
missing=[key for key,row in imports.items() if not row['individually_pinned']]
need(missing==['DirectBFS80CellShift:DiophantineConsistency.SymbolicKBandDraft'], 'unexpected unpinned imports')

print(json.dumps({'status':'PASS', 'modules':out, 'imports':imports, 'resource_samples':sample_count,
                  'historical_receipts':history, 'scope':'selected receipts and direct imports; no Lean replay or full ancestry'}, indent=2, sort_keys=True))
