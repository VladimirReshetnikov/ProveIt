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
 ('ten-positive-80-positive-transport-prototype','Direct80PositiveTransport','positive-attempt02','394c3250a885b65fcd5db7b3605fc8ba43037d059d6f9385adce1312d604718d'),
 ('direct-bfs-lean-coefficient-decoder-prototype','DirectBFSCoefficientDecoder','directbfscoeffdecoder-attempt01','97345af089b6ebc58a25f66ccd43d68f478ae4b83118fb617d97146c70385ee7'),
 ('direct-bfs-lean-raw-column-prototype','DirectBFSRawColumn','directbfsrawcolumn-attempt02','f7be7af309b5ee7dc0af23b228e6052db178349028687b5769868cb2dacfeb27'),
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
        imports[module + ':' + name] = {'path': str(selected), 'sha256': h(selected),
                                      'individually_pinned': selected in extras}
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

contains('Direct80PositiveTransport', '(hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)',
         'q p v<v 5 ∧ ∃ t : V, 0 < t ∧ 0<Cnat p v',
         '((p 1:V)+v 5)*Cnat p v=v 1+b p v*t', 'graph_natural_transport p v h31 hl hh hv hz hodd',
         'Direct80GraphPower.graph_power p v h31 hl hh hv hz hodd', 'Direct80RankThree.graph_rank_gt_three_q p v h31 hv hz')
contains('DirectBFSCoefficientDecoder', 'CompactCoefficientMass.value (DirectBFSSymbolicKernel.row i)',
         'DirectBFSDecoder.tileValue (V:=V) i', 'theorem selector_model', 'theorem finite_decomposition')
contains('DirectBFSRawColumn', 'DirectBFSCoefficientDecoder.finite_decomposition',
         '(hn : 0<n) (hk : k<n) (hC : C<Exp.exp (67*n))', 'theorem flatten', 'theorem decoder_bands',
         'DirectBFSDecoder.tileValue (V:=V) j', 'RawColumnBands.bareColumn n C k+dig 67 T k')
for key,row in imports.items():
    if key.endswith(':DirectBFSBandCarry'):
        need(row['sha256']=='e585f2a52aece195858cdfcbcbe764df2aa8984af9cbebdd018e97a7b1e51e7e', 'prior band carry provider')
    if key.endswith(':DirectBFSDecoder'):
        need(row['sha256']=='35b321fbe268eaa4ba19c844cf517168b0d256cd85f65a4e4eebac648c4b6d3e', 'prior decoder provider')
    if key.endswith(':DirectBFSCoefficientMass'):
        need(row['sha256']=='0e7ef845800ed71d77dd080dea7f841431cbff37224e46dfa3e8f84024312d9f', 'prior coefficient mass provider')
missing=[key for key,row in imports.items() if not row['individually_pinned']]
need(missing==['DirectBFSCoefficientDecoder:DiophantineConsistency.ArithmeticWindowCarry'], 'unexpected unpinned imports')

print(json.dumps({'status':'PASS', 'modules':out, 'imports':imports, 'resource_samples':sample_count,
                  'historical_receipts':history, 'scope':'selected receipts and direct imports; no Lean replay or full ancestry'}, indent=2, sort_keys=True))
