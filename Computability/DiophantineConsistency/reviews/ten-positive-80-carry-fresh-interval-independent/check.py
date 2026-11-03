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
 ('ten-positive-80-support-carry-prototype','Direct80SupportCarry','supportcarry-attempt01','c8e314ab5283e4f35b70f0fa23b9da8330dd7f61b316cd07e900dee81fc7d84b'),
 ('ten-positive-80-fresh-auxiliary-prototype','Direct80FreshAuxiliary','fixeddigits-attempt02','1963be154ec18fbb06522368b2ded194ba92367b148234dcd0d0d80e86268d2b'),
 ('ten-positive-80-half-binomial-prototype','Direct80HalfBinomial','halfbinomial-attempt01','8a969528c4af6398d25a5c9c788419ef619e7340069af1cfc3788404aca09d1a'),
 ('ten-positive-80-simple-parity-prototype','Direct80SimpleParity','simpleparity-attempt02','99c45b4896b28b363c07d937871ce6565c83d74ceac64989b8c508e3972ed649'),
 ('ten-positive-80-clean-carry-prototype','Direct80CleanCarry','cleancarry-attempt01','a82f62ecf6223bd8ce53493b6baaf61b2987ea2d3639cca0e49ef4ef33528031'),
 ('ten-positive-80-fresh-interval-prototype','Direct80FreshInterval','fixeddigits-attempt01','59ecea033c6f2c25ad35bb5adb1626c76d5f6acd2ba0b02b373db16c0fc44ed8'),
 ('ten-positive-pell-sandwich-floor-prototype','PellSandwichFloor','fixeddigits-attempt04','3e284051d05f4419d2efc4b5fd60cdec05abddab92786fc2a6b0e50fecbc71c9'),
 ('ten-positive-80-occupied-anchor-prototype','Direct80OccupiedAnchor','occupiedanchor-attempt02','b6693e7c031b26a67328593f2c604e41b0f5fa8a996e040a911e48f07a0dd0e4'),
 ('ten-positive-80-fresh-first-main-prototype','Direct80FreshFirstMain','fixeddigits-attempt01','3c8be3dd6d55789314efba6206e1a456f00e49b98dfbe91f564509ff7c9ccebd'),
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

contains('Direct80SupportCarry', 'Direct80IndexedCarry.graph_indexed_carry p v hp0 hp1 hp2 hp3 hv hz',
         'Direct80FixedSlots.graph_fixed_slots p v hp0 hp2 hp3 hv hz', "have hNN : N'=N", 'exp_inj (hq\'.symm.trans hq)',
         'v 5=Exp.exp (rankNat p v-(67*8807)*N)', 'CleanModelSupport.zero_outside', 'CleanModelSupport.boolean_away_special')
contains('Direct80SimpleParity', 'Direct80SupportCarry.graph_support_carry p v hp0 hp1 hp2 hp3 hv hz',
         "have hNN : N'=N", 'exp_inj (hq\'.symm.trans hq)', 'ParityColumns.at2195', 'ParityColumns.at3296')
contains('Direct80CleanCarry', 'Direct80SupportCarry.graph_support_carry p v hp0 hp1 hp2 hp3 hv hz',
         '(t=4393 ∨ t=5495)', 'TemporalSafeCyclic.safe', 'TemporalCarryExact.clean_exact')
contains('Direct80FreshAuxiliary', 'let a := Y p v*(X p v+1)', 'let c := ycoord R a',
         'auxiliary_seed (Y p v*(X p v+1)) (rankNat p v)', 'graph_phase p v hp0 hp2 hp3 hv hz')
contains('Direct80HalfBinomial', 'TenPositive80SandwichBoth.graph_sandwich_both p v hbeta31 hl hh hv hz hbetaodd',
         'ScaledPellRounding.extract (X p v) (Y p v) r (v 8) (v 9)', 'rankNat p v=2*r+1')
contains('PellSandwichFloor', 'theorem split_floor', '∃ v, v<power X r', 'theorem transfer_floor', 'K*Y<C ∧ C<K*(Y+1)')
contains('Direct80FreshInterval', 'TenPositive80SandwichBoth', 'graph_sandwich_both p v h31 hl hh hv hz hodd',
         'split_floor (X p v) (Y p v) r (v 8) (v 9) (k v) (c p v)', 'transfer_floor (Y p v)',
         'ycoord (2*r+1) (Y p v*(X p v+1))')
contains('Direct80OccupiedAnchor', 'Direct80CleanCarry.graph_clean_carry p v hp0 hp1 hp2 hp3 hv hz',
         'Direct80SupportCarry.graph_support_carry p v hp0 hp1 hp2 hp3 hv hz',
         "have eq1 : N'=N", "have eq2 : N''=N", '34≤j.val → dig 67 (Cnat p v) (position j:V)=1')
contains('Direct80FreshFirstMain', 'graph_fresh_interval p v hp0 hp2 hp3 hv hz',
         'C=K*Y0+eta ∧ K=eta+zeta', 'let C:=ycoord (2*r+1) (Y0*(X0+1))',
         '0 < eta ∧ 0 < zeta')

print(json.dumps({'status':'PASS', 'modules':out, 'imports':imports, 'resource_samples':sample_count,
                  'historical_receipts':history, 'scope':'selected receipts and direct imports; no Lean replay or full ancestry'}, indent=2, sort_keys=True))
