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
 ('direct-bfs-lean-model-mass-prototype','DirectBFSModelMass','directbfsmodelmass-attempt02','99278f25964e0c2a8c452572978d02759b2d6b73b5c798d53d569c47af044f9a'),
 ('ten-positive-80-fresh-main-offset-prototype','Direct80FreshMainOffset','fixeddigits-attempt01','bd6a09e5eb499bf1865f6e42d2f9c922d2e2553f00c0070b33780ef5269b6c0a'),
 ('ten-positive-fresh-main-algebra-prototype','FreshMainAlgebra','fixeddigits-attempt01','f465e1f3a2d5e0e043ddbb88182f111a98fb16aa8a737443f4837c6c0e8da25d'),
 ('ten-positive-90-main-recipe-prototype','Direct90MainRecipe','fixeddigits-attempt04','36b8663f8825c586f22866d5e229dd967fbb83068affad692c52c7c09fa1589c'),
 ('ten-positive-90-main-factor-prototype','Direct90MainFactor','fixeddigits-attempt01','69f6f194139766f513bc004875ec32598fa2dc04f77d3ca6f955b23aff0d2a48'),
 ('ten-positive-80-to-90-main-prototype','Direct80To90Main','fixeddigits-attempt07','0fb2a54c094a68216abe4b043e32593804c401544301e82445f79b58d8ff00bb'),
 ('ten-positive-80-to-90-main-flexible-prototype','Direct80To90MainFlexible','fixeddigits-attempt01','43a362a3b443e3590b61bd35e490afebdd6e9fd3141d5704b263d49a25eaab60'),
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
        log = (archived / 'stdout').read_text() + (archived / 'stderr').read_text()
        history[str(path.relative_to(D))] = {'terminal': h(path), 'exit': old['exit'], 'reason': old['reason'],
                                              'object': old['object_sha256'],
                                              'diagnostics': bool(re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:', log)),
                                              'sorryAx': 'sorryAx' in log}

for key, row in imports.items():
    name = key.split(':', 1)[1]
    if name in out:
        need(row['sha256'] == out[name]['object'], 'cross-producer mismatch ' + key)

def contains(module, *fragments):
    entry = next(x for x in E if x[1] == module)
    src = (B / entry[0] / (module + '.lean')).read_text()
    need(all(x in src for x in fragments), 'scope/witness ' + module)

contains('DirectBFSModelMass', 'DirectBFSSymbolicKernel.row i', 'DirectBFSCoefficientMass.selectorMass',
         'theorem natural_mass', 'DirectBFSCoefficientMass.stencilMass', 'theorem stencil_below_half', 'theorem family_mass_b1')
contains('Direct80FreshMainOffset', 'graph_fresh_projection p v hp0 hp2 hp3 hv hz',
         'K=rankNat p v+1+(Y0*(q p v*q p v))*h', 'residue_quotients (r+1) B (2*P) hdiv',
         'xcoord (2*r+1) a=X0+a*C+(4*a+3)*gamma')
contains('FreshMainAlgebra', 'hoff : K=rank+1+U*h', 'hroot : d=X+a*C+(4*a+3)*gamma',
         'hnorm : d*d=1+(a*a+(4*a+3))*C*C', '(U*(X+a*C)+(4*a+3)*(U*(gamma+h)-(K-rank-1)))')
contains('Direct90MainRecipe', '((FreeJDirectMainGraph.graph p).main).evalRing v', 'let K := v 8+v 9',
         'let z := U*(X+a*C)+H*(U*(v 11)-(K-rank-1))', 'z*z-U*U*(1+(H+a*a)*(C*C))')
contains('Direct90MainFactor', 'hdirect : v 11=gamma+h', 'main_recipe',
         'residual_zero _ _ _ _ _ _ gamma h d hoff hroot hnorm')
contains('Direct80To90Main', '![v 0,v 1,v 2,1,1,v 5,v 6,1,eta,zeta,1,direct]',
         '(hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)',
         '(hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)',
         '∃ eta zeta gamma h : V, 0 < eta ∧ 0 < zeta ∧ 0 < gamma',
         '(∀j,0<valuation v eta zeta (gamma+h) j)',
         '((FreeJDirectMainGraph.graph (integerPorts p)).main).evalRing',
         'graph_fresh_main_offset p v hp0 hp2 hp3 hv hz',
         '(graph_natural_rank p v hb hv hz).1',
         'TenPositive90MainFactor.main_zero')
contains('Direct80To90MainFlexible', '![v 0,v 1,v 2,t,T,v 5,v 6,s,eta,zeta,n,direct]',
         '(hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)',
         '∃ eta zeta gamma h : V, 0 < eta ∧ 0 < zeta ∧ 0 < gamma',
         '∀ t T n s : V, 0 < t → 0 < T → 0 < n → 0 < s →',
         '(∀j,0<valuation v eta zeta (gamma+h) t T n s j)',
         '((FreeJDirectMainGraph.graph (integerPorts p)).main).evalRing',
         'graph_fresh_main_offset p v hp0 hp2 hp3 hv hz', 'TenPositive90MainFactor.main_zero')
for key,row in imports.items():
    if key.endswith(':DirectBFSCoefficientMass'):
        need(row['sha256']=='0e7ef845800ed71d77dd080dea7f841431cbff37224e46dfa3e8f84024312d9f', 'prior mass provider')
    if key.endswith(':Direct80FreshProjection'):
        need(row['sha256']=='c9cc80175e2705b9aa49d6c9a7a6b15d092a7755120852c911e60d98b7d073d6', 'prior fresh projection provider')
missing = [key for key,row in imports.items() if not row['individually_pinned']]
need(missing == ['Direct80FreshMainOffset:DiophantineConsistency.ArithmeticPellCongruences'], 'unexpected unpinned imports')

print(json.dumps({'status':'PASS', 'modules':out, 'imports':imports, 'resource_samples':sample_count,
                  'historical_receipts':history, 'scope':'selected receipts and direct imports; no Lean replay or full ancestry'}, indent=2, sort_keys=True))
