#!/usr/bin/env python3
"""Bind the historical/current Lean arithmetic expression to parsed 14-variable TeX.

This is a finite external source/transcription check, not Lean elaboration, a
proof about PDF semantics, or a check of the four concrete Lean port values.
"""
import ast
import contextlib
import hashlib
import io
import json
from pathlib import Path
import re
import runpy
import subprocess
import tempfile

if not __debug__:
    raise RuntimeError('This audit requires assertions; do not run Python with -O or -OO')

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1]
ROOT = HERE.parents[3]
SNAP = Path('/tmp/ipra-aq29-fresh-source-closure-v2')
TRIAL = Path('/tmp/ipra-standard-current14-author-trial')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

expected_tex = '94f5eba440c5c74d5ab28f51f1104aae13a774ab0238ed9e46b24a4c6b2f9635'
expected_pdf = '23a52933980352f83a19c21a0d6f349594be5f85edc85a462e25ffc83c7fd5d6'
expected_syntax = '112c21a16ddb3d45b311dbe9099ea89619ff6b25f6fb61050d9a7b8f8898d2f9'
expected_old_nat = 'a202ec90e91f2ed35e0aa00394ea94a47d29b32a64704dd7f3ec2c7155c30250'
expected_new_nat = '0e0923fcc8dde83a1e8099a55e5ec8c804ff2b1648d8376b6c81ac343eac4e4f'
expected_state = 'bd643e25b07538400b7f7cc397ff64af6ddc6d73f1e563d69fb5c6aed863da61'

tex = BASE/'equation.tex'; pdf = BASE/'equation.pdf'
frozen = SNAP/'src/DiophantineConsistency/CurrentEquationSyntax2011.lean'
current = BASE/'Lean/DiophantineConsistency/CurrentEquationSyntax2011.lean'
old_nat = SNAP/'src/DiophantineConsistency/NaturalExpression.lean'
new_nat = BASE/'Lean/DiophantineConsistency/NaturalExpression.lean'
assert H(tex) == expected_tex and H(pdf) == expected_pdf
assert H(frozen) == H(current) == expected_syntax
assert H(old_nat) == expected_old_nat and H(new_nat) == expected_new_nat
assert H(TRIAL/'state.json') == expected_state
state = json.loads((TRIAL/'state.json').read_text())
assert state['status'] == 'AUTHOR_ONLY_PASS'

# The source change lies entirely inside one theorem's proof body; its
# signature and every byte outside that proof are unchanged. This is a
# syntactic source observation, not a replay of the current Lean project.
old = old_nat.read_text(); new = new_nat.read_text()
start = 'theorem eval_splitNatural '
end = 'theorem eval_eq_zero_iff_splitNatural '
assert old.count(start) == new.count(start) == old.count(end) == new.count(end) == 1
assert old[:old.index(start)] == new[:new.index(start)]
old_block = old[old.index(start):old.index(end)]
new_block = new[new.index(start):new.index(end)]
assert old_block[:old_block.index(':= by')] == new_block[:new_block.index(':= by')]
assert old[old.index(end):] == new[new.index(end):]

# Inspect the entire source-declared project import closure of the literal
# expression, not just the named top-level file. The sole observed source
# drift is the theorem-body difference above. External/package ancestry and
# Lean's runtime imports are outside this line-based source graph.
parent = json.loads((SNAP/'manifest.json').read_text())
pending = ['DiophantineConsistency.CurrentEquationSyntax2011']; closure = set()
while pending:
    name = pending.pop()
    if name in closure: continue
    closure.add(name)
    pending.extend(dep for dep in parent['sources'][name]['imports']
                   if dep in parent['sources'] and dep not in closure)
assert len(closure) == 24
changed = []
for name in sorted(closure):
    row = parent['sources'][name]
    frozen_file = SNAP/row['snapshot_path']; workspace_file = ROOT/row['workspace_path']
    assert frozen_file.is_file() and not frozen_file.is_symlink() and H(frozen_file) == row['sha256']
    assert workspace_file.is_file() and not workspace_file.is_symlink()
    if H(frozen_file) != H(workspace_file): changed.append(name)
assert changed == ['DiophantineConsistency.NaturalExpression']

with contextlib.redirect_stdout(io.StringIO()) as captured:
    existing = runpy.run_path(str(BASE/'research/adaptive-direct-ordinate86/verify_display_tex14.py'))
assert '14 positive unknowns; two mutation controls' in captured.getvalue()
candidate = existing['candidate']; dag = existing['dag']; Poly = existing['Poly']
assert candidate['witnesses'] == ['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma']
assert candidate['fixed_numerals'] == ['beta','K0','MC','MF']
assert len(candidate['source']) == 65

def evaluate(node, env):
    if isinstance(node, ast.Expression): return evaluate(node.body, env)
    if isinstance(node, ast.Name) and node.id in env: return env[node.id]
    if isinstance(node, ast.Constant) and type(node.value) is int and node.value >= 0:
        return Poly.lift(node.value)
    if isinstance(node, ast.BinOp):
        a = evaluate(node.left, env)
        if isinstance(node.op, ast.Pow):
            assert isinstance(node.right, ast.Constant) and type(node.right.value) is int and 0 <= node.right.value <= 3
            return a ** node.right.value
        b = evaluate(node.right, env)
        if isinstance(node.op, ast.Add): return a + b
        if isinstance(node.op, ast.Sub): return a - b
        if isinstance(node.op, ast.Mult): return a * b
    raise ValueError(('unsupported Lean arithmetic syntax',ast.dump(node)))

definitions = {'b':'qm','q':'q','C':'C','X':'X','Y':'Y','E':'E','k':'k',
               'ell':'ell','c':'c','a':'a','H':'H','delta':'Delta',
               'D':'main_root','rank':'R','tau':'tau','V':'V','S':'normalized_S',
               'P':'N0','Q':'N1','U':'Na','W':'Nt','Z':'scaled_Ns'}
const_names = ['beta','K0','MC','MF']

def check_lean(text):
    header = 'def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :='
    suffix = '/-- The current ports retain the full kernel and both complete masks. -/'
    assert text.count(header) == text.count(suffix) == 1
    body = text.split(header,1)[1].split(suffix,1)[0]
    tail = '\n  P * Q * U * W * Z - delta\n\n'
    assert body.endswith(tail)
    lines = body[:-len(tail)]
    pattern = re.compile(r'^  let ([A-Za-z][A-Za-z0-9_]*)(?: : Expr \(Fin 14\))? :=\s*(.*?)(?=^  let |\Z)',re.M|re.S)
    found = list(pattern.finditer(lines))
    assert ''.join(m.group(0) for m in found).strip() == lines.strip(), 'unparsed expression source'
    assert [m.group(1) for m in found] == candidate['witnesses'] + list(definitions)
    env = {}; used_ports = []
    for j,m in enumerate(found):
        name = m.group(1); rhs = ' '.join(m.group(2).split())
        if j < 14:
            assert rhs == f'.var {j}', ('coordinate',name,rhs)
            env[name] = dag[name]
            continue
        def port(match):
            i = int(match.group(1)); used_ports.append(i); return 'fixed_'+str(i)
        rhs = re.sub(r'Expr\.constant\s*\(p\s+([0-3])\)',port,rhs)
        local = dict(env, **{'fixed_'+str(i):dag[n] for i,n in enumerate(const_names)})
        value = evaluate(ast.parse(rhs.replace('^','**'),mode='eval'),local)
        assert value == dag[definitions[name]], ('factor mismatch',name)
        env[name] = value
    assert sorted(used_ports) == [0,1,2,3]
    assert 'def expression : Expr (Fin 14) := expressionAt CurrentWindowCarry2011.ports' in text
    assert 'def naturalExpression : Expr (Fin 14) := positiveShift expression' in text
    assert 'e.subst (fun i => Expr.var i + Expr.constant 1)' in text
    return len(found)-14

lean = frozen.read_text(); assert check_lean(lean) == len(definitions)
for old_text,new_text in [('let C := q - F - alpha','let C := q + F - alpha'),
                          ('  P * Q * U * W * Z - delta','  P * Q * U * W * Z + delta'),
                          ('let z : Expr (Fin 14) := .var 3','let z : Expr (Fin 14) := .var 4')]:
    assert old_text in lean
    try: check_lean(lean.replace(old_text,new_text,1))
    except (AssertionError, ValueError): continue
    raise AssertionError(('Lean source mutation accepted',old_text))

nozero = TRIAL/'src/DiophantineConsistency/IPRACurrentNativeZFC.lean'
std = TRIAL/'src/DiophantineConsistency/IPRAStandardCurrentEndpoint.lean'
records = {x['module']:x for x in state['rows']}
for name, path in [('IPRACurrentNativeZFC',nozero),('IPRAStandardCurrentEndpoint',std)]:
    row = records['DiophantineConsistency.'+name]
    assert row['exit'] == 0 and H(path) == row['source_sha256']
sentence = nozero.read_text()
assert 'naturalExpression.splitNatural.1' in sentence and 'naturalExpression.splitNatural.2' in sentence
assert 'def noZero14 : Sentenceᵢ language := ∀⁰* (∼' in sentence
assert '(provable_iff _).2 equivalence14' in std.read_text()

# Reproduce the committed PDF from the exact current TeX with the installed
# TeX toolchain. This is byte reproduction, not a general PDF semantics proof.
with tempfile.TemporaryDirectory(prefix='equation14-render-binding-') as temp:
    proc = subprocess.run(['pdflatex','-halt-on-error','-interaction=batchmode',
                           '-output-directory',temp,'equation.tex'],cwd=BASE,
                          text=True,capture_output=True,timeout=120)
    assert proc.returncode == 0, (proc.stdout,proc.stderr)
    assert H(Path(temp)/'equation.pdf') == expected_pdf
    log=(Path(temp)/'equation.log').read_text(errors='replace')
    assert 'Overfull \\hbox' not in log and 'Overfull \\vbox' not in log

result = {'status':'PASS_FINITE_HISTORICAL_EXPRESSION_BINDING',
          'tex_sha256':H(tex),'pdf_sha256':H(pdf),'historical_lean_expression_sha256':H(frozen),
          'historical_natural_expression_sha256':H(old_nat),'current_natural_expression_sha256':H(new_nat),
          'trial_state_sha256':H(TRIAL/'state.json'),'unshifted_variables':14,
          'symbolic_ports':['beta','K0','MC','MF'],'checked_lean_abbreviations':len(definitions),
          'declared_project_import_closure':len(closure),'changed_project_sources':changed,
          'tex_candidate_gate_count':65,'source_mutation_controls':3,
          'scope':'Finite parsed arithmetic source-to-TeX comparison and byte-reproduced PDF. Concrete ports are symbolic here; this is not a Lean proof of TeX interpretation, a direct evaluation of the Lean fixed ports, or a paired/current-source endpoint replay.'}
output = HERE/'expression-receipt.json'; assert not output.exists(); output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(result['status'],H(output))
