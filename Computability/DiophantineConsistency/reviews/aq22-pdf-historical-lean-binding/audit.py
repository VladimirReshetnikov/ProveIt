#!/usr/bin/env python3
"""Finite historical AQ22 Lean/circuit/recorded-port binding audit."""
import gzip
import hashlib
import json
import re
import sys
from collections import deque
from pathlib import Path

if not __debug__:
    raise RuntimeError('optimized Python is unsupported')
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REV = ROOT / 'reviews'
TASK = ROOT / 'research/adaptive-square-sums22-degree10'
AUTH = REV / 'ipra-aq22-guarded-author'
OLD = REV / 'equation10-22-independent-audit'
REFRESH = REV / 'equation10-22-wording-independent-audit'
PORT = REV / 'equation14-historical-literal-binding'
PORT_REVIEW = REV / 'equation14-historical-literal-binding-independent'
PARENT = Path('/tmp/ipra-aq29-fresh-project-pair/author/state.json')
SNAP = Path('/tmp/ipra-aq29-fresh-source-closure-v2/src/DiophantineConsistency')
COEFF = ROOT / 'candidates/one-page-padding-staircase-carrier65-2011'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
J = lambda p: json.loads(Path(p).read_text())
raw = lambda b: hashlib.sha256(b).hexdigest()
def recorded_hash(table, path):
    suffix='/' + str(path.relative_to(ROOT))
    matches=[value for name,value in table.items() if name.endswith(suffix)]
    assert len(matches)==1
    return matches[0]

literal = AUTH / 'src/DiophantineConsistency/AdaptiveAQ22Literal.lean'
endpoint = AUTH / 'src/DiophantineConsistency/IPRAStandardAQ22.lean'
graph = TASK / 'candidate.json'
tex = TASK / 'equation10-22.tex'
pdf = TASK / 'equation10-22.pdf'
files = [Path(__file__).resolve(), literal, endpoint, graph, tex, pdf, ROOT/'equation.tex',
         AUTH/'state.json', AUTH/'terminal-exit.json',
         REV/'ipra-aq22-guarded-author-independent-audit/receipt.json',
         REV/'ipra-aq22-guarded-author-independent-audit/terminal-observation.json',
         OLD/'receipt.json', REFRESH/'receipt.json', REFRESH/'terminal-observation.json',
         PORT/'ports-receipt.json', PORT/'printed-constants-repeat.json',
         PORT_REVIEW/'receipt.json', PORT_REVIEW/'terminal-observation.json',
         COEFF/'polynomial.json', PARENT, SNAP/'AdaptiveEquationSyntax2011.lean',
         SNAP/'IPRAExpressionNative.lean']
carrier = J(COEFF/'polynomial.json')
files += [PORT/'port-outputs'/f'port{i}.txt.gz' for i in range(4)]
files += [COEFF/'coefficients'/carrier['coefficient_binding']['ports'][n]['file']
          for n in carrier['fixed_numerals']]
before = {str(p.resolve()): H(p) for p in files}

assert H(graph) == '1266b143c5512351739ea2c71fc8e0b8b0e5cecc599392f128c0803ff78ce106'
c = J(graph)
assert len(c['witnesses']) == len(set(c['witnesses'])) == 22
assert c['fixed_numerals'] == ['beta','K0','MC','MF'] == carrier['fixed_numerals']
assert len(c['source']) == 114
def check_literal(s):
    signature = 'def literal (p : Fin 4 → ℤ) : Expr (Fin 22) :=\n'
    assert s.count(signature) == 1
    body = s.split(signature,1)[1].split('\nend DiophantineConsistency.AdaptiveAQ22Literal',1)[0]
    expected = [f'  let {name} : Expr (Fin 22) := .var {i}' for i,name in enumerate(c['witnesses'])]
    expected += [f'  let {name} : Expr (Fin 22) := .constant (p {i})' for i,name in enumerate(c['fixed_numerals'])]
    expected += [f'  let {target} := {left} {op} {right}' for target,op,left,right in c['source']]
    expected += [f"  {c['output']}"]
    assert body.splitlines() == expected
check_literal(literal.read_text())
src = literal.read_text()
mutations = [
 ('variable_index', src.replace('.var 0', '.var 1',1)),
 ('port_index', src.replace('.constant (p 0)', '.constant (p 1)',1)),
 ('gate_operation', src.replace('let qm := J * beta', 'let qm := J + beta',1)),
 ('gate_operand', src.replace('let qm := J * beta', 'let qm := F * beta',1)),
 ('gate_target', src.replace('let qm := J * beta', 'let qmWrong := J * beta',1)),
 ('output', src.replace('  addDELTAConstraint\nend ', '  addVConstraint\nend ',1)),
]
for label, mutated in mutations:
    assert mutated != src
    try: check_literal(mutated)
    except AssertionError: pass
    else: raise AssertionError(('literal mutation survived',label))

# Link the checked sources to recorded author rows and the selected endpoint.
state = J(AUTH/'state.json'); parent = J(PARENT)
assert H(PARENT) == state['parent_state_sha256'] == 'b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153'
assert state['status'] == 'AUTHOR_ONLY_PASS' and len(state['rows']) == 37
assert parent['status'] == 'PASS' and len(parent['records']) == 1210
rows = {r['module']: r for r in parent['records']}
rows.update({r['module']:r for r in state['rows']})
for name in ('AdaptiveEquationSyntax2011', 'IPRAExpressionNative'):
    assert rows['DiophantineConsistency.'+name]['source_sha256'] == H(SNAP/(name+'.lean'))
assert ('def positiveShift {σ : Type*} (e : Expr σ) : Expr σ :=\n'
        '  e.subst (fun i => Expr.var i + Expr.constant 1)') in (SNAP/'AdaptiveEquationSyntax2011.lean').read_text()
assert 'def nativeNoZero {n : ℕ} (e : Expr (Fin n)) : Sentenceᵢ language := ∀⁰* (∼' in (SNAP/'IPRAExpressionNative.lean').read_text()
for p,name in [(literal,'AdaptiveAQ22Literal'),(endpoint,'IPRAStandardAQ22')]:
    row = rows['DiophantineConsistency.'+name]
    assert row['exit'] == 0 and row['source_sha256'] == H(p)
ep = endpoint.read_text()
assert ep.count('positiveShift (AdaptiveAQ22Literal.literal CurrentWindowCarry2011.ports)') == 2
assert 'theorem literal_iff_translated_consistency : standardTheory ⊢' in ep
assert '(Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ' in ep
assert J(AUTH/'terminal-exit.json')['returncode'] == 0
artifact=REV/'ipra-aq22-guarded-author-independent-audit'
artifact_receipt=J(artifact/'receipt.json')
assert artifact_receipt['status']=='PASS_INDEPENDENT_AQ22_AUTHOR_ARTIFACT_AUDIT'
assert artifact_receipt['trial_state_sha256']==H(AUTH/'state.json')
assert artifact_receipt['parent_state_sha256']==H(PARENT)
assert J(artifact/'terminal-observation.json')['observed_exit_code'] == 0

# Follow recorded project-import object hashes to both the literal and fixed
# port provider. This is recorded direct ancestry, not a dynamic load trace.
def recorded_path(target):
    start='DiophantineConsistency.IPRAStandardAQ22'; q=deque([[start]]); seen=set()
    while q:
        path=q.popleft(); n=path[-1]
        if n in seen: continue
        seen.add(n)
        if n == target: return path
        row=rows[n]; assert row['exit'] == 0
        for dep,info in row.get('imports',row.get('direct_inputs',{})).items():
            if dep in rows and dep not in seen:
                assert info['sha256'] == rows[dep]['object_sha256']
                q.append(path+[dep])
    raise AssertionError(('no recorded path',target))
literal_path=recorded_path('DiophantineConsistency.AdaptiveAQ22Literal')
port_path=recorded_path('DiophantineConsistency.CurrentKernelData2011')
kernel=rows['DiophantineConsistency.CurrentKernelData2011']
guard=next(v for k,v in state['overlay_guards'].items() if k.endswith('/CurrentKernelData2011.olean'))
assert guard['sha256'] == kernel['object_sha256'] == '95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896'

# Connect the separately audited exact graph-to-print and refresh checks.
old=J(OLD/'receipt.json'); refresh=J(REFRESH/'receipt.json')
assert H(OLD/'receipt.json') == '9d1bedacd8f643952a9ba95e972006e7275652d9d222539655d036d16c0c4664'
assert old['status'] == 'PASS_INDEPENDENT_AQ22_DISPLAY'
assert refresh['status'] == 'PASS_AQ22_WORDING_AUDIT'
assert recorded_hash(old['inputs_sha256'],graph) == H(graph)
assert refresh['candidate_sha256'] == H(graph)
for p in (tex,pdf,graph,ROOT/'equation.tex'):
    assert recorded_hash(refresh['inputs_sha256'],p) == H(p)
assert J(REFRESH/'terminal-observation.json')['ordinary_python_exit_code'] == 0
assert old['printed_gates'] == 114 and old['unknowns'] == 22 and old['fixed_ports'] == 4
begin=r'\textbf{The four fixed integers.}'; end=r'\endgroup'
def block(s):
    i=s.index(begin); return s[i:s.index(end,s.index(r'\textbf{The integer $\mathcal A$',i))+len(end)]
assert block(tex.read_text()) == block((ROOT/'equation.tex').read_text())
assert raw(block(tex.read_text()).encode()) == 'e5e7b58b54e57badc97ba6ee7f7577ec8e858c88189474723ce28ae629b0a6c6'

# Recompare captured full #eval output bytes to coefficient files and the
# independently rerun manually transcribed printed-constant reconstruction.
prior=J(PORT_REVIEW/'receipt.json'); terminal=J(PORT_REVIEW/'terminal-observation.json')
assert prior['status']=='PASS_INDEPENDENT_FINITE_BINDING_REVIEW'
assert prior['fresh_probe_exit']==prior['fresh_probe_deps_exit']==prior['recipe_rerun_exit']==0
assert terminal['observed_exit_code']==0
assert prior['input_sha256'][str(PARENT.resolve())] == H(PARENT)
assert recorded_hash(prior['input_sha256'],PORT/'printed-constants-repeat.json') == H(PORT/'printed-constants-repeat.json')
probe=J(PORT/'ports-receipt.json'); printed=J(PORT/'printed-constants-repeat.json')
assert probe['parent_state_sha256']==H(PARENT) and probe['kernel_data_object_sha256']==guard['sha256']
assert printed['result']=='PASS' and printed['constant_block_sha256']=='e5e7b58b54e57badc97ba6ee7f7577ec8e858c88189474723ce28ae629b0a6c6'
assert printed['tile_rows']==942 and printed['rank_comparisons']==885481
ports=[]
def check_port(dec, binary, expected_hash):
    assert dec == str(int.from_bytes(binary,'big')).encode('ascii')
    assert raw(binary) == expected_hash
for i,(name,display) in enumerate(zip(c['fixed_numerals'],['beta','K','MC','MF_source'])):
    meta=carrier['coefficient_binding']['ports'][name]
    packed=(COEFF/'coefficients'/meta['file']).read_bytes()
    assert raw(packed)==meta['gzip_sha256']
    binary=gzip.decompress(packed)
    assert len(binary)==meta['raw_bytes'] and raw(binary)==meta['raw_sha256']
    dec=gzip.decompress((PORT/'port-outputs'/f'port{i}.txt.gz').read_bytes())
    check_port(dec, binary, meta['raw_sha256'])
    assert raw(binary) == printed['fixed_port_records'][display]['sha256'] == probe['ports'][i]['integer_sha256'] == prior['ports'][i]['integer_sha256']
    assert raw(dec) == probe['ports'][i]['decimal_sha256'] == prior['ports'][i]['decimal_sha256']
    ports.append({'index':i,'name':name,'decimal_sha256':raw(dec),'integer_sha256':raw(binary),'decimal_digits':len(dec)})
    changed=bytes([dec[0] ^ 1])+dec[1:]
    try: check_port(changed, binary, meta['raw_sha256'])
    except AssertionError: pass
    else: raise AssertionError(('decimal port mutation survived',i))
assert {str(p.resolve()):H(p) for p in files} == before
result={'status':'PASS_AQ22_HISTORICAL_FINITE_BINDING','inputs_sha256':before,
        'variables':22,'fixed_ports':ports,'gates':114,
        'literal_mutations_rejected':[x[0] for x in mutations],
        'port_decimal_mutations_rejected':4,
        'literal_recorded_import_path':literal_path,'port_recorded_import_path':port_path,
        'historical_author_parent_sha256':H(PARENT),'pdf_sha256':H(pdf),
        'scope':'Finite source/graph/display binding and recorded #eval comparisons; no Lean semantics of TeX, no new Lean endpoint replay, and no matched peer replay. Printed decoder/table/rank recipe is manually transcribed.'}
out=HERE/'receipt.json'
assert not out.exists()
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(result['status'],H(out),H(pdf))
