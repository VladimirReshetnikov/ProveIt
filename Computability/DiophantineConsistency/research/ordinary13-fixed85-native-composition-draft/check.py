from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-fixed85-native-composition-draft')
expected=(D/'manifest.json').read_bytes()
actual=subprocess.check_output([sys.executable,'-I','-S','-B',str(D/'scan.py')])
assert actual==expected,'local lexical import inventory changed'
m=json.loads(expected);modules=m['local_modules'];order=m['dependency_first_order']
assert len(order)==len(modules)==len(set(order)) and len(m['external_frontier'])>0
position={n:i for i,n in enumerate(order)}
for n,record in modules.items():
    for dep in record['imports']:
        if dep in position:assert position[dep]<position[n],(n,dep)
for n in ['Fixed85Endpoint','Unscale84OutputBridge','Unscale84CompactChain',
 'Positive83GammaCalibration','Positive83CrossRoot','Positive84ClosedCuts',
 'Positive84RankWindow','Positive84EarlyExact','Positive84StrongAux','Positive83To84Bridge']:
 assert n in modules,n
root=(D/'Fixed85Endpoint.lean.src').read_text()
for t in ['Unscale84OutputBridgeDraft.fixed_native85','Positive83CrossRootDraft.crossRootCut',
 'Positive83To84BridgeDraft.gammaCut_of_calibration','Positive83GammaCalibrationDraft.calibrationCut',
 'Positive84ClosedCutsDraft.divCut','Unscale84CompactChainDraft.fixedK',
 '#print axioms DiophantineConsistency.Fixed85EndpointDraft.native85']:assert t in root,t
s=lambda n:Path(modules[n]['path']).read_text()
assert 'theorem output_eq' in s('Unscale84OutputBridge') and 'theorem fixed_native85' in s('Unscale84OutputBridge')
assert 'def fixedK : ℕ := paramKernel rho' in s('Unscale84CompactChain')
assert 'theorem fixed88Bridge' in s('Unscale84CompactChain')
assert 'theorem crossRootCut' in s('Positive83CrossRoot')
assert 'theorem calibrationCut' in s('Positive83GammaCalibration')
assert 'theorem divCut' in s('Positive84ClosedCuts')
g=json.loads(Path('research/ordinary13-qcube-unscale84/candidate.json').read_text())
a=s('PositiveUnscale84Graph');b=s('PositiveUnscaled84Graph')
for text in (a,b):
 for i,n in enumerate(g['witnesses']):assert f'  let {n} : Expr (Fin 13) := .var {i}\n' in text
 for i,n in enumerate(g['fixed_numerals']):assert f'  let {n} : Expr (Fin 13) := .constant (p {i})\n' in text
 for n,op,x,y in g['source']:assert f'  let {n} := {x} {op} {y}\n' in text
assert '⟨A0,A1,Fa,g72,Z,Bt,ell,k,out⟩' in a
assert '⟨A0,A1,Fa,g72,out⟩' in b
print(json.dumps({'manifest_sha256':sha256(expected).hexdigest(),
 'root_sha256':sha256(root.encode()).hexdigest(),
 'local_modules':len(modules),'external_frontier_modules':len(m['external_frontier']),
 'local_lexical_cycles':0,'same_84_literal_rows_checked':len(g['source']),
 'lean_executed':False,'status':'Unelaborated source composition; external frontier, selected compiled providers, axioms, semantic graph and PDF linkage remain open.'},sort_keys=True,indent=2))
