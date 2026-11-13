from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-fixed85-native-composition-source-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-fixed85-native-composition-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(P/'check.py')])==(P/'receipt.json').read_bytes()
m=json.loads((P/'manifest.json').read_text());mods=m['local_modules'];frontier=set(m['external_frontier'])
assert m['root']=='Fixed85Endpoint' and len(mods)==m['local_module_count'] and len(frontier)==m['external_frontier_count'] and not (set(mods)&frontier)
# Independent hash, lexical-edge and Kahn topological validation of the
# selected source inventory. It neither finds omitted roots nor resolves oleans.
parents={name:[] for name in mods}; degree={name:0 for name in mods}
for name,rec in mods.items():
 path=Path(rec['path']);b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==rec['sha256'],name
 imports=[]
 for line in b.decode().splitlines():
  found=re.match(r'^\s*(?:public\s+)?import\s+(.+?)\s*(?:--.*)?$',line)
  if found:imports+=found.group(1).split()
 assert imports==rec['imports'],name
 for dep in imports:
  assert dep in mods or dep in frontier,(name,dep)
  if dep in mods:degree[name]+=1;parents[dep].append(name)
ready=[n for n,d in degree.items() if d==0];count=0
while ready:
 n=ready.pop();count+=1
 for x in parents[n]:
  degree[x]-=1
  if degree[x]==0:ready.append(x)
assert count==len(mods)
def s(name):return Path(mods[name]['path']).read_text()
root=s('Fixed85Endpoint');bridge=s('Unscale84OutputBridge'); chain=s('Unscale84CompactChain')
for v in ['IPRAExpressionNative.nativeNoZero','EtaNaturalUnitGraphDraft.graph','ports Unscale84CompactChainDraft.fixedK','∼mappedNativeRefutation embedding','Positive83CrossRootDraft.crossRootCut Unscale84CompactChainDraft.fixedK','Positive83GammaCalibrationDraft.calibrationCut Unscale84CompactChainDraft.fixedK','Positive84ClosedCutsDraft.divCut Unscale84CompactChainDraft.fixedK']:
 assert v in root,v
for v in ['theorem output_eq','theorem fixed_native85','CrossRootCut Unscale84CompactChainDraft.fixedK','GammaCut Unscale84CompactChainDraft.fixedK','DivCut Unscale84CompactChainDraft.fixedK','positiveBridge87 Unscale84CompactChainDraft.fixedK']:
 assert v in bridge,v
assert 'def fixedK : ℕ := paramKernel rho' in chain
assert 'theorem fixed_ports' in chain and 'CompactSymbolicModelIff.p' in chain
assert 'theorem fixed88Bridge' in chain and 'P88FourSquareModel.positiveBridge' in chain
assert 'theorem crossRootCut (K : ℕ) : Positive81To83TransportDraft.CrossRootCut K' in s('Positive83CrossRoot')
assert 'theorem calibrationCut (K : ℕ) : Positive83To84BridgeDraft.CalibrationCut K' in s('Positive83GammaCalibration')
assert 'theorem gammaCut_of_calibration (K : ℕ) (hc : CalibrationCut K) : GammaCut K' in s('Positive83To84Bridge')
assert 'theorem divCut (K : ℕ) : DiophantineConsistency.Positive83To84BridgeDraft.DivCut K' in s('Positive84ClosedCuts')
# Confirm this endpoint selects the prior eta-natural prototype, not the
# later eta/zeta-natural probe. Exact witness, port and source rows.
g=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text());graph=s('EtaNaturalUnitGraph')
assert len(g['source'])==85
for i,n in enumerate(g['witnesses']):assert f'  let {n} : Expr (Fin 13) := .var {i}\n' in graph
for i,n in enumerate(g['fixed_numerals']):assert f'  let {n} : Expr (Fin 13) := .constant (p {i})\n' in graph
for n,op,x,y in g['source']:assert f'  let {n} := {x} {op} {y}\n' in graph,(n,op,x,y)
assert ['k','+','kbase',1] in g['source']
print(json.dumps({'all_local_hashes_and_lexical_edges_checked':len(mods),'unresolved_frontier':len(frontier),'independent_kahn_cycle_check':'no cycle in selected local lexical graph','fixed_tuple_and_three_cut_signatures_checked':True,'eta_natural_not_eta_zeta_natural_rows_checked':len(g['source']),'lean_executed':False,'scope':'No claim about omitted roots, external frontier, compiled providers, proof escapes, axioms, end-to-end proof or PDF.'},sort_keys=True,indent=2))
