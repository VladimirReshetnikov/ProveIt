from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-unscale84-compact-chain-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s=(D/'Unscale84CompactChain.lean.src').read_text()
for x in ['def fixedK : ℕ := paramKernel rho','theorem compact_beta','CompactFixedBeta.bounds','theorem positiveBridge87','Positive87To88BoundsDraft.bounds_cut','theorem fixed_ports','CompactSymbolicModelIff.p','theorem fixed88Bridge','P88FourSquareModel.positiveBridge','theorem native84','Unscale84EndpointDraft.native84 fixedK (positiveBridge87 fixedK fixed88Bridge)']:
 assert x in s,x
m=Path('research/ordinary13-freej88-four-square-lean-draft/P88FourSquareModel.lean').read_text()
assert 'def expression : Expr (Fin 13) := (P88FourSquare.graph CompactSymbolicModelIff.p).output' in m
assert 'theorem positiveBridge : PositiveModelBridge expression' in m
ports=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean').read_text()
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in ports
print(json.dumps({'fixed_tuple_source_signatures_checked':True,'source_chain_elaborated':False,'lean_executed':False,'axiom_reports_executed':False,'pdf_binding_proved':False},sort_keys=True,indent=2))
