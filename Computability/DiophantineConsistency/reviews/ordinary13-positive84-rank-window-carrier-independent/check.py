from pathlib import Path
import hashlib,json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-positive84-rank-window-carrier-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-positive84-rank-window-model-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(P/'check.py')])==(P/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-qcube-unscale84/candidate.json').read_text());rows={r[0]:r[1:] for r in g['source']}
needed={'qm':['*','J','beta'],'q':['+',1,'qm'],'qF':['-','q','F'],'C':['-','qF','alpha'],'g25':['*','K0','q'],'g26':['+','X','g25'],'g27':['*','C','g26'],'g28':['*','F','q'],'Bt':['-','g27','g28'],'g44':['*','qF','qm'],'G':['+','alpha','g44'],'g46':['-','q2',1],'g47':['*','G','g46'],'g48':['*','MF','q'],'g49':['+','MC','g48'],'g50':['*','J','g49'],'R':['+','g47','g50']}
for k,v in needed.items():assert rows[k]==v,(k,rows[k],v)
source=(P/'Positive84RankWindow.lean.src').read_text()
for v in ['PositiveCarrierDataDraft.P_positive','(Unscale84ReverseGraphDraft.k v) (v 8)', 'Unscale84ReverseGraphDraft.source_root p v', 'PositiveUnscale84To87Draft.squares_zero','P72Root.ι_tsub hF','P72Root.ι_tsub hq2','(p 3:V)=(CompactFixedBeta.betaNat:V)+(CompactSymbolicPorts.highNat:V)', 'Residue90CompactPortBoundsDraft.compact_rank_window', 'Positive84EarlyExactDraft.exactPowerGraphCut_of_window_and_main K (rankWindowGraphCut K) hm']:
 assert v in source,v
pos=Path('research/ordinary13-positive81-carrier-data-model-draft/PositiveCarrierData.lean.src').read_text()
for v in ['theorem P_positive (b ell k r : V) (P z : DiffRing V) (hb : 0<b) (hk : 2≤k)','(hz : z=ι b*(ι ell+ι k+ι r-ι k*P)-P)','(hnorm : z*z=ι b*ι b*(1+ι ell*(ι ell+ι k)))']:
 assert v in pos,v
rank=Path('research/ordinary13-positive84-power-model-draft/Positive84Power.lean.src').read_text()
assert '((p 2:V)+q84 p v*(p 3:V))*v 0' in rank
ports=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean').read_text()
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports
compact=Path('research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src').read_text()
for v in ['CompactSymbolicPorts.ports CompactFixedBeta.betaNat K','let MF : V := (CompactFixedBeta.betaNat:V)+(CompactSymbolicPorts.highNat:V)','(hgap : F+alpha<q)']:
 assert v in compact,v
early=Path('research/ordinary13-positive84-early-exact-model-draft/Positive84EarlyExact.lean.src').read_text()
for v in ['def RankWindowGraphCut','26≤rank84 (ports K) v','rank_congruence_of_main (ports K) v hv (hm V v hv hz)']:
 assert v in early,v
# Free-ring identity for the carrier: (q-F-alpha)*(X+K*q)-F*q.
# This enumerates its source expression tree, independent of numeric tests.
assert rows['qF']==['-','q','F'] and rows['C']==['-','qF','alpha']
assert rows['Bt']==['-','g27','g28']
print(json.dumps({'actual_first_carrier_and_rank_rows_checked':True,'positive_carrier_theorem_exact_inputs_checked':True,'compact_fourth_port_shifted_once':True,'window_and_main_congruence_requirements_distinguished':True,'author_receipt_reproduced':True,'lean_executed':False,'scope':'Unelaborated source and interface review; main/strong/aux cut, providers, endpoint and PDF remain open.'},sort_keys=True,indent=2))
