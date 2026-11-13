from pathlib import Path
import hashlib,json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-eta-zeta-zero-graph-obstruction-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-eta-zeta-zero-graph-obstruction-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(P/'check.py')])==(P/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text());r={row[0]:row[1:] for row in g['source']}
required={'qm':['*','n_J','beta'],'q':['+',1,'qm'],'X':['*','q','n_w'],'F':['+','n_F',1],'alpha':['+','n_alpha',1],'s':['+','n_s',1],'Y':['*','q3','s'],'U':['*','Y','q2'],'kbase':['+','n_eta','n_zeta'],'kY':['*','Y','kbase'],'c':['+','n_eta','kY'],'C':['-','qF','alpha'],'g26':['+','X','K0'],'g27':['*','C','g26'],'Bt':['-','g27','F'],'g32':['*','qm','folded_g31'],'Z':['-','g32','Bt'],'r0base':['-','kbase','R'],'r0':['-','r0base',1],'g54':['*','U','n_gamma'],'shift':['-','g54','r0'],'a':['+','E','Y'],'E':['*','X','Y'],'H':['+',3,'g15'],'g15':['*',4,'a'],'g19':['*','a','c'],'b0':['+','X','g19'],'Dstar':['+','g58','g59'],'g58':['*','U','b0'],'g59':['*','H','shift'],'A1':['-','g61','g65'],'g63':['*','Delta','c2']}
for n,row in required.items():assert r[n]==row,(n,r[n],row)
s=(P/'EtaZetaZeroGraphObstruction.lean.src').read_text();j=(P/'EtaZetaNaturalJPositive.lean.src').read_text()
for x in ['(p : Fin 4 → ℕ)','(hbeta : 0<(p 0:V)) (heta : v 9=0) (hzeta : v 10=0)','EtaZetaNaturalJPositiveDraft.J_positive p v hz','EtaZetaNaturalUnitBridgeDraft.signed_norms pp v hz','ZeroOrdinateMainObstructionDraft.zero_ordinate_impossible','(q p v) (Y p v) (q p v*v 6) (v 6) z (shift p v) hq hY rfl hshape hnorm']:
 assert x in s,x
for x in ['(p : Fin 4 → ℕ)', '(hz : InternalZero', 'v 0=0', 'P72Root.cast_port', 'EtaZetaNaturalUnitBridgeDraft.signed_norms']:
 assert x in j,x
fact=Path('research/ordinary13-eta-zeta-zero-main-obstruction-draft/ZeroOrdinateMainObstruction.lean.src').read_text()
for x in ['(hq : 2≤q) (hY : q^3≤Y) (hX : X=q*w)','(hshape : z=ι (Y*(q*q))*ι X+ι (3+4*Y*(X+1))*t)','(hnorm : z*z=ι (Y*(q*q))*ι (Y*(q*q)))']:
 assert x in fact,x
print(json.dumps({'probe_J_zero_and_double_zero_actual_rows_checked':True,'natural_ports_positive_beta_and_both_zero_hypotheses_checked':True,'exact_fact_level_obstruction_inputs_checked':True,'author_receipt_reproduced':True,'lean_executed':False,'scope':'Unelaborated source proposal; graph/provider/axiom validation, eta>0 case and zero-map remain open.'},sort_keys=True,indent=2))
