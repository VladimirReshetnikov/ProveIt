from pathlib import Path
import hashlib,json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-positive84-main-strong-aux-same-witness-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-positive84-main-strong-aux-model-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(P/'check.py')])==(P/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-qcube-unscale84/candidate.json').read_text()); r={row[0]:row[1:] for row in g['source']}
required={'E':['*','X','Y'],'g55':['*','E','q'],'g54':['*','U','gamma'],'g56':['+','g54','g55'],'g52':['-','k','R'],'r0':['-','g52',1],'shift':['-','g56','r0'],'Dstar':['+','g58','g59'],'g72':['-','g71','Q'],'V':['-','g76','c'],'Fa':['-','y2','g82']}
for key,row in required.items():assert r[key]==row,(key,r[key],row)
main=(P/'Positive84Main.lean.src').read_text();aux=(P/'Positive84StrongAux.lean.src').read_text();close=(P/'Positive84ClosedCuts.lean.src').read_text()
for s in ['U p v*v 12+v 6*Y84 p v*q84 p v+rank84 p v+1','Positive84RankWindowDraft.rank_representation p v hgap','ArithmeticAdaptiveMainOrientation2011.main_parts_positive','DirectMainNorm.oriented_scaled_norm','ArithmeticPellClassification.solution_index (a p v) main (c84 p v) hm\'', '⟨main,m,hx,hy,hm\',?_⟩']:
 assert s in main,s
for s in ['Unscale84LargeKDraft.large_k p v hv hz\' hbeta','Positive84RankWindowDraft.gap p v hv hz hbeta','EtaNaturalStrongAuxDraft.strict_bounds_of_strong','EtaNaturalStrongAuxDraft.index_aux_of_direct','Positive84MainDraft.oriented_index _ v hv hz hbeta','strong_aux_witness _ v hv hz hbeta','⟨main,m,u,hx,hy,hnorm,hstrong,?_,?_⟩']:
 assert s in aux,s
assert 'Positive84RankWindowDraft.divCut K' in close and 'Positive84StrongAuxDraft.mainStrongAuxGraphCut K' in close
for s in (main,aux):
 assert 'q84 p v∣v 6' not in s and 'zero84_to83' not in s
src=Path('research/ordinary13-eta-natural-strong-aux-adapter-draft/EtaNaturalStrongAux.lean.src').read_text()
for s in ['theorem strict_bounds_of_strong (c i Delta f T R : V)','theorem index_aux_of_direct (c Delta f T R y : V)','(hf : 0<f)','∃ u : V, 0<u']:
 assert s in src,s
geom=Path('research/ordinary13-eta-natural-auxiliary-draft/AuxGeometryEtaNatural.lean.src').read_text()
assert 'A<c ∧ 1<c ∧ 0<Delta ∧ Delta<c*c*c' in geom
print(json.dumps({'actual_84_extra_term_and_auxiliary_rows_checked':True,'main_norm_pell_root_and_index_thread_checked':True,'strong_auxiliary_geometry_interface_checked':True,'no_explicit_q_div_X_or_84_to83_assumption':True,'author_receipt_reproduced':True,'lean_executed':False,'scope':'Only unelaborated source composition; transitive providers, tactic execution, axiom audits and endpoint remain open.'},indent=2,sort_keys=True))
