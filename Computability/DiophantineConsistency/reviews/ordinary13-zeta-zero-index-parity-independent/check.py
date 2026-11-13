from pathlib import Path
import hashlib,json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-zeta-zero-index-parity-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-zeta-zero-index-parity-contradiction-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(P/'check.py')])==(P/'receipt.json').read_bytes()
a=(P/'ZetaZeroIndexParity.lean.src').read_text();b=Path('research/ordinary13-eta-zero-p72-index-draft/P72ExactEtaNatural.lean.src').read_text();c=Path('research/pell-main-ordinate-parity-model-draft/PellOrdinateParity.lean.src').read_text()
for x in ['(hc : c = k + Y * k)', '(hny : 2 * ycoord n', '(hks : k = 2 * n', '(hmy : ycoord m a = c)', 'm k hq3 hX hy0 hYq hc hi\' hf ha', 'PellOrdinateParityModelDraft.ordinate_mod_two m a']:
 assert x in a,x
for x in ['(hc : c = η + Y * k)', '13 ≤ n ∧ n < m ∧ m = R ∧ 2 * n = R + 1', '(hmy : ycoord m a = c)', '(haux :']:
 assert x in b,x
assert 'theorem ordinate_mod_two (n b : V) : ycoord n b % 2 = n % 2' in c
print(json.dumps({'general_eta_index_interface_and_same_m_n_checked':True,'main_ordinate_parity_interface_checked':True,'eta_positive_not_assumed':True,'actual_graph_binding_proved':False,'lean_executed':False},indent=2,sort_keys=True))
