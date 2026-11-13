from pathlib import Path
import hashlib,json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-zeta-zero-compact-parity-witness-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-zeta-zero-compact-parity-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(P/'check.py')])==(P/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text());r={row[0]:row[1:] for row in g['source']}
required={'kbase':['+','n_eta','n_zeta'],'kY':['*','Y','kbase'],'c':['+','n_eta','kY'],'i':['+','n_i',1],'T':['+','n_T',1],'E':['*','X','Y'],'a':['+','E','Y'],'g15':['*',4,'a'],'H':['+',3,'g15'],'g17':['*','a','a'],'Delta':['+','H','g17'],'I':['*','c2','i'],'g71':['*','I','I'],'g72':['-','g71','Q'],'g74':['*','T','c'],'g75':['-','g74','R'],'g76':['*','f2','g75'],'V':['-','g76','c'],'g81':['-','y2','V2'],'g82':['*','Q','g81'],'Fa':['-','y2','g82']}
for name,row in required.items():assert r[name]==row,(name,r[name],row)
a=(P/'ZetaZeroCompactGraph.lean.src').read_text();b=(P/'ZetaZeroCompactParity.lean.src').read_text()
for t in ['(hzeta : v 10=0) (heta : 0<v 9)','have hkeq : k v=v 9','EtaZetaNaturalGapRankDraft.gap p v hz hbeta hk1','EtaZetaNaturalGraphStrongAuxDraft.direct_auxiliary p v hz hFq','zeta_zero_of_represented_factors K v hz hzeta heta hstrong haux','by_cases heta : v 9=0','both_zero_impossible p v hz hbeta heta hzeta','positive_eta_branch K v hz hzeta (pos_iff_ne_zero.mpr heta)','theorem zeta_positive']:
 assert t in a,t
for t in ['(hzeta : v 10=0) (heta : 0<v 9)','compact_rank_at_least_26 K v hz','compact_rank_window K v hz hk1','natural_norms_of_graph p v hz hbeta','⟨tau,n,w,hfirst,_,_,_,hny,hnmod,_,_,hks⟩','compact_early_index K v hz hk1','(k v) (rank p v) tau g (v 4+1) (v 3) (v 5+1) (v 11) n w (v 7+1)','hq3 hX hs hYeq hk hi hR26 hfirst hmain hny hks hRmu hnmod hstrong haux']:
 assert t in b,t
boundary=Path('research/ordinary13-zeta-zero-parity-boundary-draft/ZetaZeroParityBoundary.lean.src').read_text()
for t in ['theorem contradiction_of_facts (q X Y k R tau g i f T y n w s0 : V)','(hfirst : tau*tau=1+(X*Y*Y)*(X*Y*Y+1)*k*k)','(hny : 2*ycoord n (2*(X*Y*Y-1)+1)=k)','(hnmod : (2*n)%(q^4)=R+1)','(hstrong :','(haux :','solution_index a g c hg','zeta_zero_contradiction q X Y k R g c a s0 i f T u n w (q^4) m']:
 assert t in boundary,t
early=Path('research/ordinary13-eta-zeta-natural-early-index-draft/EtaZetaNaturalGraphEarlyIndex.lean.src').read_text()
for t in ['theorem compact_early_index (K : ℕ) (v : Fin 13 → V)','∃ tau n w : V,','2*ycoord n','(2*n)%((q p v)^4)=rank p v+1','k v=2*n+4*(X p v*Y p v*Y p v)*w']:
 assert t in early,t
aux=Path('research/ordinary13-eta-zeta-natural-strong-aux-draft/EtaZetaNaturalGraphStrongAux.lean.src').read_text()
for t in ['theorem field_I','theorem direct_auxiliary','(hFq : v 1+1≤q p v)','v 3*v 3*(T v*c p v)','v 3*v 3*rank p v+c p v']:
 assert t in aux,t
print(json.dumps({'actual_changed_graph_strong_aux_rows_checked':True,'eta_zero_and_eta_positive_branches_checked':True,'same_graph_rank_tau_n_w_and_main_norm_interfaces_checked':True,'compact_port_K_is_arbitrary_natural':True,'author_receipt_reproduced':True,'lean_executed':False,'endpoint_proved':False},sort_keys=True,indent=2))
