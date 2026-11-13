from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
PINS={'research/ordinary13-qcube-unscale84/candidate.json': '2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77', 'research/ordinary13-positive84-early-exact-model-draft/Positive84EarlyExact.lean.src': '2735739f3320c6d8794deba53e73bfc054bfeef0ff1b57ed4deefae5623d8d19', 'research/ordinary13-positive84-power-model-draft/Positive84Power.lean.src': '565b28f2fcecbbc0b0f53d827a3dffc7fe8cd1f5090a8a80375e03242cf60a23', 'research/ordinary13-unscale84-reverse-graph-model-draft/Unscale84ReverseGraph.lean.src': 'a747d1b83f054946cca51cb43c965236e79b5a0c970936c2539a30e1cf0d7387', 'research/ordinary13-unscale84-large-k-model-draft/Unscale84LargeK.lean.src': '8002fb8d0000a0f2f49b7f6e65826ce543deec738f5bf6b15e6c3f20ad841251', 'research/ordinary13-positive81-carrier-data-model-draft/PositiveCarrierData.lean.src': 'd223f34c2bd1f493bff5a8925971d8d5a5a3d8b0142377248e9cac4000ea9182', 'research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src': '11ba8e4e01d29b956926a26b04815d5a660b79caabfce7b8cc1ce6d5c85d615a', 'research/ordinary13-eta-natural-rank-index-model-draft/EtaNaturalRankIndex.lean.src': '0832b087042375be828531a61d8baeca8676e64d386f6995e1f12de3bf441c41', 'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean': '0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414', 'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean': 'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea', 'research/ordinary13-positive84-rank-window-model-draft/Positive84RankWindow.lean.src': '0896c49f3234e39487713c8cbd4e2341746e4f92222bdc0cccef200604d78377'}
for p,h in PINS.items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
f=list(PINS);g=json.loads(Path(f[0]).read_text());s=[Path(x).read_text() for x in f[1:]];r={row[0]:row for row in g['source']}
for row in [['qm','*','J','beta'],['q','+',1,'qm'],['C','-','qF','alpha'],['g25','*','K0','q'],['g26','+','X','g25'],['g27','*','C','g26'],['g28','*','F','q'],['Bt','-','g27','g28'],['g44','*','qF','qm'],['G','+','alpha','g44'],['g46','-','q2',1],['g47','*','G','g46'],['g48','*','MF','q'],['g49','+','MC','g48'],['g50','*','J','g49'],['R','+','g47','g50']]:assert r[row[0]]==row
for i,needles in {0:['def RankWindowGraphCut'],1:['def rank84'],2:['theorem source_first','theorem source_root'],3:['def rank'],4:['theorem P_positive'],5:['theorem compact_rank_window','(hgap : F+alpha<q)'],7:['def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]'],9:['theorem carrier_positive','theorem gap','theorem rank_representation','theorem rank_at_least_26','theorem compact_rank_window','theorem rankWindowGraphCut']}.items():
 for x in needles:assert x in s[i],(i,x)
gap_cases=rank_cases=0
for beta in (46,47,48,64,79):
 for J in range(1,4):
  q=1+beta*J
  for F in range(1,12):
   for alpha in range(1,12):
    for X in (1,2,7):
     for K in (0,1,5):
      P=(q-F-alpha)*(X+K*q)-F*q
      if P>0:assert F+alpha<q;gap_cases+=1
    if F+alpha<q:
     for MC,MF in ((0,0),(beta-1,2*beta-1),(beta//2,beta)):
      R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
      Rs=(alpha+(q-F)*(J*beta))*(q*q-1)+J*(MC+MF*q)
      assert R==Rs and R>=26 and R+q**3+q+1<=q**4;rank_cases+=1
assert min(gap_cases,rank_cases)>0
print(json.dumps({'sha256':PINS,'actual_carrier_and_rank_rows_checked':True,'positive_carrier_gap_controls':gap_cases,'rank_and_window_controls':rank_cases,'lean_executed':False,'status':'Unelaborated source proposal; dependency providers, tactics, compact byte/PDF bindings remain open.'},sort_keys=True,indent=2))
