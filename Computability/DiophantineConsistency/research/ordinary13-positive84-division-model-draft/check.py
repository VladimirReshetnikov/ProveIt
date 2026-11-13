from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
PINS={'research/ordinary13-qcube-unscale84/candidate.json': '2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77', 'research/ordinary13-positive83-to84-model-draft/PositiveUnscaled84Graph.lean.src': 'd2eb1fc077aac66c67a4c75f6b6a70792b6f0c7923f3ec952ea64d3ad7cf8740', 'research/ordinary13-positive83-to84-model-draft/Positive83To84Bridge.lean.src': '25c422df0ada61b60049e7ccc2cdfbb6ea1ab52060c40c9ba1d57f9fa37dac17', 'research/ordinary13-residue-three-projection-model-draft/ResidueThreeProjection.lean.src': 'd4c30dc20ef93cbcad180d4ba350d77d0c0534e8ef485254509a9c1604026cf2', 'research/ordinary14-modified-carrier-model-facts-draft/ModifiedCarrierFacts.lean': 'd16c6dca1f5bb5240db5e2b72d6d1895568c9e178c933a68e92f82b6be2be43e', 'Lean/DiophantineConsistency/ArithmeticAdaptiveMersenne2011.lean': 'c8a132e1b28bd1cf1ed76d80e953d5568ff0c77f566ad7b2b66715c8be9641ef', 'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean': 'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea', 'research/ordinary13-unscale84-reverse-graph-model-draft/Unscale84ReverseGraph.lean.src': 'a747d1b83f054946cca51cb43c965236e79b5a0c970936c2539a30e1cf0d7387', 'research/ordinary13-eta-zero-growth-model-draft/EtaZeroGrowth.lean.src': '8f7f61c667d87c2e302e92a893dab01839cb5c5f5a8c1be26b08bf3a74360ab2', 'Lean/DiophantineConsistency/Compact44/FreeJPowerFinish.lean': 'e4b2e84586b6232b9accc7775f094d4e1047453f1e8337f6241d39a6657d8816', 'Lean/DiophantineConsistency/Compact44/FreeJPowerProjection.lean': 'fee95da196452c374b5d6aeaf2b3bb330e8d690224ad8dab523760df79da2749', 'research/ordinary13-positive84-division-model-draft/Positive84Division.lean.src': '20840eedc6993eaea993d7dc6cdec7b1b3643a0331d51c64f4ea2febadb530ac'}
for p,h in PINS.items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
f=list(PINS);g=json.loads(Path(f[0]).read_text());r={x[0]:x for x in g['source']}
assert len(g['source'])==84 and g['witnesses'][6:8]==['X','s']
for row in [['q','+',1,'qm'],['q3','*','q','q2'],['Y','*','q3','s'],['U','*','Y','q2'],['E','*','X','Y'],['g55','*','E','q'],['g56','+','g54','g55'],['shift','-','g56','r0']]:assert r[row[0]]==row
s=[Path(x).read_text() for x in f]
for i,items in {2:['def DivCut'],3:['theorem q_dvd_threeX','X*Y*q+R+1'],4:['theorem compact_beta_divides_X','(hX : X=Exp.exp R)'],5:['theorem cancel_three','(hq : q=(Exp.exp d-1)*J+1)'],6:['def betaNat : ℕ := 2^(67*8807)-1','theorem beta_identity'],7:['def ReverseInputs','8*X v*Y p v*Y p v+4≤k v'],8:['theorem power','(hX : X=q*w0)','(U*gamma+R+1)'],9:['theorem graph_power','Fin 12 → V'],10:['theorem graph_projection','Fin 12 → V'],11:['def OrientedIndexCut','def IndexGraphCut','def PowerGraphCut','theorem divCut_of_index_and_power']}.items():
 for item in items:assert item in s[i],(i,item)
assert 67*8807==590069
projection_cases=0
for q in range(1,8):
 for ss in range(1,3):
  Y=q**3*ss;U=Y*q*q
  for X in range(1,18):
   H=3+4*(X*Y+Y)
   for R in range(3):
    for w in range(3):
     k=R+1+4*(X*Y*Y)*w
     for c in range(3):
      for gamma in range(3):
       numerator=U*(X+(X*Y+Y)*c)+H*(U*gamma+X*Y*q+R+1)-H*k
       if numerator>=0 and numerator%U==0:
        main=numerator//U
        assert U*main+H*k==U*(X+(X*Y+Y)*c)+H*(U*gamma+X*Y*q+R+1)
        assert 3*X%q==0;projection_cases+=1
assert projection_cases>0
# Non-Mersenne scalar control; not a graph zero.
assert (3*8)%3==0 and 8%3!=0 and 8==2**3
print(json.dumps({'sha256':PINS,'exact_extra_carrier_rows_checked':True,'finite_oriented_projection_cases':projection_cases,'non_mersenne_scalar_countercontrol':{'q':3,'X':8,'is_graph_zero':False},'lean_executed':False,'status':'Conditional source client; graph index, power, reverse root, providers and Lean validation remain open.'},sort_keys=True,indent=2))
