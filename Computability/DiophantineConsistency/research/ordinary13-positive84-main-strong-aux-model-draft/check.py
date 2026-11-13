from pathlib import Path
from hashlib import sha256
import json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
PINS={'research/ordinary13-qcube-unscale84/candidate.json': '2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77', 'research/ordinary13-positive84-rank-window-model-draft/Positive84RankWindow.lean.src': '0896c49f3234e39487713c8cbd4e2341746e4f92222bdc0cccef200604d78377', 'research/ordinary13-unscale84-large-k-model-draft/Unscale84LargeK.lean.src': '8002fb8d0000a0f2f49b7f6e65826ce543deec738f5bf6b15e6c3f20ad841251', 'research/ordinary13-positive84-early-exact-model-draft/Positive84EarlyExact.lean.src': '2735739f3320c6d8794deba53e73bfc054bfeef0ff1b57ed4deefae5623d8d19', 'research/ordinary13-eta-natural-strong-aux-adapter-draft/EtaNaturalStrongAux.lean.src': 'c13a8d83acb13784027eb63dde7f61d0c4bd7f07b0f64e95afbf0eb9950e0abd', 'research/ordinary13-eta-natural-auxiliary-draft/AuxGeometryEtaNatural.lean.src': '5ccefb9efd90dad307ffcf55d67597b32a620d02e0a8b09eb88e642474a12782', 'research/ordinary13-residue90-norm-model-draft/Residue90SignedNorms.lean.src': 'f0f7b2af039ed45c19cb45170d8f6bed601451f794d871b7b21c818fd1cac70a', 'Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean': '29c748582368b4ab2bcdb4b4cdd4f7890dda32f77718e33355b590b8f07b7fbd', 'Lean/DiophantineConsistency/ArithmeticPellClassification.lean': '77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78', 'Lean/DiophantineConsistency/ArithmeticAdaptiveMainOrientation2011.lean': 'ad8a0d17ccf06c2f75ce8b095698b66f79869041ae07cf9ff0a376894b4c3968', 'research/ordinary13-positive84-main-strong-aux-model-draft/Positive84ClosedCuts.lean.src': '0f43b66ecdef8fb93fdbb788495621253944b51e685f562891d6594ef11be03b', 'research/ordinary13-positive84-main-strong-aux-model-draft/Positive84Main.lean.src': '6e44896ae06867726f2e02e84ac218cf00b3d8cde4ef438e9a6faecfa963e732', 'research/ordinary13-positive84-main-strong-aux-model-draft/Positive84StrongAux.lean.src': '6527457144160c5ce1e3f23e4bb745dc2ad2cd3f72557fdc051d11f4e88b852c'}
for p,h in PINS.items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
f=list(PINS);g=json.loads(Path(f[0]).read_text());src=[Path(x).read_text() for x in f[1:]];r={row[0]:row for row in g['source']}
assert len(g['source'])==84
for row in [['q','+',1,'qm'],['Y','*','q3','s'],['U','*','Y','q2'],['E','*','X','Y'],['g55','*','E','q'],['g56','+','g54','g55'],['shift','-','g56','r0'],['Dstar','+','g58','g59'],['A1','-','g61','g65'],['Q','*','Delta','rho'],['g72','-','g71','Q'],['V','-','g76','c'],['g81','-','y2','V2'],['Fa','-','y2','g82']]:assert r[row[0]]==row
checks={0:['theorem gap','theorem rank_representation','theorem divCut'],1:['theorem main_form','theorem large_k'],2:['def MainStrongAux','def MainStrongAuxGraphCut'],3:['theorem ordinary_strong_of_signed','theorem strict_bounds_of_strong','theorem index_aux_of_direct'],4:['theorem geometry_of_large_k'],5:['theorem main_pair_norm'],6:['theorem oriented_scaled_norm'],7:['theorem solution_index'],8:['theorem main_parts_positive'],9:['theorem divCut'],10:['theorem root_pair','theorem main_pair_norm','theorem oriented_index'],11:['theorem strong_form','theorem aux_form','theorem graph_norms','theorem strong_aux_witness','theorem mainStrongAuxGraphCut']}
for i,terms in checks.items():
 for term in terms:assert term in src[i],(i,term)
def ev(g,v,p):
 e=dict(zip(g['witnesses'],v));e.update(zip(g['fixed_numerals'],p))
 for name,op,x,y in g['source']:
  x=x if isinstance(x,int) else e[x];y=y if isinstance(y,int) else e[y]
  e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return e
rng=random.Random(840844);controls=0
for _ in range(300):
 v=[rng.randrange(1,5) for _ in range(13)];p=[rng.randrange(3,8),rng.randrange(0,5),rng.randrange(0,5),rng.randrange(0,5)]
 v[1]=v[2]=1
 e=ev(g,v,p);q=e['q'];X=v[6];Y=q**3*v[7];k=v[9]+v[10];c=v[9]+Y*k;a=X*Y+Y;H=3+4*a;D=H+a*a;U=Y*q*q
 R=((q-1)*(q-v[1])+v[2])*(q*q-1)+(p[2]+q*p[3])*v[0]
 P=U*(X+a*c)+H*(U*v[12]+X*Y*q+R+1);N=H*k
 z=v[3]**2*(v[5]*c-R)-c;Q=D*(v[3]**2-1)
 assert v[1]+v[2]<q and e['R']==R and e['Dstar']==P-N
 assert e['A1']==(P-N)**2-U**2*(1+D*c*c)
 assert e['g72']==(c*c*v[4])**2-Q and e['V']==z
 assert e['Fa']==v[11]**2-Q*(v[11]**2-z*z)
 assert (X*Y+Y+2)**2==D+1
 controls+=1
print(json.dumps({'sha256':PINS,'actual_graph_rows_checked':True,'same_rank_main_strong_aux_controls':controls,'lean_executed':False,'status':'Unelaborated proposed graph cut; no provider, axiom, Lean or endpoint validation.'},sort_keys=True,indent=2))
