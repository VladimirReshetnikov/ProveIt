from pathlib import Path
import hashlib,json,subprocess,sys,math
root=Path(__file__).resolve().parents[2];d=root/'research/free-pell-gap-seed-characterization'
pins={'README.md':'0f47f871bbffaf1726d0a59d29b391e0442ea7763c4d24ec3f37c33f42a9e2f0','check.py':'f87111800961ee6c54049e43e3d4a17724c811ac9bf6fd5c83bd7b6ca79a74c1','result.json':'a19cdffe7b1ddf4795b42ed37ccc46a37cc008388496c1c4cdc09893cc35180c'}
for n,h in pins.items():assert hashlib.sha256((d/n).read_bytes()).hexdigest()==h,n
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(d/'check.py')])==(d/'result.json').read_bytes()
q=root/'research/free-pell-gap-generic-completion';s=(q/'README.md').read_text();tail='\nIndependent external review is recorded in\n`../../reviews/free-pell-gap-generic-completion-independent/`.\n';assert s.endswith(tail) and hashlib.sha256(s[:-len(tail)].encode()).hexdigest()=='14201bdce6293c730d62745fae0bb5b92f3c64199fc5c4be87dc51768f212e89';assert subprocess.check_output([sys.executable,'-I','-S','-B',str(q/'check.py')])==(q/'result.json').read_bytes()
graph=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';assert hashlib.sha256(graph.read_bytes()).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(graph.read_text());rs={x[0]:x[1:] for x in g['source']}
expected={'E':['*','X','Y'],'k':['+','eta','zeta'],'kY':['*','k','Y'],'ell':['*','E','kY'],'c':['+','kY','eta'],'a':['+','E','Y'],'H':['+','four_a',3],'Delta':['+','a2','H'],'N0':['-','tau2','first_product'],'N1':['-','main_square','Dc2'],'Nt':['-','transport_partial','zqm'],'normalized_S':['*','i','Dc2'],'scaled_Ns':['-','scaled_f2','normalized_S2'],'product0':['*','N0','N1'],'product1':['*','product0','Na'],'product3':['*','product1','Nt'],'product4':['*','product3','scaled_Ns'],'polynomial':['-','product4','Delta']}
for n,v in expected.items():assert rs[n]==v,n
seed={'J','F','alpha','z','s','w','n','eta','zeta','gamma'};assert seed<set(g['witnesses']) and set(g['witnesses'])-seed=={'f','i','T','y'}
# Exact finite controls for the two independent unit sign arguments.
for a in range(4):
 delta=((a+2)**2-1)%4
 for x in range(4):
  for y in range(4):assert (x*x-delta*y*y)%4!=3
odd=even=0
for S in range(2,1025):
 M=S*S-1
 if S%2:
  odd+=1;assert M%8==0 and 7 not in {x*x%8 for x in range(8)}
 else:
  even+=1;assert M%4==3
  residual=M;factors=[];p=3
  while p*p<=residual:
   if residual%p==0:
    factors.append(p)
    while residual%p==0:residual//=p
   p+=2
  if residual>1:factors.append(residual)
  candidates=[p for p in factors if p%4==3];assert candidates and all(pow(p-1,(p-1)//2,p)==p-1 for p in candidates)
print(json.dumps({'status':'PASS_EXTERNAL_MATHEMATICAL_REVIEW','seed_coordinates':10,'odd_S_controls':odd,'even_S_controls':even,'scope':'Free-gap candidate zero existence iff positive first/main/transport seed; no actual-port seed, Lean or original-zero equivalence'},indent=2))
