from pathlib import Path
from hashlib import sha256
import json,ast
root=Path('research/ten-positive-79-gauge-carrier');o=root/'observations/attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='4f81e10f28e8babe452258e713c62b2c472d475b8cf49428aa4f07bbfad72149';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(root/'run.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='a880a3df700be3af796282b0600161756e640ad7da78fdcb383fa49b1c2f5b60'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
for s in ['stdout','stderr']:assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text().strip()=="'Mask79Carrier.preserve_rank_and_main' depends on axioms: [propext, Quot.sound]" and not (o/'stderr').read_text()
rows=json.loads(Path('research/ten-positive-79-mask-coordinate-probe/candidate.json').read_text())['source'];assert len(rows)==79
for i,v in {1:['bJ','*','beta','J'],2:['q','+','bJ',1],16:['Hp','-','4Am1',1],25:['G','-','G1','C'],33:['e','-','kR',1],36:['Bt','-','K0wC','F'],52:['V2','*','V','V'],53:['mu2','*','mu','mu'],54:['P1mu2','*','bJ','mu2'],56:['center','-','n','LBt'],57:['Hn','*','Hp','center'],62:['Kpos','+','Kpos0',2],63:['lin','+','Hn','Kpos'],64:['Zpart1','*','P1mu2','lin'],65:['mu2inner','*','mu2','Bt'],66:['P1e','*','bJ','e'],67:['brk','+','mu2inner','P1e'],68:['Zpart2','*','Hp','brk'],69:['Znum','-','Zpart1','Zpart2']}.items():assert rows[i-1]==v
# Extract the small independent sparse-polynomial implementation used in the prior gauge audit.
tree=ast.parse(Path('reviews/79-gauge-normalization-independent/check.py').read_text());node=next(x for x in tree.body if isinstance(x,ast.ClassDef) and x.name=='P');ns={};exec(compile(ast.Module(body=[node],type_ignores=[]),'<polynomial>','exec'),ns);P=ns['P']
q,b,k,w,F,C,n,v,u,H,Z,Pvar,t=(P({(x,):1}) for x in 'q b k w F C n v u H Z P t'.split())
D=q*(k+w)+1;Fp=F+b*t;Cp=C-q*b*t;np=n-(b*v+1)*D*t;B=(k+w)*C-F;Bp=(k+w)*Cp-Fp
assert q*(q-Fp)-Cp==q*(q-F)-C
assert (b*u)*(H*(np-v*Bp)+Z)-H*(u*Bp+b*Pvar)==(b*u)*(H*(n-v*B)+Z)-H*(u*B+b*Pvar)
assert Bp==B-b*D*t and np-v*Bp==n-v*B-D*t
for bb in range(1,6):
 qq=bb+1
 for ff in range(1,6):
  for cc in range(1,20):
   for tt in range(5):
    if qq*bb*tt<cc:assert (ff+bb*tt+cc-qq*bb*tt<qq)==(ff+cc<qq+bb*bb*tt)
assert all(1-2*dd<=0 for dd in range(1,20))
print('PASS: 79 candidate row map and independent sparse-polynomial rank/main-carrier identities verified; positive-coordinate and guard obligations remain conditional.')
