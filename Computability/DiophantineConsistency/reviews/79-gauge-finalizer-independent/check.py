from pathlib import Path
from hashlib import sha256
import json,ast
root=Path('research/ten-positive-79-gauge-finalizer');o=root/'observations/attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='d2b38140816340f0957e7acd4f7daf5f6e8658eaf8353df2ff08b44309866340';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(root/'run.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='e6a1f9f6cadd26546078c0eff1ebe8acab5dda6dc4b37b54908b999758946d8d'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
assert r['pins']['/tmp/mask79-carrier-w290b5ah/Mask79Carrier.olean']['sha256']=='a880a3df700be3af796282b0600161756e640ad7da78fdcb383fa49b1c2f5b60'
for s in ['stdout','stderr']:assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text().strip()=="'Mask79Finalizer.preserve_output' depends on axioms: [propext, Quot.sound]" and not (o/'stderr').read_text()
rows=json.loads(Path('research/ten-positive-79-mask-coordinate-probe/candidate.json').read_text())['source'];assert len(rows)==79
for i,v in {47:['Q','*','Delta','fouraF0'],52:['V2','*','V','V'],69:['Znum','-','Zpart1','Zpart2'],73:['Z2','*','Znum','Znum'],74:['RG','*','M2','Dg'],75:['RGV2','*','RG','V2'],76:['inside','-','Z2','RGV2'],77:['Qinside','*','Q','inside'],78:['correction','-','RG','Z2'],79:['N','+','Qinside','correction']}.items():assert rows[i-1]==v
# Independently expand carrier and finalizer polynomials over integer coefficients.
tree=ast.parse(Path('reviews/79-gauge-normalization-independent/check.py').read_text());node=next(x for x in tree.body if isinstance(x,ast.ClassDef) and x.name=='P');ns={};exec(compile(ast.Module(body=[node],type_ignores=[]),'<polynomial>','exec'),ns);P=ns['P']
q,b,k,w,F,C,n,v,u,H,Z,Pvar,t,L,T=(P({(x,):1}) for x in 'q b k w F C n v u H Z P t L T'.split())
D=q*(k+w)+1;Bp=(k+w)*(C-q*b*t)-(F+b*t);B=(k+w)*C-F;np=n-(b*v+1)*D*t
old=(b*u)*(H*(n-v*B)+Z)-H*(u*B+b*Pvar);new=(b*u)*(H*(np-v*Bp)+Z)-H*(u*Bp+b*Pvar)
assert new==old and L*(new*new-T*v)+T-new*new==L*(old*old-T*v)+T-old*old
print('PASS: generic full finalizer identity independently expanded; actual graph row mapping matches candidate JSON, only conditional on unchanged L, T and v.')
