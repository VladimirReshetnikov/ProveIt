#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,random,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-74-first-factor-small-cut-draft'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'b1ca108b14f6571207072d7ca1b1dff34702e499de4612ddb5fe32521b6a95fb',A/'FirstFactorSmallCut74.lean':'36d3dbed1933369558e695b67ba6fd19564718e2ab47ba3ddf6d56f7e58917d6',A/'check_source.py':'be64f984b6c47ad9882bc663e017aa97619e8bf25543bbaef76c47fb12b8a20f',A/'observation.json':'8f5301695f75c484c8c53d18db0f84ce1ef7b75faeea028cfb21235ea9894a82'}
tail=b"\nIndependent source review: [74 first-factor small cut](../../reviews/ordinary14-74-first-factor-small-cut-independent/README.md).\n"
for p,h in pins.items():
 if p==A/'README.md':
  data=p.read_bytes();assert hashlib.sha256(data).hexdigest()=='4df74a0c29938dcc5421b8b8dfcd0df4657e03f5443066dcaeb9d2b8cd44b29f'
  assert data.endswith(tail) and hashlib.sha256(data[:-len(tail)]).hexdigest()==h
 else:assert H(p)==h,(str(p),H(p),h)
a=(A/'FirstFactorSmallCut74.lean').read_text();g=(D/'research/ordinary14-unit75-guard74-lean-draft/P74PositiveGuard.lean').read_text();old=(D/'research/ordinary14-74-first-factor-client-draft/FirstFactor74.lean').read_text()
# Check the actual Lean graph rows, not only the JSON source.
rows=dict(re.findall(r'^  let (\w+) := (.+)$',g,re.M))
expected={'qm':'J * beta','q':'1 + qm','X':'q * w','q2':'q * q','q3':'q * q2','Y':'q3 * s','E':'X * Y','k':'eta + zeta','kY':'Y * k','ell':'E * kY','g30':'ell + k','g38':'r * r','g40':'ell * g30','F0':'g38 - g40'}
assert all(rows.get(k)==v for k,v in expected.items())
for x in ('let J : Expr (Fin 14) := .var 0','let w : Expr (Fin 14) := .var 6','let s : Expr (Fin 14) := .var 7','let r : Expr (Fin 14) := .var 8','let eta : Expr (Fin 14) := .var 9','let zeta : Expr (Fin 14) := .var 10','let beta : Expr (Fin 14) := .constant (p 0)','⟨F0, F1, Fa, Fs, guard, out,'):
 assert x in g,x
for x in ('def qExpr (p : Fin 4 → ℤ) : Expr (Fin 14) := 1+(.var 0)*(.constant (p 0))','def XExpr (p : Fin 4 → ℤ) : Expr (Fin 14) := qExpr p*(.var 6)','def YExpr (p : Fin 4 → ℤ) : Expr (Fin 14) := (qExpr p*(qExpr p*qExpr p))*(.var 7)','def kExpr : Expr (Fin 14) := (.var 9)+(.var 10)','def ellExpr (p : Fin 4 → ℤ) : Expr (Fin 14) := (XExpr p*YExpr p)*(YExpr p*kExpr)','(.var 8)*(.var 8)-ellExpr p*(ellExpr p+kExpr)','theorem first_shape (p : Fin 4 → ℤ) : (P74PositiveGuard.graph p).first=firstExpr p := by rfl'):
 assert x in a,x
def statement(text,name):
 i=text.index('theorem '+name+' ');return re.sub(r'\s+','',text[i:text.index(' := by',i)].replace(name,'THEOREM',1))
assert statement(a,'first_eval_small')==statement(old,'first_eval')
rng=random.Random(7408);counts={}
for modulus in (4,12,17):
 for _ in range(250):
  beta,J,w,s0,r,eta,zeta=[rng.randrange(-30,31) for _ in range(7)]
  q=1+J*beta;X=q*w;Y=q*(q*q)*s0;k=eta+zeta;ell=(X*Y)*(Y*k);m=X*Y*Y
  assert (r*r-ell*(ell+k))%modulus==(r*r-(m*k)*(m*k+k))%modulus
 counts[str(modulus)]=250
v=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,capture_output=True,check=True,timeout=90);assert not v.stderr and v.stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'literal source-cut and finite ring controls; no Lean, observed failure or measured resource benefit','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'actual_lean_rows_checked':len(expected),'modular_controls':counts,'same_eval_statement':True,'author_receipt_replayed':True},sort_keys=True,indent=2))
