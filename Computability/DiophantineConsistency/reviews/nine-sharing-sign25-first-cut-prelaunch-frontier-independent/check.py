#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-first-cut-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'9407db622e6b203a1337d1d50677bba8b42c1fa09be00335873539d857c64448','source-manifest.json':'0c7c894b8f09cb5b37978ece8fcb0b20eb93855dd99df76f5531e4670d155bc9','sign26-survey.py':'30f29f53f57089609e7e2e93c31e1885f2a91a68135e4149f36b1c83b12e41cb','src/DiophantineConsistency/Sign25FirstCut.lean':'640863c2a99e53145994df26088adc40a054e4bb8154611fbc4099da699db84c'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.SharingSign25Squares','DiophantineConsistency.SharingSign26Squares'];s=(P/'src/DiophantineConsistency/Sign25FirstCut.lean').read_text();blocks=re.findall(r'!\[([^\]]+)\]',s);assert len(blocks)==1 and [x.strip() for x in blocks[0].split(',')]==[f'v {i}' for i in range(19)]+['v 17 * v 18']+[f'v {i}' for i in range(19,26)]
a=json.loads((D/'research/nine-sharing-sign26-sextic-gap-congruence-candidate/seed.json').read_text())['residuals'];b=json.loads((D/'research/nine-sharing-sign25-octic-ell-candidate/seed.json').read_text())['residuals'];assert a[4]['gate']=='ell' and a[9]['gate']=='N0' and b[8]['gate']=='N0'
def render(t):
 op=t[0]
 if op=='var':return f'(Expr.var {t[1]})'
 if op=='num':return f'(Expr.constant ({t[1]} : ℤ))'
 if op=='port':return '(Expr.constant (p '+str({'beta':0,'K0':1,'MC':2,'MF':3}[t[1]])+'))'
 return '('+render(t[1])+' '+{'add':'+','sub':'-','mul':'*'}[op]+' '+render(t[2])+')'
for name,t in [('oldEll',a[4]['expr']),('oldN0',a[9]['expr']),('newN0',b[8]['expr'])]:assert s.split(f'def {name} (p : Fin 4 → ℤ) : Expr (Fin ',1)[1].split(':=\n  ',1)[1].split('\n',1)[0]==render(t)
for x in ['remainingResiduals p).drop 3','remainingResiduals p).drop 8','remainingResiduals p).drop 7','theorem old_ell_zero','theorem N0_eval','map_mul']:assert x in s
for n,h in [('nine-sharing-sign25-seed-squares-terminal-frontier-independent','8207d760d00d9df69137a6148da3565b8748afdf9246880eae8125feaabce9f9'),('nine-sharing-sign26-seed-squares-terminal-frontier-independent','a60bbcc769f385fd2ac4ac843ad661fa13a9668567e7f15157d3de4fa207911d')]:
 q=D/'reviews'/n/'check.py';assert H(q)==h;subprocess.run([sys.executable,'-I','-S','-B',str(q)],check=True,capture_output=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],check=True,capture_output=True,text=True,timeout=180);assert json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'product ell row/zero and affected N0 transfer only; no zero bridge or endpoint'},sort_keys=True,indent=2))
