#!/usr/bin/env python3
import hashlib,json,subprocess,sys,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-first-cut-check'
pins={'run.py':'d7fe4417b384feab95997f2ed721028f5d4fa8d68e4548581139065459d17b6c','sign32-survey.py':'37fef46c1984b58172d0a309556ed624721d99b4197d219d7c3a96d2d6e08a45','source-manifest.json':'0a1d14a9b5d34b3e52b910a1b8d56569bb0fab9cc83547977a4455bc2b87c1da','src/DiophantineConsistency/Sign31FirstCut.lean':'6200f778872a1fcff0eb184092616d41a0c7fafac59283fc37b67d47b03bbf1c'}
for n,h in pins.items(): assert hashlib.sha256((P/n).read_bytes()).hexdigest()==h,n
s=(P/'src/DiophantineConsistency/Sign31FirstCut.lean').read_text()
def body(n):return re.search(r'def '+n+r' \(p : Fin 4 → ℤ\) : Expr \(Fin \d+\) :=\n\s*(.*?)\n\n',s,re.S).group(1).strip()
def rows(path):
 t=path.read_text().split('def remainingResiduals',1)[1].split('[',1)[1].split(']',1)[0];return [line.strip().removesuffix(',') for line in t.splitlines() if line.strip().startswith('(')]
a=rows(D/'research/nine-sharing-sign32-sextic-lean-draft/SharingSeed32Sextic.lean');b=rows(D/'research/nine-sharing-sign31-sextic-lean-draft/SharingSeed31Sextic.lean')
for n,rs,i in [('oldF2',a,14),('oldV',a,16),('newV',b,15),('oldscaledNs',a,21),('newscaledNs',b,20)]:assert body(n)==rs[i],n
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],cwd=D,text=True,capture_output=True);assert r.returncode==0,(r.stdout,r.stderr);assert json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS','preflight_exit':r.returncode,'exact_residual_rows':5,'scope':'Source and provider prelaunch; no Lean replay or transitive trace.'},sort_keys=True))
