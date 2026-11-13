#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-affected-cuts-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'2b9f423151bcdee732eb6a995e2b3ad1a9319e525696a6826950626f0b06df00','source-manifest.json':'c4e9afd7fdba7b7e6a8be349e49f4af55b7034424a2c27689e51166afa55493d','src/DiophantineConsistency/Sign27AffectedCuts.lean':'0764df045edddd2059dbb80699c9ffbdd70f79dce5a299965bbd36f8111d20d4'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.Sign27FirstCut'];s=(P/'src/DiophantineConsistency/Sign27AffectedCuts.lean').read_text();assert H(D/'research/nine-sharing-sign27-affected-cuts-draft/Sign27AffectedCuts.lean')==m[0]['source_sha256']
rows=[]
for n in (28,27):
 t=(D/f'research/nine-sharing-sign{n}-sextic-lean-draft/SharingSeed{n}Sextic.lean').read_text().split('def remainingResiduals ',1)[1].split('\n  [\n',1)[1].split('\n  ]',1)[0];rows.append([x.strip().removesuffix(',') for x in t.splitlines()]);assert len(rows[-1])==n-10
for name,oldi,newi in [('MainRoot',5,5),('Dc2',6,6),('NormalizedS',14,13)]:
 for tag,idx,ss in [('old',oldi,rows[0]),('new',newi,rows[1])]:
  expr=s.split(f'def {tag}{name} ',1)[1].split(':=\n',1)[1].split('\n',1)[0].strip();assert expr==ss[idx];assert f'((SharingSeed{28 if tag=="old" else 27}Sextic.remainingResiduals p).drop {idx}).head? = some ({tag}{name} p)' in s
 assert f'theorem {name}_eval' in s
lift=(D/'research/nine-sharing-sign27-first-cut-retry01/src/DiophantineConsistency/Sign27FirstCut.lean').read_text();assert 'v 21 + 1, v 21 * (v 21 + 2), v 22, v 23, v 24, v 25, v 26, v 27' in lift
up=D/'reviews/nine-sharing-sign27-first-cut-retry01-terminal-frontier-independent/check.py';assert H(up)=='d049db4de12602c490af2b6649f1d6c850a5d2982014b2eddd6acc138fdb1549';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'three affected residual identities at exact old/new positions; no full zero bridge or Lean replay'},sort_keys=True,indent=2))
