#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-jones-named-formula-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'4758be79ca76102e103b219827409e4f4d1d2301843394f035f008418d7639d0','provider_survey.py':'e4df24ce990aab278c7c7d6182fa75e43bc225f4c9a67898aff9d43d83fb2a0b','source-manifest.json':'c1b69e75cfdbd0416c08ad94f8f5ad66a84e9f928ffac5f91e2539b9966324b2'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1;n='Sign33NamedFormula';q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==rows[0]['source_sha256']=='297573ea8e44e9047b73614337f2c0054fcc9de1c42272a4893bf6365d7e2871' and rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33IPRAEndpoint','DiophantineConsistency.ModelJonesSyntax']
old=(d/'research/nine-seed38-jones-named-formula-check/src/DiophantineConsistency/Norm38NamedFormula.lean').read_text();assert old.replace('Norm38IPRAEndpoint','Sign33IPRAEndpoint').replace('Norm38NamedFormula','Sign33NamedFormula').replace('38-witness','33-witness').replace('let ν := 38','let ν := 33').replace('SharingSeed38.seed','SharingSeed33.seed')==s
for x in ['[CommRing R]','let ν := 33','let seed := SharingSeed33.seed CurrentWindowCarry2011.ports','let z := indexZ seed 0','let y := indexY seed 0','let aa : Fin 10 → R := Fin.cons 1 a','RefinedPair.value','ModelJonesSyntax.evalRing_expression','ModelJonesSyntax.mapVars_syntaxVars']:assert x in s
survey=(p/'provider_survey.py').read_text();assert '451878b602e716cd712c2e8709e3546c13e5dbcc7c1ff7edc6dc669b640a4338' in survey
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'symbolic ring named RHS only; no Lean replay or external serialization binding'},indent=2,sort_keys=True))
