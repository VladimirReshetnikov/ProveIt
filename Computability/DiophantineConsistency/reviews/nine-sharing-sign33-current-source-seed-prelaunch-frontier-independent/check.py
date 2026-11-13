#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-current-source-seed-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'435b9afc246f0b5ba7efe0a0c369bc8e2827fc415240957085ab5db4bbf6289e','provider_survey.py':'d9cd84d013f9aeb7627dcf69a9791f8a1ba56b7067fc88ada1fea1211b8d48d5','source-manifest.json':'f8327d8f599c4054f3e267e7362f8e08caa2a57b7882665970300466ad36c324'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1;n='Sign33CurrentSourceSeed';q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==rows[0]['source_sha256']=='09d79663023756ca3bfa52a7dc518e6d8388ee30fb79e4f5a590c9d8f315c25d' and rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33CurrentForwardAllCuts','DiophantineConsistency.Sign33ResidualIff']
for x in ['(hp : ∀ j, ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V) = ι (ports j))','InternalZero ObjectCurrentEquation2011.naturalExpression u','∃ w : Fin 33 → V','InternalZero (SharingSeed33.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w)','source_has_all_cuts ports u hp hz','SharingForward33.witnessCoordinates ports u gap tau inner value negative','(Fin.cons (1 : V) w) (hp 0) (hp 1) (hp 2) (hp 3)).mpr hcuts']:assert x in s
prev=(d/'research/nine-sharing-sign33-residual-iff-check/src/DiophantineConsistency/Sign33ResidualIff.lean').read_text();assert 'InternalZero (SharingSeed33.seed p) v ↔ Sign33ResidualAssembly.AllCuts ports v' in prev
survey=(p/'provider_survey.py').read_text();assert 'a2a847e5f153f20fc29faaf3b19ffe4c8730f99b608f42be21ac05c95f751109' in survey and 'Sign33ResidualIff' in survey
run=(p/'run.py').read_text();assert "if mod in survey['selected']" in run and "need(guard(deps)==row['direct_guard']" in run
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'current natural source zero to 33-seed zero under explicit port casts; no Lean replay'},indent=2,sort_keys=True))
