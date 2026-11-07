#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-reference-ell-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'7d1865d0b6193f5dedabaaad943165bfdc33109e77b6b7a58b5696157e129b6e','provider_survey.py':'e93e0ae60790a3d94e7fa5dcc43319e962df44972ad865e7989b00f738809f25','source-manifest.json':'3c309f3cd0521e6efd486b839a65db60f9a67541d6034cb952454f55c981b542'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1;n='Sign33ReferenceEll';q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==rows[0]['source_sha256']=='de77993a9c692389f563cfde2b1b405b19cfd7ebb2765ae26d34739751de4976' and rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Norm38ReferenceFieldsAll'];assert '[CommRing R]' in s and 'reference p x 30 = (Carrier65.core p x).ell' in s and 'simp [reference, Carrier65.core] <;> ring' in s
ref=(d/'research/nine-sharing-norm38-reference-draft/Norm38Reference.lean').read_text();core=(d/'Lean/DiophantineConsistency/Carrier65.lean').read_text()
for x in ['let a21 : R := a14 * a0','let a22 : R := a21 + a18','let a23 : R := a22 * a22','let a24 : R := a23 * a22','let a25 : R := a8 * a22','let a26 : R := a7 * a24','let a27 : R := a25 * a26','let a28 : R := a10 + a11','let a29 : R := a28 * a26','let a30 : R := a27 * a29']:assert x in ref
for x in ['let X := w * q','let Y := s * q ^ 3','let E := X * Y','let k := eta + zeta','let ell := E * k * Y']:assert x in core
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'generic commutative-ring node 30 ell identity; no Lean replay'},indent=2,sort_keys=True))
