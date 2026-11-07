#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-lean-bridge-plan/README.md';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert H(P)=='43f9733a995e420af214b12ca9de35b8e43efad518375a2ea6598f25ac42f4e3';s=P.read_text()
for x in ['Fin 27','Fin 28','old 22','old 23–27','-(a-n)*(Q-q³)','conditional on the q3 residual vanishing','Nt = H*(q-n-t) - n - (f-1)*a','((p 0 : ℤ) : DiffRing V) = ι beta','((p 1 : ℤ) : DiffRing V) = ι K','1 ≤ beta','nonneg_iff','ι w = g','source-only plan','no sign26 Lean syntax']:assert x in s
q=D/'research/nine-sharing-sign26-sextic-gap-congruence-candidate';assert H(q/'check.py')=='c1cd665b9e9bc170bbdb416662e7e56c6397a4e038b4e1da8af2df4d6ae0d3c7' and H(q/'seed.json')=='36efa7dd3b2ea06d210b8975db2cbfc4f7494549c87204ada18747a720cb1f25';r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,text=True,check=True,timeout=120);j=json.loads(r.stdout);assert not r.stderr and j['status']=='PASS_EXACT_POLYNOMIAL_CONGRUENCE_AND_FINITE_CONTROLS' and j['residuals']==17 and j['witnesses']==26
print(json.dumps({'status':'PASS_SOURCE_PLAN_REVIEW','scope':'conditional algebra and explicit ordered-model/port-cast/representation obligations only; no Lean bridge'},sort_keys=True,indent=2))
