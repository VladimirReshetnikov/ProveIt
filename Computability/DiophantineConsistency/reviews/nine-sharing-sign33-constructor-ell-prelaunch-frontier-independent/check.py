#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-constructor-ell-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'3d60f4443715537875a2934da3feda3b42440ca36542a5d9409fcac416f04575','provider_survey.py':'baeb9e22dc79386969847a6ce3cc260e87e2b455bfbb162256995b37bc99aa43','source-manifest.json':'8f11f3918461d4506face1a466728bc154da3ee56c0284b4235107bae43aea4d'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1;n='Sign33ConstructorEll';q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==rows[0]['source_sha256']=='5b53d2dc7b13f93019c618e6584c427b36f7792f98c94e0a123ba38d1cb7770c' and rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+x for x in ['Sign33ReferenceEll','Norm38ReferenceTerminals','Norm38ForwardGatesAssembly','Norm38ForwardPrefix','SharingForward33']]
for x in ['ι (v 21)','u j+1','static_assignment_fixed','ringRun_agrees_of_topological','val 30 = ref 30','initial_agreement ports w','reference_gate_equations_batched','Sign33ReferenceEll.reference_ell','Norm38Forward.forward_prefix','(20 : Fin 33).succ = (21 : Fin 34)','Fin.cons_succ']:assert x in s
f=(d/'research/nine-sharing-sign33-forward-constructor-check/src/DiophantineConsistency/SharingForward33.lean').read_text();vec=[x.strip() for x in re.search(r'!\[(.*?)\]',f.split('def witnessCoordinates',1)[1].split('theorem witness_inputs',1)[0],re.S).group(1).split(',')];assert vec[20]=='w 20'
a=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text();assert 'let a30 : SignedPair S := ⟨w 20, 0⟩' in a
survey=(p/'provider_survey.py').read_text();assert "'research/nine-sharing-sign33-reference-ell-check/attempt01/state.json','55e40338fc8a1c4274b7a53aa696c4a03eb7382c22b949fb3eec82ec9a916c0d'" in survey and "'Sign33ReferenceEll'" in survey
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'constructor ell via node 30 topology; no Lean replay'},indent=2,sort_keys=True))
