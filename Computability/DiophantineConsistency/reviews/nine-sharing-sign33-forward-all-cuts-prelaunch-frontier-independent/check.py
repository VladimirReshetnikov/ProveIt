#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-all-cuts-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'3925a68dfede035104669429ec03204340ec244b24257351dca0c6259442982a','provider_survey.py':'d42076bd2c967953fdaa4b8bfd7eec3666fb545522bb42b2a2f9bf30185eeae6','source-manifest.json':'a1b74ea6c5aa22c68b344f3122f6be049bec08871e245ee4b988852aabadf3da'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1;n='Sign33ForwardAllCuts';q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==rows[0]['source_sha256']=='2fabc1accbddf85f43399b1bbd9bf1efeb4cece5c550ae24fed0f3bae56767f6' and rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M) and len(rows[0]['imports'])==14
for x in ['(hgap :','(htau :','(hinner :','(hvalue :','(hnegative :','(hnorms :','d.P=1 ∧ d.Q=1 ∧ d.U=1 ∧ Carrier65.strong d=1 ∧ d.W=1','Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)','rcases hnorms with ⟨hp,hq,hu,hs,hw⟩','⟨h00, h01, h02, ⟨h03.1, h03.2, hqcut⟩','⟨hgapcut, htaucut, hpcut⟩, ⟨hwcut, hlate.1, hinnercut⟩','⟨hvaluecut, hlate.2.1, hlate.2.2⟩, ⟨hnegativecut, hucut, hscut⟩']:assert x in s
assembly=(d/'research/nine-sharing-sign33-residual-assembly-check/src/DiophantineConsistency/Sign33ResidualAssembly.lean').read_text();assert re.findall(r'^  (batch\d\d) :',assembly,re.M)==['batch00','batch01','batch02','batch03','batch04','batch05','batch06','batch07']
survey=(p/'provider_survey.py').read_text();assert '38684d452247c485eea2dade759bc7563f7ac85f04b7e9e0ec0c4b584a3d0b63' in survey
run=(p/'run.py').read_text();assert "if mod in survey['selected']" in run and "need(guard(deps)==row['direct_guard']" in run
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'conditional same-valuation 24-cut assembly proposal; no Lean replay'},indent=2,sort_keys=True))
