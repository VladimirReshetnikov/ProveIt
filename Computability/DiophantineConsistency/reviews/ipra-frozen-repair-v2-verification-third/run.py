#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,subprocess,sys
D=Path(__file__).resolve().parent;V=D.parent;A=Path('/tmp/ipra-frozen-ancestry-repair-5_g68wg3');B=Path('/tmp/ipra-frozen-ancestry-repair-6ftdeyrq');PLAN=V/'ipra-frozen-repair-plan-v2';h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();paths=[D/'compare.py',Path(__file__)];before={str(p):h(p) for p in paths};log=D/'run.log'
with log.open('w') as out:r=subprocess.run([sys.executable,str(D/'compare.py'),str(PLAN),str(A),str(B)],stdout=out,stderr=subprocess.STDOUT)
after={str(p):h(p) for p in paths};terminal={'status':'FAIL','exit_code':r.returncode,'before':before,'after':after,'log_sha256':h(log)}
if r.returncode==0 and before==after and (D/'receipt.json').is_file():
 terminal['receipt_sha256']=h(D/'receipt.json');terminal['author_receipt_sha256']=h(V/'ipra-frozen-repair-v2-verification/receipt.json')
 if terminal['receipt_sha256']==terminal['author_receipt_sha256']:terminal['status']='PASS_EXIT_0'
(D/'terminal.json').write_text(json.dumps(terminal,sort_keys=True,indent=2)+'\n');print(terminal['status'],flush=True)
if terminal['status']!='PASS_EXIT_0':raise SystemExit(1)
