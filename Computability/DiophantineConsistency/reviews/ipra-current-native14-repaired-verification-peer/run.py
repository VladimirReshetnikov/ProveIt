#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,subprocess,sys
D=Path(__file__).resolve().parent;V=D.parent;A=Path('/tmp/ipra-current-native14-fixed-axt06pi5');B=Path('/tmp/ipra-current-native14-fixed-kgvq8602');h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();paths=[D/'compare.py',Path(__file__).resolve()];before={str(p):h(p) for p in paths};log=D/'run.log'
with log.open('w') as out:r=subprocess.run([sys.executable,str(D/'compare.py'),str(A),str(B)],stdout=out,stderr=subprocess.STDOUT)
after={str(p):h(p) for p in paths};terminal={'status':'FAIL','exit_code':r.returncode,'before':before,'after':after,'log_sha256':h(log)}
if r.returncode==0 and before==after and (D/'receipt.json').is_file():
 terminal['receipt_sha256']=h(D/'receipt.json');terminal['author_receipt_sha256']=h(V/'ipra-current-native14-repaired-verification/receipt.json')
 if terminal['receipt_sha256']==terminal['author_receipt_sha256'] and log.read_text()=='MATCHED_PASS 6 rows 7821 files\n':terminal['status']='PASS_EXIT_0'
(D/'terminal.json').write_text(json.dumps(terminal,sort_keys=True,indent=2)+'\n');print(terminal['status'],flush=True)
if terminal['status']!='PASS_EXIT_0':raise SystemExit(1)
