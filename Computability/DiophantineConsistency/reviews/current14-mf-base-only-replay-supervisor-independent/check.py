#!/usr/bin/env python3
"""No-Lean source, evidence-pin and synthetic-control review of replay supervisor."""
import hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[4];task=root/'Computability/DiophantineConsistency';p=task/'research/current14-mf-base-only-endpoint-replay';orig=task/'research/current14-mf-base-only-endpoint-attempt02'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
need(sha(p/'supervisor.py')=='d1a61a05bd815afb109155be4985dedba39a15cece37a425e8e1fe88947169fa','supervisor pin')
need(sha(p/'runner.py')=='988112f6ab8585dfa7eff62ce22d615d7faefa593eea1978b7d071ee638ed0ed','runner pin')
for x in ('Current14LiteralPortsMF.lean','StructuredEndpointMF.lean'):need((p/x).read_bytes()==(orig/x).read_bytes(),'client source differs')
a=(orig/'runner.py').read_text();b=(p/'runner.py').read_text();need(a.replace('/tmp/current14-mf-base-only-attempt02-20261104','/tmp/current14-mf-base-only-replay-20261104')==b,'runner changes exceed output path')
spec=importlib.util.spec_from_file_location('replay_supervisor',p/'supervisor.py');s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s);s.pin()
obs=s.read(s.FIRST_PACKET/'terminal-observation.json');audit=s.read(s.FIRST_AUDIT);ae=s.read(s.FIRST_AUDIT_EXEC);first=s.read(s.FIRST/'state.json')
s.check_first_evidence(obs,audit,ae,first,sha(s.FIRST/'state.json'),sha(s.FIRST_AUDIT_SCRIPT))
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'controls.py')],stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=60)
need(r.returncode==0 and json.loads(r.stdout)['status']=='PASS','synthetic controls')
print(json.dumps({'status':'PASS','supervisor_sha256':sha(p/'supervisor.py'),'runner_sha256':sha(p/'runner.py'),'controls_sha256':sha(p/'controls.py'),'review_script_sha256':sha(__file__),'scope':'Source/pin and synthetic controls, no Lean and no replay success claim.'},sort_keys=True))
