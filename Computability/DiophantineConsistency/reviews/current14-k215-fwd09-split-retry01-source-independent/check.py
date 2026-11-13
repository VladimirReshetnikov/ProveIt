from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];old=root/'research/current14-k215-fwd09-split-draft';new=root/'research/current14-k215-fwd09-split-retry01-draft'
for n in ('KSource215Fwd09Left.lean','KSource215Fwd09Right.lean'):assert (old/n).read_bytes()==(new/n).read_bytes()
a=(old/'KSource215FwdCheck09.lean').read_text();b=(new/'KSource215FwdCheck09.lean').read_text();line='  rw [fwd9Left_ok, fwd9Right_ok]\n';assert a.count(line)==1 and b==a.replace(line,line+'  rfl\n');assert hashlib.sha256((new/'KSource215FwdCheck09.lean').read_bytes()).hexdigest()=='c9ce44de31026b69f22b78380468c18eb359e925fbaf3c9769a369a83f4e0e9a'
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-fwd09-split-failure-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_SOURCE_DELTA_REVIEW','lean_run':False,'scope':'Only rfl added after rewrites; split join uncompiled'},indent=2))
