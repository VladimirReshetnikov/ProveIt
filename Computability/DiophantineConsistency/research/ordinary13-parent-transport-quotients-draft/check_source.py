from pathlib import Path
import hashlib,json,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'ParentTransportQuotients.lean').read_text()
for t in ('ParentScaledNormsDraft.scaled_norms','quotients_of_scaled_norms','quotients_force_transport','quotient_transport','positive_Y_quotient_of_facts','P88FourSquare.graph'):assert t in s
r=D/'research/ordinary13-parent-scaled-norms-draft';x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
print(json.dumps({'scope':'same-parent-zero source interface composition, no Lean','lean_run':False,'source_sha256':hashlib.sha256((p/'ParentTransportQuotients.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
