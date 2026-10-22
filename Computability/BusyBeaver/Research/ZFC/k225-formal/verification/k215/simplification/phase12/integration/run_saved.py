from pathlib import Path
import subprocess,hashlib,json,time
R=Path.cwd();P=Path('/tmp/k215-phase12-import-proposal');D=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase12/lean'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
files=['README.md','basis-reference.json','basis.py','packet.py','review_saved.py','execution.tar.gz','index.json','result.json'];before={n:sha(D/n) for n in files}
cmd=['python3','-B',str(D/'review_saved.py'),'--basis-repo',str(R),'--repo',str(R),'--output',str(P/'root-saved-review.json')];start=time.monotonic()
with (P/'root-saved.stdout.txt').open('wb') as out,(P/'root-saved.stderr.txt').open('wb') as err:r=subprocess.run(cmd,stdout=out,stderr=err)
after={n:sha(D/n) for n in files};record={'command':cmd,'exit_code':r.returncode,'elapsed_seconds':time.monotonic()-start,'packet_before':before,'packet_after':after,'packet_unchanged':before==after,'stdout_sha256':sha(P/'root-saved.stdout.txt'),'stderr_sha256':sha(P/'root-saved.stderr.txt'),'scope':'Saved source/import/object-hash/log/command/current-source reader only; no compiler, producer or live-object replay.'};(P/'root-saved-actual.json').write_text(json.dumps(record,indent=2)+'\n');assert r.returncode==0 and before==after;print('PASS root canonical saved reader',round(record['elapsed_seconds'],2),'seconds')
