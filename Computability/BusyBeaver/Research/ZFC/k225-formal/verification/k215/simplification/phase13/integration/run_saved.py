"""Own canonical saved-packet reread wrapper. Does not invoke Lean or a producer."""
from pathlib import Path
import hashlib,json,subprocess,time
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');P=Path(__file__).resolve().parent
D=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase13/lean'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
files=['README.md','basis-reference.json','basis.py','packet.py','review_saved.py','execution.tar.gz','index.json','result.json'];before={n:sha(D/n) for n in files}
command=['python3','-B',str(D/'review_saved.py'),'--basis-repo',str(R),'--repo',str(R),'--output',str(P/'root-saved-review.json')]
assert not (P/'root-saved-review.json').exists();start=time.monotonic();rec={'command':command,'packet_before':before};code=1
try:
 proc=subprocess.run(command,cwd=R,capture_output=True,timeout=180);code=proc.returncode
 (P/'root-saved.stdout.txt').write_bytes(proc.stdout);(P/'root-saved.stderr.txt').write_bytes(proc.stderr)
 rec.update(exit_code=code,stdout_sha256=hashlib.sha256(proc.stdout).hexdigest(),stderr_sha256=hashlib.sha256(proc.stderr).hexdigest())
finally:
 rec.update(elapsed_seconds=time.monotonic()-start,packet_after={n:sha(D/n) for n in files},scope='Saved source/import/object-hash/log/command/current-source reader only. No compiler, producer or live-object replay.')
 rec['packet_unchanged']=rec['packet_before']==rec['packet_after'];(P/'root-saved-actual.json').write_text(json.dumps(rec,indent=2)+'\n')
assert code==0 and rec['packet_unchanged'];print('PASS root canonical saved reader',round(rec['elapsed_seconds'],2),'seconds')
