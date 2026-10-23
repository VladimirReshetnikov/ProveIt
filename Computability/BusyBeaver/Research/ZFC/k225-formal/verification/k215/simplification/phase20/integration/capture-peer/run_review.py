from pathlib import Path
import hashlib,json,subprocess,time
D=Path('/tmp/k215-phase20-capture-peer');helper=D/'review_capture_v1.py'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(helper)=='f98babca3d416e0da76f263d468472ffe677f778617cc9fa5e17952e59ee9502'
assert sha('/tmp/k215-phase20-publication-capture/evidence.tar.gz')=='ad907b9e29a3a7e0453540c34d3480ee6bce84ecb660e4470b1ad03d89dfb075'
argv=['python3','-B',str(helper),'--packet','/tmp/k215-phase20-publication-capture','--config','/tmp/k215-phase20-publication-config/capture-config.json','--config-sha','4c731d0736d617aa041bc54c4ccbaf8db78c0260211a0ffa1cbeabd83ab75533','--capture-helper-sha','737507a8bff5d660662a599ffb2db6266a7381ac10f5f4bca0b07cca54f05d82','--output',str(D/'actual-review-v1.json')]
t=time.monotonic()
with (D/'actual-review-v1.stdout').open('xb') as out,(D/'actual-review-v1.stderr').open('xb') as err:r=subprocess.run(argv,stdout=out,stderr=err)
receipt=dict(status='PASS_EXIT_ZERO' if r.returncode==0 else 'FAIL',exit_code=r.returncode,seconds=time.monotonic()-t,argv=argv,helper_sha256=sha(helper),stdout_sha256=sha(D/'actual-review-v1.stdout'),stderr_sha256=sha(D/'actual-review-v1.stderr'),launcher_sha256=sha(__file__))
with (D/'actual-review-v1.outer.json').open('x') as out:json.dump(receipt,out,indent=2);out.write('\n')
print(json.dumps(receipt));raise SystemExit(r.returncode)
