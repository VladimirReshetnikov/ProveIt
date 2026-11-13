#!/usr/bin/env python3
"""Isolated historical-input finite audit replay, never modifies repository inputs."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import hashlib,json,os,subprocess
from pathlib import Path
INPUTS = {
    'Lean/DiophantineConsistency/CarrierNormalizedProduct106.lean': ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/normalized106-degree-audit-drift/historical-CarrierNormalizedProduct106.lean', 'efaa7ff2df3751b00cae602aaf17c6e3140c568c6bee956fa7a28fda6596e46f'),
    'Lean/DiophantineConsistency/CarrierNormalizedProduct106Checks.lean': ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CarrierNormalizedProduct106Checks.lean', 'e269c855713dbb0badc9b11f276a9cdb5b068f6ea364d2b401f2122f6ee7b0c6'),
    'Lean/DiophantineConsistency/CarrierScaledAuxiliary118.lean': ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/normalized106-degree-audit-drift/historical-CarrierScaledAuxiliary118.lean', '2e222efd3b40626e6734fe30e5b7239fb7a7abd5fd9c14bee8e4a238c237c620'),
    'research/fourteen-nonzero-spheres/polynomial71.json': ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/fourteen-nonzero-spheres/polynomial71.json', '937752350556a94539584db8f646ff9e02d25a7113e6d4af70ac22c1b1e01ad2'),
    'research/fourteen-normalized-product106/CERTIFICATE.json': ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/fourteen-normalized-product106/CERTIFICATE.json', '16358ce2d453371d2f2d1cad8ab22136ea61ec9ff77200a55264ad56d4a57879'),
    'research/fourteen-normalized-product106/PROOF.md': ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/fourteen-normalized-product106/PROOF.md', '751910f2c2c24681fab32413e43c70f51e4157fb68bf3fd1cd6a06198b899883'),
    'research/fourteen-normalized-product106/audit.py': ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/fourteen-normalized-product106/audit.py', '7c4adcc2955d589ef1e1af39260c89d24ed6673c9e32b811af4fe5a35bba6bbd'),
    'research/fourteen-normalized-product106/coefficients/K.bin.gz': ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/fourteen-normalized-product106/coefficients/K.bin.gz', 'cfc3229f5281580358370e198b433936161b732a7229a1f8dc4f8839a701f4ab'),
    'research/fourteen-normalized-product106/coefficients/MC.bin.gz': ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/fourteen-normalized-product106/coefficients/MC.bin.gz', 'b178777ae605e6d0073c824c48237e89e9b28911a2583bce7c6689a50ce3cdfd'),
    'research/fourteen-normalized-product106/coefficients/MF_source.bin.gz': ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/fourteen-normalized-product106/coefficients/MF_source.bin.gz', 'f04d074f8413c49581f262bcbb030c616f00745935010afc0d30050771627c3a'),
    'research/fourteen-normalized-product106/coefficients/beta.bin.gz': ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/fourteen-normalized-product106/coefficients/beta.bin.gz', 'a94c07b25b9c185fa920d5c76ab04ea4de69b0a6a439995cf5ee390be225c719'),
    'research/fourteen-normalized-product106/polynomial.json': ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/fourteen-normalized-product106/polynomial.json', '0485cd1e884b918d766261b1780be117238f0813a965c6d8ae4d805176a5f6e1'),
    'research/padding-staircase-independent/PROOF.md': ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/padding-staircase-independent/PROOF.md', '69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8'),
    'research/padding-staircase-independent/certificate.json': ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/padding-staircase-independent/certificate.json', 'fae49c56a9c57d394335c8a47da395f000a0c25cb8267d1330104eddbbc7850f'),
    'research/padding-staircase-independent/coefficients.json': ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/padding-staircase-independent/coefficients.json', '43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93'),
    'research/scaled-auxiliary118/polynomial.json': ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/scaled-auxiliary118/polynomial.json', '588f295e6d965ff5f7b78deda02b808575aaf818908af528a738a98ecda5c72f'),
}
ROOT=Path('/tmp/normalized106-historical-finite-replay-20261105')
EXPECTED_CERT='16358ce2d453371d2f2d1cad8ab22136ea61ec9ff77200a55264ad56d4a57879'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,m):
    if not v:raise RuntimeError(m)
need(not os.path.lexists(ROOT),'output root already exists')
ROOT.mkdir(mode=0o700)
for dst,(src,expected) in INPUTS.items():
    source=Path(src);need(source.is_file() and sha(source)==expected,'source mismatch '+src)
    target=ROOT/dst;target.parent.mkdir(parents=True,exist_ok=True)
    with target.open('xb') as out:out.write(source.read_bytes())
    need(sha(target)==expected and sha(source)==expected,'copy drift '+src)
source_digests={src:sha(Path(src)) for src,_ in INPUTS.values()}
cmd=['/usr/bin/nice','-n','19',sys.executable,'-I','-S','-B','audit.py']
try:
    child=subprocess.run(cmd,cwd=ROOT/'research/fourteen-normalized-product106',capture_output=True,timeout=120,check=False)
    code=child.returncode;stdout=child.stdout;stderr=child.stderr;reason=None
except subprocess.TimeoutExpired as exc:
    code=None;stdout=exc.stdout or b'';stderr=exc.stderr or b'';reason='120-second timeout'
(ROOT/'stdout').write_bytes(stdout);(ROOT/'stderr').write_bytes(stderr)
stable=all(sha(Path(src))==expected and sha(ROOT/dst)==expected for dst,(src,expected) in INPUTS.items())
try:out=json.loads(stdout)
except Exception:out={}
passed=(code==0 and reason is None and stable and stderr==b'' and out.get('status')=='PASS' and
        out.get('operations')==67 and out.get('degree')==106 and out.get('variables')==14 and
        out.get('certificate_sha256')==EXPECTED_CERT)
result={'status':'PASS' if passed else 'FAILED','command':cmd,'exit':code,'reason':reason,
        'root':str(ROOT),'inputs':{dst:{'source':src,'sha256':expected} for dst,(src,expected) in INPUTS.items()},
        'inputs_stable':stable,'stdout_sha256':sha(ROOT/'stdout'),'stderr_sha256':sha(ROOT/'stderr'),
        'certificate_sha256':EXPECTED_CERT,'auditor_report':out,
        'scope':'isolated historical-source finite audit; no current-source replay, no Lean or PDF proof'}
(ROOT/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result,sort_keys=True))
if not passed:raise SystemExit(1)
