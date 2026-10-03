#!/bin/sh
# Trusted bootstrap: fixed inventory and payload pins before any packaged helper.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec python3 -I -B - "$ROOT" "$@" <<'PREFLIGHT'
from pathlib import Path, PurePosixPath
import hashlib, json, re, subprocess, sys
root=Path(sys.argv[1]).resolve()
args=sys.argv[2:]
REQUIRED = ('README.md', 'build.sh', 'figures/make_figures.py', 'figures/visited-geometry.pdf', 'replay.py', 'report30.pdf', 'report30.tex', 'reproduce.sh', 'scientific/examples/REVIEW.md', 'scientific/examples/independent-audit.py', 'scientific/first-visit/MANIFEST.sha256', 'scientific/first-visit/PROOF.md', 'scientific/first-visit/README.md', 'scientific/first-visit/audit-results-optimized.json', 'scientific/first-visit/audit-results.json', 'scientific/first-visit/audit.py', 'scientific/first-visit/independent-review.md', 'scientific/geometry/MANIFEST.sha256', 'scientific/geometry/PROOF.md', 'scientific/geometry/README.md', 'scientific/geometry/audit-results-optimized.json', 'scientific/geometry/audit-results.json', 'scientific/geometry/audit.py', 'scientific/geometry/counting-review.md', 'scientific/original-frame/PROOF.md', 'scientific/original-frame/REVIEW.md', 'tamper_regression.py', 'verification/expected-examples.json', 'verification/expected-first-visit.json', 'verification/expected-geometry.json', 'verification/source-lineage.json')
PINNED = {'README.md': '322c16025cae91f0a9458b3da93ebc28c8632b9e09eb75d9ac2e6672212bf9e8', 'build.sh': '624661a0d3851384b4acb3fe99d6feca345e831f2ab1bb3fcb89d7fa832c42e3', 'figures/make_figures.py': '581a9168e3c14ac1327f910834a493060c7b3c850f5a06847aca4207e58f8eca', 'figures/visited-geometry.pdf': '29c9478463616823751b7202d4321252d57e519191dad2c90209d2d689a99f7c', 'replay.py': 'b56882687f0a216a93ec1658d35e2e78c6a0e976e69c8139acb01faa445737ec', 'report30.pdf': '6aaa34f0dc034110fa5736c149e6bada386ed20f4d9fbe62653dad0b58968bec', 'report30.tex': '0723338c7bafb6f9bf977ac276793564f789dbb73f46b5cef77838b895fcf4dd', 'scientific/examples/REVIEW.md': '01c4a17969d970b2badb1ac35c42f2d9a1c4df124c81f62e289aa65b2e0481a4', 'scientific/examples/independent-audit.py': '8d04266904bac6642065f5e474ddd7b6ea3b89beac741b17a76f2de5b444c093', 'scientific/first-visit/MANIFEST.sha256': '287ffeb198da5a704db2c150a0e015b8b038ab0342a8c754480968db346874a3', 'scientific/first-visit/PROOF.md': '3247951ca7afa4d65bd3eb90d99bfb48fcb43dbf0eaa067c3e9380cdfbcebbda', 'scientific/first-visit/README.md': '4ca2dad788f32dfff5d23040c4815eec1be22113eb71456ca99d4e4c2e8fff43', 'scientific/first-visit/audit-results-optimized.json': '92e50968fd64f016096201aa4c1b6efef1919b7c60b0c4b6df371bafd8fa03e1', 'scientific/first-visit/audit-results.json': '92e50968fd64f016096201aa4c1b6efef1919b7c60b0c4b6df371bafd8fa03e1', 'scientific/first-visit/audit.py': 'bcf5f56bc932f95b8a866beb32d6c22cbccaf063de687caa5bd5c2b332b5bfc2', 'scientific/first-visit/independent-review.md': '3a4555dd780c6b677f8bb5ca4df71c2f5ac7d74822649d096e44c4060b588b8a', 'scientific/geometry/MANIFEST.sha256': '408805ec804fc56c30b9d21c22b4aa4a96630a5acb4879943137052930dfcb16', 'scientific/geometry/PROOF.md': '3f05b484cd3c0035422df431f571bb2b56c85a31d5f49ae681033ffb2ca6e4fa', 'scientific/geometry/README.md': 'a173a1471a416e7ff69a17636c0dd3e6a3cf3f4052be1a20221c1a640a2ea735', 'scientific/geometry/audit-results-optimized.json': '4663a73b6d198ea271f40b30308bedb71dc6b399c27244c06bdfdc640d4569fc', 'scientific/geometry/audit-results.json': '4663a73b6d198ea271f40b30308bedb71dc6b399c27244c06bdfdc640d4569fc', 'scientific/geometry/audit.py': '9baf8b72474b2904f3cb3989eda959a505e9772721bfe76537445536d943e6a9', 'scientific/geometry/counting-review.md': '27a50b857d4a26ce21e24cac27694ff4a2addef049d027c9ccce52c20b49bf39', 'scientific/original-frame/PROOF.md': '385c455537ee7c4631fd5400918b57602bc08c26383fe71f99b3345791964a8f', 'scientific/original-frame/REVIEW.md': '9fdcf0ce8911823089e05e56d236ab2b15064878f82c19c9a2d0e94b0611fbd5', 'tamper_regression.py': '934a536c181f6c0b93d51415a6232120746dc644dbd69890db3ce4ba8f681590', 'verification/expected-examples.json': '5d43767bcae7ffc8b8d1f512efacaf8c4967c8ecf962b5136f219187f76e880a', 'verification/expected-first-visit.json': '92e50968fd64f016096201aa4c1b6efef1919b7c60b0c4b6df371bafd8fa03e1', 'verification/expected-geometry.json': '4663a73b6d198ea271f40b30308bedb71dc6b399c27244c06bdfdc640d4569fc', 'verification/source-lineage.json': '136f9ced03d99314b34f5fba69bbab178aa9264c3dc477322c6a4a4155e56de7'}

def reject(message):
    raise SystemExit('Preflight rejected: '+message)
if not ((len(args)==1 and args[0]=='--verify-only') or (len(args)==2 and args[0]=='--output-dir')):
    reject('Use --verify-only or --output-dir EXTERNAL_DIRECTORY')
actual=set()
for p in root.rglob('*'):
    if p.is_symlink():
        reject('symlink payload')
    if p.is_file():
        actual.add(p.relative_to(root).as_posix())
if actual!=set(REQUIRED)|{'SHA256SUMS'}:
    reject('required inventory mismatch: '+str(sorted(actual^(set(REQUIRED)|{'SHA256SUMS'}))))
expected={}
for line in (root/'SHA256SUMS').read_text(encoding='ascii').splitlines():
    try:
        digest,name=line.split('  ',1)
    except ValueError:
        reject('invalid manifest syntax')
    path=PurePosixPath(name)
    if not re.fullmatch('[0-9a-f]{64}',digest) or path.is_absolute() or '..' in path.parts or str(path)!=name or name in expected:
        reject('invalid manifest entry')
    expected[name]=digest
if set(expected)!=set(REQUIRED):
    reject('manifest inventory differs from fixed required payloads')
for name in REQUIRED:
    digest=hashlib.sha256((root/name).read_bytes()).hexdigest()
    if digest!=expected[name]:
        reject('manifest digest mismatch: '+name)
    if name in PINNED and digest!=PINNED[name]:
        reject('independent pin mismatch: '+name)
print('Preflight PASS: fixed inventory, manifest, and pinned payloads',flush=True)
if args==['--verify-only']:
    raise SystemExit(0)
out=Path(args[1]).resolve()
if out==root or root in out.parents:
    reject('output directory must be external')
subprocess.run([sys.executable,'-I','-B',str(root/'replay.py'),*args],check=True)
done=subprocess.run([sys.executable,'-I','-B',str(root/'tamper_regression.py')],text=True,capture_output=True,check=True)
result=json.loads(done.stdout)
if type(result) is not dict or result.get('status')!='PASS' or type(result.get('cases')) is not dict or len(result['cases'])!=6:
    reject('tamper regression receipt failed')
(out/'tamper-regression.json').write_text(done.stdout)
print(done.stdout,end='')
print('Replay PASS: isolated normal and optimized science; six preflight tamper cases')
PREFLIGHT
