"""Finalize presentation acceptance after independent reviews.
No scientific executable is imported or run; copied review metadata is preserved.
"""
from pathlib import Path
import difflib,hashlib,json,stat
R=Path('/workspace/shared/report69-low-arity-compilers-release-20261004')
def sha(b):return hashlib.sha256(b).hexdigest()
def enc(x):return (json.dumps(x,sort_keys=True,indent=2)+'\n').encode()
def require(x,m):
 if not x:raise ValueError(m)
def inv(root):
 result={}
 for p in [root,*sorted(root.rglob('*'))]:
  s=p.lstat();require(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode),'Nonregular copy')
  row={'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns,'kind':'directory' if p.is_dir() else 'file'}
  if p.is_file():
   require(s.st_nlink==1,'Hardlinked copy');b=p.read_bytes();row.update(bytes=len(b),sha256=sha(b))
  result[p.relative_to(root).as_posix()]=row
 return result
copies={}
for name,origin in [('manuscript-review','/workspace/shared/report69-independent-manuscript-review-20261004'),('release-tool-review','/workspace/shared/report69-independent-release-tool-review-20261004/dossier')]:
 a=inv(Path(origin));b=inv(R/'qa'/name);require(a==b,'Review copy mismatch');copies[name]={'origin':origin,'entries':len(a),'status':'PASS','bytes_modes_mtimes_equal':True}
tooldir=R/'qa/release-tool-review';raw=(tooldir/'DOSSIER_MANIFEST.json').read_bytes()
require(sha(raw)=='0e04a01fb4e3becef0cc7ff7c4e88fa2f51522ce7de0b932ab604ad827c52d18','Tool dossier manifest pin')
m=json.loads(raw)
for name,row in m['files'].items():
 b=(tooldir/name).read_bytes();require({'bytes':len(b),'sha256':sha(b)}==row,'Tool dossier member')
require({p.relative_to(tooldir).as_posix() for p in tooldir.rglob('*') if p.is_file()}=={'DOSSIER_MANIFEST.json',*m['files']},'Tool dossier coverage')
pins={'Report69.pdf':'fc0db742d499ee0e515700134460f78b44d3c7301f14c63c77cfa6fb9a6686ce','Report69.tex':'9f0508066f9354b6c7d74b4d6b8a10498e632e5e31b149ff8312ffb75f82cfd0','manuscript/MANUSCRIPT_PINS.json':'38b3f7a8a3bb1f837ace42df35edffd8d7627d3af476f4869106903e31824e4c','tools/release69.py':'cf70098ca75442d0e7868bf63fe03a15f80694895aa2ffe660d16f67c4ed3807','tools/build_report69.py':'16074885d6203a09cbcc448478d4d4cbfb4ac91c36c018963da793d08194e2cb','tools/selftest69.py':'c3beaf2f18090c851ead535239e6ef91964a3241bce11ea8004f980f9cd326f4','tools/BUILD_DEPENDENCIES_LOCK.json':'62d196ba3a660790910afa4ac4eb83f1410b8b64e6a401ad52d1388ee812f3f5'}
for name,pin in pins.items():require(sha((R/name).read_bytes())==pin,'Accepted principal pin changed: '+name)
readme=R/'README.md';before=readme.read_text()
old="The owner inspected all final page images and corrected the initial overfull source-path line and two small layout issues before the final render. The exact locked packaged-PDF replay and all 39 owned synthetic tests passed. The independent mathematical-transcription/page review and release-tool review are in progress at this candidate stage; their accepted final dossiers will replace this status before sealing. A fresh root terminal verification is performed separately after the final archive is sealed, so its later receipt is not claimed to be inside that archive."
new="The complete 17-page manuscript and every page image passed independent mathematical-transcription and visual review without a required correction; the accepted dossier is in `qa/manuscript-review/`. The exact locked packaged-PDF replay and all 39 owned synthetic tests passed. The independent release-tool review passed 117 adversarial checks, 12 additional build probes and 12 full-candidate checks, including relocated PDF and all-page byte equality; its compact accepted dossier is in `qa/release-tool-review/`. One filesystem-socket probe was unavailable because the environment denied socket creation; its authentic interrupted log is retained and the separate FIFO and socket-typed ZIP checks passed. Bulky duplicate test archives, copied candidate trees and synthetic fixture payloads remain external and are hash-indexed by the review dossier, rather than being claimed as included. The release owner separately accepted all 17 v5 pages and both complete reviews. A fresh post-seal terminal verification is recorded separately after the final archive is sealed, so its later receipt is not claimed to be inside that archive."
require(before.count(old)==1,'Expected acceptance-only README update')
after=before.replace(old,new);readme.write_text(after)
(R/'qa/README_ACCEPTANCE_ONLY.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='independently-reviewed-candidate/README.md',tofile='final-release/README.md')))
(R/'qa/REVIEW_COPY_VERIFICATION.json').write_bytes(enc({'status':'PASS','copies':copies,'tool_dossier_payloads':len(m['files'])}))
(R/'qa/REVIEW_ACCEPTANCE.json').write_bytes(enc({'status':'PASS','mathematical_audit_manifest_sha256':'6852625bc450563eeda5ad96956e3ac18da64b95ca446c654da14f3b978594b3','manuscript_review_manifest_sha256':'c761cc1e28f5e62f20f8a212566f9a81b4382e4dedbaec2ad4f6678f74388a4c','release_tool_dossier_manifest_sha256':sha(raw),'tool_review_sha256':'ad4baabbcc0c077745ddce783da023d73782a51f838ee83fe80ec0293cfe580f','principal_pins':pins,'owned_tests':39,'independent_adversarial_passes':117,'unavailable_os_socket_probe':1,'independent_build_probes':12,'independent_full_candidate_checks':12,'required_tool_or_manuscript_corrections':[],'inspections':'Individual model-performed page reviews; not human visual inspection','root_owner_acceptance':'Owner confirmed all 17 v5 pages, complete manuscript review, complete scientific proofs/audit and complete tool review before seal; later terminal gate remains separate','terminal_verification_in_archive':False}))
(R/'qa/RELEASE_PREPARATION.json').write_bytes(enc({'status':'PASS','science_executed':False,'accepted_primary_bytes_unchanged':True,'readme_change':'Acceptance paragraph only','readme_before_sha256':sha(before.encode()),'readme_after_sha256':sha(after.encode()),'tool_dossier_files_excluding_manifest':len(m['files'])}))
print('Accepted reviews retained; README acceptance-only update and principal pins verified')
