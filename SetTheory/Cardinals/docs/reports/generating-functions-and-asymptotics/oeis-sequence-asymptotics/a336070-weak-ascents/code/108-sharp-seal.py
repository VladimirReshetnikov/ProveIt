#!/usr/bin/env python3
"""Create a deterministic integrity manifest and source/checks ZIP after validation."""
from hashlib import sha256
import json
from pathlib import Path
from zipfile import ZipFile, ZipInfo, ZIP_DEFLATED
from verify_package import ROOT, payload_paths, require, verify

paths = payload_paths()
require(all(p.is_file() and not p.is_symlink() for p in paths), 'Payload incomplete')
qa = json.loads((ROOT/'validation/quality_review.json').read_text())
require(qa['status']=='passed' and qa['pages_reviewed']==list(range(1,25)), 'Visual review is incomplete')
require(qa['pdf_sha256']==sha256((ROOT/'report108.pdf').read_bytes()).hexdigest(), 'Visual review refers to a different PDF')
proof = json.loads((ROOT/'validation/proof_review.json').read_text())
require(proof['weighted_sharp_audit']=='passed' and proof['fixed_d_sharp_audit']=='passed', 'Analytic audit gate not passed')
require(proof['article_tex_sha256']==sha256((ROOT/'report108.tex').read_bytes()).hexdigest(), 'Proof review refers to a different TeX article')
parts=sorted((ROOT/'source').glob('[0-9][0-9]_*.tex'))
assembled=''.join(p.read_text(encoding='utf-8').rstrip()+'\n\n' for p in parts)
require(assembled==(ROOT/'report108.tex').read_text(), 'Source sections differ from assembled TeX')
campaign=json.loads((ROOT/'checks/corruption_results.json').read_text())
require(campaign['status']=='passed' and campaign['weak_campaign_rerun'] is True, 'Complete exact corruption campaign missing')
require(campaign['combined_independent_mutations']==72 and campaign['combined_failed_corrupt_runs']==144, 'Mutation coverage gate differs')
standalone=json.loads((ROOT/'checks/standalone_replay.json').read_text())
require(standalone['status']=='passed' and standalone['original_input_files_unchanged'] is True, 'Standalone exact replay incomplete')
rows=[]
for p in paths:
    data=p.read_bytes()
    rows.append({'path': p.relative_to(ROOT).as_posix(), 'bytes': len(data), 'sha256': sha256(data).hexdigest()})
manifest={'schema':'report108-sha256-v1', 'scope':'Self-contained article, final PDF, exact finite checks, scripts, and validation records. The manifest is not self-hashed.', 'files':rows}
(ROOT/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
verify()
archive=ROOT/'report108_source_checks.zip'
with ZipFile(archive,'w',compression=ZIP_DEFLATED,compresslevel=9) as z:
    for p in sorted(paths+[ROOT/'manifest.json'],key=lambda p:p.relative_to(ROOT).as_posix()):
        info=ZipInfo('report108/'+p.relative_to(ROOT).as_posix(),date_time=(2026,10,2,0,0,0))
        info.create_system=3; info.compress_type=ZIP_DEFLATED
        info.external_attr=(0o100755 if p.suffix=='.sh' else 0o100644)<<16
        z.writestr(info,p.read_bytes(),compress_type=ZIP_DEFLATED,compresslevel=9)
summary=[]
for name in ('report108.tex','report108.pdf','manifest.json','report108_source_checks.zip'):
    summary.append(f'{sha256((ROOT/name).read_bytes()).hexdigest()}  {name}')
(ROOT/'FINAL_SHA256.txt').write_text('\n'.join(summary)+'\n')
print('\n'.join(summary))
