"""Verify the unchanged Foundation package without writing any of its files."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[1]
FOUNDATION=ROOT/'foundation'
manifest=FOUNDATION/'SHA256SUMS'
records=[]
for line in manifest.read_text().splitlines():
    expected,relative=line.split('  ',1)
    path=FOUNDATION/relative
    actual=hashlib.sha256(path.read_bytes()).hexdigest()
    assert actual==expected, 'Foundation checksum mismatch: '+relative
    records.append({'file':relative,'sha256':actual,'status':'PASS'})
# The historical integrated mathematical receipt binds source, PDF and checks.
receipt=json.loads((FOUNDATION/'audit/mathematical-verification.json').read_text())
entries=receipt['source_files']+[receipt['delivery_pdf_identification_only'],receipt['verification_report']]+receipt['reproducibility_run']['script_files']+receipt['reproducibility_run']['recorded_json_outputs']
for entry in entries:
    assert hashlib.sha256((FOUNDATION/entry['path']).read_bytes()).hexdigest()==entry['sha256'],entry['path']
result={'status':'PASS','manifest_files_verified':len(records),'foundation_total_files_including_manifest':len(records)+1,
        'source_sha256':hashlib.sha256((FOUNDATION/'article.tex').read_bytes()).hexdigest(),
        'pdf_sha256':hashlib.sha256((FOUNDATION/'article.pdf').read_bytes()).hexdigest(),
        'manifest_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest(),
        'files':records,'operation':'Read-only integrity verification; no Foundation file was modified.'}
(ROOT/'results').mkdir(exist_ok=True)
(ROOT/'results/foundation-integrity.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: '+str(len(records)+1)+' unchanged Foundation files, including original manifest and hash-bound mathematical receipt')
