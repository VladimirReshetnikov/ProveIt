"""Copy already-completed review evidence into a compact dossier and inventory it."""
from pathlib import Path
import hashlib,json,runpy,shutil
BASE=Path('/workspace/shared/report67-release-independent-review-20261004');D=BASE/'dossier'
def copy(src,dst):
    dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
for n in ['CANDIDATE_AUTHENTICATION.json','FINAL_CANDIDATE_AUTHENTICATION.json','CANDIDATE_MANIFEST.json','FINAL_CANDIDATE_MANIFEST.json','INDEPENDENT_RECEIPT.json','FINAL_REPLAY_RECEIPT.json','ARCHIVE_BOUNDARY_RECEIPT.json','ORIGINALS_BEFORE.json','ORIGINALS_FINAL_AFTER.json']:
    copy(BASE/n,D/n)
copy(BASE/'owned-selftest/SELFTEST_RECEIPT.json',D/'OWNED_SELFTEST_RECEIPT.json')
copy(BASE/'hostile-full-build/BUILD_RECEIPT.json',D/'HOSTILE_ARTICLE_BUILD_RECEIPT.json')
for folder in ('full-build','relocated-full-build','final-full-build','final-relocated-build'):
    for p in sorted((BASE/folder).iterdir()):
        if p.is_file() and p.suffix in ('.json','.fls','.stdout','.txt','.log'):copy(p,D/'builds'/folder/p.name)
for p in sorted((BASE/'independent-firstpass').iterdir()):
    if p.is_file():copy(p,D/'firstpass'/p.name)
for folder in ('bootstrap','locked','omitted'):
    for p in sorted((BASE/'independent-firstpass'/folder).iterdir()):
        if p.is_file() and p.suffix in ('.json','.fls','.stdout'):copy(p,D/'firstpass'/folder/p.name)
for p in (BASE/'independent-firstpass/fixture/manuscript').iterdir():copy(p,D/'firstpass/manuscript'/p.name)
for p in (BASE/'independent-logs').glob('*.stdout'):copy(p,D/'logs'/p.name)
for p in BASE.glob('*.stdout'):copy(p,D/'logs'/p.name)
for p in (BASE/'candidate/tools').iterdir():copy(p,D/'reviewed-tools'/p.name)
copy(BASE/'candidate/README.md',D/'reviewed-readmes/original-candidate.md')
copy(BASE/'final-candidate/README.md',D/'reviewed-readmes/corrected-candidate.md')
for p in BASE.glob('*.py'):copy(p,D/'review-scripts'/p.name)
for p in BASE.glob('final-contact-*.png'):copy(p,D/'visual'/p.name)
copy(BASE/'FINAL_RASTER_DECODE_RECEIPT.json',D/'visual/FINAL_RASTER_DECODE_RECEIPT.json')
api=runpy.run_path(str(D/'verify_dossier.py'),run_name='dossier_inventory')
m={'format':'Independent Report67 release-review dossier v1',**api['inventory']()}
raw=(json.dumps(m,sort_keys=True,indent=2)+'\n').encode();(D/'DOSSIER_MANIFEST.json').write_bytes(raw)
receipt={'status':'PASS','files':len(m['files']),'directories':len(m['directories']),'bytes':sum(r['bytes'] for r in m['files'].values()),'manifest_sha256':hashlib.sha256(raw).hexdigest(),'report_sha256':hashlib.sha256((D/'REVIEW.md').read_bytes()).hexdigest()}
(BASE/'DOSSIER_PACKAGING_RECEIPT.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n');print(json.dumps(receipt))
