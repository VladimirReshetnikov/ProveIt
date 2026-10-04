"""Seal and relocate only an external authenticated updated candidate copy."""
from pathlib import Path
import json,runpy,shutil,subprocess,sys
BASE=Path('/workspace/shared/report67-release-independent-review-20261004')
I=runpy.run_path(str(BASE/'auth_snapshot.py'));inv,sha,enc=I['inventory'],I['sha'],I['encoded']
source=BASE/'final-candidate';before=inv(source);root=BASE/'final-sealed';shutil.copytree(source,root,copy_function=shutil.copy2)
s=inv(root);m={'format':'Report67 release manifest v1','files':s['files'],'directories':s['directories']};raw=enc(m);pin=sha(raw)
(root/'RELEASE_MANIFEST.json').write_bytes(raw);(BASE/'FINAL_CANDIDATE_MANIFEST.json').write_bytes(raw)
results=[]
def cmd(label,root,tool,args):
    before=inv(root)
    c=subprocess.run([sys.executable,'-I','-S','-B',str(root/'tools'/tool),*args],stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
    (BASE/(label+'.stdout')).write_bytes(c.stdout);assert c.returncode==0,(label,c.stdout[-2000:]);assert inv(root)==before
    results.append({'name':label,'status':'PASS','source_preserved':True})
cmd('final-candidate-verify',root,'release67.py',['verify','--manifest-sha256',pin])
for suffix in ('a','b'):cmd('final-archive-'+suffix,root,'release67.py',['archive','--manifest-sha256',pin,'--output',str(BASE/('final-'+suffix+'.zip'))])
assert (BASE/'final-a.zip').read_bytes()==(BASE/'final-b.zip').read_bytes()
relocated=BASE/'final-relocated'
cmd('final-extraction',root,'release67.py',['extract','--manifest-sha256',pin,'--archive',str(BASE/'final-a.zip'),'--output-dir',str(relocated)])
r=inv(relocated);assert r['directories']==m['directories'];assert {n:v for n,v in r['files'].items() if n!='RELEASE_MANIFEST.json'}==m['files']
cmd('final-relocated-verify',relocated,'release67.py',['verify','--manifest-sha256',pin])
cmd('final-relocated-build',relocated,'build_report67.py',['--output-dir',str(BASE/'final-relocated-build'),'--pins-sha','99a8beb275e70e66aa4426f1497ccad79a2a4ed13617cce7e6d912ec98a11656','--dependency-lock-sha','924a24fab30a2e05eccd168d7951273e31b99a8adbb3290ab5d8b6f332b884e1','--require-packaged-match'])
expected='20ef1b64f4a87496bd6c64a72cb760d9d555f4d0d459f84b57cdfd910e1dd800'
assert sha((BASE/'final-full-build/Report67.pdf').read_bytes())==sha((BASE/'final-relocated-build/Report67.pdf').read_bytes())==expected
for folder in ('final-full-build','final-relocated-build'):
    assert (BASE/folder/'BUILD_DEPENDENCIES.json').read_bytes()==(source/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes()
    assert json.loads((BASE/folder/'PAGE_INVENTORY.json').read_bytes())==json.loads((BASE/'final-full-build/PAGE_INVENTORY.json').read_bytes())
assert inv(source)==before
orig=json.loads((BASE/'ORIGINALS_BEFORE.json').read_bytes());after={p:inv(Path(p)) for p in orig};assert orig==after
(BASE/'ORIGINALS_FINAL_AFTER.json').write_bytes(enc(after))
receipt={'status':'PASS','scope':'Updated presentation candidate review seal, not final author release seal','candidate_manifest_sha256':pin,'pdf_sha256':expected,'archive_sha256':sha((BASE/'final-a.zip').read_bytes()),'files':len(m['files']),'directories':len(m['directories']),'tests':results,'exact_relocated_pdf_match':True,'exact_page_raster_match':True,'source_snapshot_preserved':True,'seven_original_roots_preserved':True,'script_sha256':sha(Path(__file__).read_bytes())}
(BASE/'FINAL_REPLAY_RECEIPT.json').write_bytes(enc(receipt));print(enc(receipt).decode())
