#!/usr/bin/env python3
"""Independent inert log/recorder, byte replay and archive audit; executes no supplied code."""
import hashlib,json,os,stat,zipfile
from pathlib import Path
D=Path('/workspace/shared/oeis-uniform-sectors-tools-review-20261004')
R=Path('/workspace/shared/oeis-uniform-sectors-release-20261004')
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def get(p):return json.loads(p.read_bytes())
def enc(v):return (json.dumps(v,indent=2,sort_keys=True)+'\n').encode()
def inventory(root):
 files,dirs={},{}
 for p in sorted(root.rglob('*')):
  s=p.lstat();need(stat.S_ISDIR(s.st_mode) or stat.S_ISREG(s.st_mode),'nonregular restored object');n=p.relative_to(root).as_posix();r={'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns}
  if stat.S_ISDIR(s.st_mode):dirs[n]=r
  elif n!='RELEASE_MANIFEST.json':b=p.read_bytes();files[n]={**r,'bytes':len(b),'sha256':sha(b)}
 return {'files':files,'directories':dirs}
pins={'article.tex':'d0770c2f36b214204b13f7487f3d7299b2da96844de47f954cd717f5f78b3191','manuscript/article.tex':'d0770c2f36b214204b13f7487f3d7299b2da96844de47f954cd717f5f78b3191','article.pdf':'e1689dc2ba86b8a1c01ac33897007bcafa3e6454f197b87920e56af87235b1df','manuscript/MANUSCRIPT_PINS.json':'10ddbdee2fc822c63b437b3e4b84c57717d3ed7934f63aa05952f0e1aac19164','tools/BUILD_DEPENDENCIES_LOCK.json':'6ee7f579ad072c7c57d76341d35c51742f8b976c40816ad305b12a9836f35d07','INPUT_PINS.json':'a235911032a7d93a59ecb48b3ec2d27d91d863fb9f4b4a373f1f5b58beb7a44c','tools/build_article.py':'881cdd3aa3658bed29b2ed70014285143f0ef1f2315eb1065b1f6aeef3f65072','tools/freeze_inputs.py':'30a5224ed75eb0a8b86f2f58b6dd7c4d508e824c63a6e2048472dcbd9e861782','tools/release.py':'b98817cf30ce60dfb7aaac85b1633176225dec27b29698b25be95c065176ce87','tools/selftest.py':'ea9ac2939a676bb2082966d979ed52cb3b4e6b4b909ce329bd201ccdebefbf53'}
for root in [R,D/'final-candidate',D/'candidate-extracted']:
 for name,pin in pins.items():need(sha((root/name).read_bytes())==pin,'stable artifact changed '+str(root/name))
lockraw=(R/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes();lock=json.loads(lockraw)
need(len(lock['executables'])==7 and len(lock['system_inputs'])==190,'dependency counts')
replays={}
for name in ['candidate-replay','relocated-replay']:
 b=D/name;r=get(b/'BUILD_RECEIPT.json');p=get(b/'PREFLIGHT.json');u=get(b/'RECORDER_INPUT_UNION.json')
 need(r['status']=='PASS' and r['dependency_lock_verified'] and r['packaged_pdf_match'] and r['release_preserved'] and not r['shell_escape'] and r['fresh_format'] and r['recorded_passes']==4 and r['page_count']==12,'replay receipt')
 need(p['status']=='PASS' and p['dependency_lock_sha256']==pins['tools/BUILD_DEPENDENCIES_LOCK.json'],'preflight status')
 need((b/'BUILD_DEPENDENCIES.json').read_bytes()==lockraw,'exact dependency digest')
 need(sha((b/'article.pdf').read_bytes())==pins['article.pdf'],'exact PDF replay')
 need(get(b/'PRESERVATION_BEFORE.json')==get(b/'PRESERVATION_AFTER.json'),'replay preservation')
 observed=set();passrows=[];local_inputs=set()
 for i,label in enumerate(['format','compile-1','compile-2','compile-3']):
  raw=(b/(label+'.fls')).read_bytes();lines=raw.decode().splitlines();pwd=[x[4:] for x in lines if x.startswith('PWD ')];need(len(pwd)==1,'recorder cwd');pwd=Path(pwd[0]);work=pwd.parent if label=='format' else pwd
  inputs=set()
  for line in lines:
   if not line.startswith('INPUT '):continue
   q=Path(line[6:]);q=q if q.is_absolute() else pwd/q;q=q.resolve(strict=False)
   if q==work or work in q.parents:local_inputs.add(q.relative_to(work).as_posix());continue
   need(str(q).startswith(('/usr/share/texlive/','/usr/share/texmf/','/etc/texmf/','/var/lib/texmf/')),'non-system external dependency')
   blob=q.read_bytes();need(lock['system_inputs'].get(str(q))=={'bytes':len(blob),'sha256':sha(blob)},'executed dependency digest');inputs.add(str(q))
  need(u['passes'][i]=={'pass':label,'fls_sha256':sha(raw),'system_inputs':sorted(inputs)},'raw recorder differs from receipt')
  observed.update(inputs);passrows.append({'pass':label,'raw_system_input_count':len(inputs),'raw_fls_sha256':sha(raw)})
  if label=='format':need('OUTPUT pdflatex.fmt' in lines,'fresh format output missing')
 for mapname in ['lm.map','cm.map','cmextra.map','symbols.map','latxfont.map']:
  q=Path((b/('map-'+mapname+'.stdout')).read_text().strip()).resolve(strict=True);blob=q.read_bytes();need(lock['system_inputs'][str(q)]=={'bytes':len(blob),'sha256':sha(blob)},'map bytes');observed.add(str(q))
 need(observed==set(lock['system_inputs']) and u['union']==lock['system_inputs'],'all-pass raw union plus selected maps differs')
 need(local_inputs<={'article.tex','article.aux','article.out','cache/pdftex.map','cache/pdflatex.fmt','cache/texsys.aux'},'unexpected local typesetting input '+str(local_inputs))
 warnings=['Overfull \\hbox','Overfull \\vbox','Underfull \\hbox','undefined references','undefined citations','Rerun to get cross-references right','Label(s) may have changed','rerunfilecheck Warning']
 txt=(b/'compile-3.stdout').read_text();need(not any(x in txt for x in warnings),'final typesetting warning')
 pages=get(b/'PAGE_INVENTORY.json');need(len(pages)==12,'raster page count')
 for page,row in pages.items():blob=(b/'pages'/page).read_bytes();need(len(blob)==row['bytes'] and sha(blob)==row['sha256'],'raster pin')
 replays[name]={'status':'PASS','pdf_sha256':pins['article.pdf'],'page_count':12,'recorders_independently_parsed':passrows,'local_inputs':sorted(local_inputs),'system_input_union_count':len(observed),'dependency_lock_sha256':pins['tools/BUILD_DEPENDENCIES_LOCK.json'],'typesetting_warnings':False,'all_raster_bytes_pinned':True}
need((D/'candidate-replay/PAGE_INVENTORY.json').read_bytes()==(D/'relocated-replay/PAGE_INVENTORY.json').read_bytes(),'replay raster identities differ')
need((D/'candidate-replay/article.txt').read_bytes()==(D/'relocated-replay/article.txt').read_bytes(),'PDF extraction text differs')
mraw=(D/'candidate-manifest.json').read_bytes();m=json.loads(mraw)
for root in [D/'final-candidate',D/'candidate-extracted']:
 need(inventory(root)=={key:m[key] for key in ['files','directories']},'candidate/restored authenticated metadata')
a=(D/'candidate-a.zip').read_bytes();bb=(D/'candidate-b.zip').read_bytes();need(a==bb,'repeat ZIP differs')
with zipfile.ZipFile(D/'candidate-a.zip') as z:
 need(z.namelist()==['UniformSectors/'+n for n in sorted([*m['files'],'RELEASE_MANIFEST.json'])],'ZIP inventory')
 need(z.testzip() is None,'ZIP CRC')
 for info in z.infolist():
  n=info.filename.removeprefix('UniformSectors/');blob=z.read(info)
  need(info.date_time==(2026,10,4,0,0,0) and info.create_system==3 and info.compress_type==zipfile.ZIP_DEFLATED,'deterministic ZIP fields')
  if n=='RELEASE_MANIFEST.json':need(blob==mraw and stat.S_IMODE(info.external_attr>>16)==0o644,'manifest ZIP convention')
  else:need(len(blob)==m['files'][n]['bytes'] and sha(blob)==m['files'][n]['sha256'] and stat.S_IMODE(info.external_attr>>16)==m['files'][n]['mode'],'ZIP member bytes or mode')
receipt={'status':'PASS','review_boundary':'V2 stable artifact/tool/input pins plus external pre-final-QA review snapshot; not the root final release seal','artifact_pins':pins,'replays':replays,'review_candidate_manifest_sha256':sha(mraw),'review_candidate_zip_sha256':sha(a),'review_candidate_zip_bytes':len(a),'review_candidate_files_excluding_manifest':len(m['files']),'review_candidate_directories':len(m['directories']),'deterministic_zip_bytes_equal':True,'authenticated_restoration_bytes_modes_mtime_ns_equal':True,'relocated_pdf_and_all_raster_bytes_equal':True,'scientific_execution':False}
(D/'evidence/INDEPENDENT_REPLAY_RECEIPT.json').write_bytes(enc(receipt));print(enc(receipt).decode())
