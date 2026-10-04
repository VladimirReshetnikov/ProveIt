#!/usr/bin/env python3
"""Independent read-only content/metadata and sealed evidence audit. Never imports supplied source."""
import hashlib,json,os,stat,zipfile
from pathlib import Path
BASE=Path('/workspace/shared')
ROOT=BASE/'oeis-uniform-sectors-release-20261004'
OUT=BASE/'oeis-uniform-sectors-tools-review-20261004/evidence'
def need(ok,msg):
 if not ok: raise ValueError(msg)
def sha(data): return hashlib.sha256(data).hexdigest()
def row(p):
 s=p.lstat();need(not stat.S_ISLNK(s.st_mode),'symlink '+str(p));need(stat.S_ISDIR(s.st_mode) or stat.S_ISREG(s.st_mode),'nonregular '+str(p))
 d={'kind':'directory' if p.is_dir() else 'file','mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns}
 if p.is_file():
  need(s.st_nlink==1,'hardlink '+str(p));b=p.read_bytes();d.update(size=len(b),sha256=sha(b))
  t=p.lstat();need((s.st_ino,s.st_size,s.st_mode,s.st_mtime_ns,s.st_ctime_ns)==(t.st_ino,t.st_size,t.st_mode,t.st_mtime_ns,t.st_ctime_ns),'read mutation '+str(p))
 return d
def tree(p): return {q.relative_to(p).as_posix():row(q) for q in [p,*sorted(p.rglob('*'))]}
def get(p): return json.loads(p.read_bytes())
def write(name,data):
 with (OUT/name).open('x') as f: json.dump(data,f,sort_keys=True,indent=2);f.write('\n')
source_map={'uniform-sectors':'growing-sector-truncations-20261004','independent-audit':'independent-growing-sector-audit-20261004','predecessor-release':'oeis-arity-asymptotics-release-20261004'}
primary={'uniform-sectors/PROOF.md':'ebd92e3b5bdf684981b2ff248376ac290c57aec403169beee780fef9ea92aa65','independent-audit/AUDIT.md':'4fa84b2ddfe383668c86ea0ad4d7419b0304eb0d9a97725aecbdab7e3b63ff03'}
for name,pin in primary.items():need(sha((ROOT/'inputs'/name).read_bytes())==pin,'primary pin')
comparisons={}
for name,original in source_map.items():
 a,b=tree(BASE/original),tree(ROOT/'inputs'/name);need(a==b,'copy boundary '+name)
 comparisons[name]={'objects':len(a),'files':sum(x['kind']=='file' for x in a.values()),'directories_including_root':sum(x['kind']=='directory' for x in a.values()),'bytes_modes_mtime_ns_identical':True}
for p in (ROOT/'inputs/source-seals').iterdir(): need(row(p)==row(BASE/p.name),'adjacent seal copy '+p.name)
pinsraw=(ROOT/'INPUT_PINS.json').read_bytes();need(sha(pinsraw)=='a235911032a7d93a59ecb48b3ec2d27d91d863fb9f4b4a373f1f5b58beb7a44c','input pins')
pins=json.loads(pinsraw);fr=tree(ROOT/'inputs');need(len(pins['files'])==213 and len(pins['directories'])==26,'frozen counts')
for name,x in fr.items():
 key='inputs' if name=='.' else 'inputs/'+name
 d={'mode':x['mode'],'mtime_ns':x['mtime_ns']}
 if x['kind']=='file':d.update(bytes=x['size'],sha256=x['sha256']);expected=pins['files'][key]
 else:expected=(pins['roots'] if name=='.' else pins['directories'])[key]
 need(d==expected,'frozen row '+key)
need(len(fr)==240,'frozen object inventory')
boundary=get(ROOT/'qa/tool-original-inputs-before.json');need(len(boundary)==355,'original count')
current={name:row(Path(name)) for name in boundary};need(boundary==current,'original current boundary')
for name,x in current.items():
 if x['kind']=='directory':need(all(str(p) in current for p in Path(name).rglob('*')),'unrecorded original under '+name)
need(get(ROOT/'qa/tool-original-inputs-after-freeze.json')==boundary,'owner freeze endpoints')
historical={}
for name,count in [('uniform-sectors',51),('independent-audit',333)]:
 before=get(ROOT/'inputs'/name/'evidence/input-before.json')['objects'];after=get(ROOT/'inputs'/name/'evidence/input-after.json')['objects'];need(before==after,'historical endpoint '+name);need(len(before)==count,'historical count')
 converted={}
 for x in before:
  x=x.copy();p=x.pop('path')
  if x['kind']=='directory':x.pop('size',None)
  need(p not in converted,'historical duplicate');need(current[p]==x,'current historical '+p);converted[p]=x
 historical[name]=converted
need(set(historical['uniform-sectors'])<=set(historical['independent-audit']),'source subset historical audit')
archives={}
archive_pins={'uniform-sectors':'5155553958eb14f2a2bb0c28aa1262cc2e2ad1871aac3b37d6d3efc2c7355c42','independent-audit':'a9f4bd10377462b1430da6579d02f0d920985c17344c4f4c6e43fab7d38b40f3','predecessor-release':'821a1cfc1c00fd6d109ee2f6ff8007b4e8985f03d45f6f9a04d07aa8623fde27'}
for name,original in source_map.items():
 source=ROOT/'inputs'/name
 if name=='predecessor-release':filename='A196460-clipping-tables-source-evidence-20261004.zip';prefix='ArityAsymptotics'
 else:filename=original+'.zip';prefix=original
 p=ROOT/'inputs/source-seals'/filename;need(sha(p.read_bytes())==archive_pins[name],'archive external pin')
 files={q.relative_to(source).as_posix():q for q in source.rglob('*') if q.is_file()}
 with zipfile.ZipFile(p) as z:
  need(z.namelist()==[prefix+'/'+x for x in sorted(files)],'archive exact file inventory')
  need(z.testzip() is None,'archive CRC')
  for rel,q in files.items():
   info=z.getinfo(prefix+'/'+rel);need(z.read(info)==q.read_bytes(),'archive bytes');need(stat.S_ISREG(info.external_attr>>16),'archive regular')
   mode=0o644 if name=='predecessor-release' and rel=='RELEASE_MANIFEST.json' else stat.S_IMODE(q.stat().st_mode)
   need(stat.S_IMODE(info.external_attr>>16)==mode,'archive mode')
 archives[name]={'sha256':archive_pins[name],'exact_members_bytes_modes':len(files)}
 if name!='predecessor-release':
  records={}
  for line in (source/'MANIFEST.sha256').read_text().splitlines():
   digest,rel=line.split('  ',1);need(rel not in records,'duplicate source manifest');records[rel]=digest
  need(set(records)==set(files)-{'MANIFEST.sha256'},'source manifest inventory')
  for rel,pin in records.items():need(sha(files[rel].read_bytes())==pin,'source manifest hash')
 else:
  raw=(source/'RELEASE_MANIFEST.json').read_bytes();need(sha(raw)=='313fe6210e10e3053ff518a591dc46c86c29681618775be67f0f87474ca4584c','predecessor manifest pin');m=json.loads(raw)
  rows=tree(source)
  for rel,x in rows.items():
   if rel in ('.','RELEASE_MANIFEST.json'):continue
   expected={'mode':x['mode'],'mtime_ns':x['mtime_ns']}
   if x['kind']=='file':expected.update(bytes=x['size'],sha256=x['sha256'])
   need(m['files' if x['kind']=='file' else 'directories'][rel]==expected,'predecessor manifest metadata')
write('INDEPENDENT_ORIGINAL_BOUNDARY.json',current)
write('INDEPENDENT_FROZEN_BOUNDARY.json',fr)
receipt={'status':'PASS','primary_pins':primary,'frozen_files':213,'frozen_directories_excluding_inputs_root':26,'original_objects':355,'historical_source_objects':51,'historical_audit_objects':333,'historical_source_is_subset_of_audit':True,'copied_trees':comparisons,'authenticated_archives':archives,'full_predecessor_unchanged':True,'scientific_code_executed_or_imported':False,'scope_exclusions':['atime','ctime','owner','inode allocation','directory allocation size'],'historical_scope_not_retroactively_broadened':True}
write('INDEPENDENT_PRESERVATION_RECEIPT.json',receipt);print(json.dumps(receipt,indent=2,sort_keys=True))
