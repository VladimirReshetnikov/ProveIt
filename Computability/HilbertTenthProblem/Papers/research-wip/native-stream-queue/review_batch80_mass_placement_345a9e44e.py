#!/usr/bin/env python3
"""Authenticate batch80 mass-report companion placement without executing it."""
import argparse, hashlib, io, json, subprocess, zipfile
from pathlib import Path, PurePosixPath
ARRIVAL='4e270aa4648c5fd7e18626507531046715976535'
COMMIT='345a9e44e665c5e21888fcb1be6da9d1a94e2d25'
REPORT='SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates'
PACKAGES={
 '14-three-mass':('Three_Mass_Reversible_Computation.zip','fd86a8a6b71735ef08ebd7913498603213244484da8b23d81876b10c40ffd1de',66),
 '15-clean-targets':('Exact_Targets_Three_Mass_Units.zip','d69d8df9ee3a2074bcff1ef400853724eafb679ada8b287ef397eb8891965dcc',38),
 '16-single-unit':('Single_Unit_Three_Mass_Decidability (1).zip','299fef3508423dfe1fc88dc3473a39a40eac7cbfaf5d53c16dc26b9a3d119b12',13),
 '17-four-mass':('Four_Mass_Decidability_Package.zip','0bcc026a8ca7bd4745b82e6f9c2841073e5fb8c639970105690fc40803a780fe',33),
 'original-single-unit':('Single_Unit_Three_Mass_Decidability.zip','25c0d2712b111ba9240fb11b23689b3eded14b059a5a793e33aa515f1c97f646',12),
}
def need(ok,message):
 if not ok:raise ValueError(message)
def sha(data):return hashlib.sha256(data).hexdigest()
def git(repo,*args):return subprocess.check_output(['git',*args],cwd=repo,timeout=60)
def blob(repo,ref,path):return git(repo,'show',ref+':'+path)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def verify(repo):
 packages={};raw={};archive_paths=[]
 for prefix,(archive,pin,count) in PACKAGES.items():
  path='docs/incoming/'+archive; archive_paths.append(path);data=blob(repo,ARRIVAL,path)
  need(sha(data)==pin,'archive pin '+archive)
  with zipfile.ZipFile(io.BytesIO(data)) as z:
   names=[i.filename for i in z.infolist() if not i.is_dir()]
   need(len(names)==count and len(names)==len(set(names)),'member inventory')
   raw[prefix]={name:z.read(name) for name in names}
  packages[prefix]=dict(archive=archive,sha256=pin,members={name:sha(v) for name,v in raw[prefix].items()})
 changes=[line.split('\t') for line in git(repo,'diff-tree','--no-commit-id','--name-status','-r',COMMIT).decode().splitlines()]
 need({path for mode,path in changes if mode=='D'}==set(archive_paths),'exact retired archives')
 need([path for mode,path in changes if mode=='M']==['SetTheory/Cardinals/.gitattributes'],'only non-addition metadata edit')
 added=[path for mode,path in changes if mode=='A']
 need(len(added)==116 and len(changes)==122,'full change inventory')
 mapped=[];covered={prefix:set() for prefix in PACKAGES}
 for path in added:
  need(path.startswith(REPORT+'/'),'all additions in intended report')
  rel=path[len(REPORT)+1:];name=PurePosixPath(rel).name
  prefixes=[prefix for prefix in PACKAGES if name.startswith(prefix+'-')]
  need(len(prefixes)==1,'one package prefix '+path);prefix=prefixes[0];data=blob(repo,COMMIT,path)
  candidates=[src for src,b in raw[prefix].items() if b==data]
  stem=name[len(prefix)+1:]
  named=[src for src in candidates if PurePosixPath(src).name==stem or src.endswith('/'+stem.replace('legacy-','legacy/',1))]
  need(len(named)==1,'unique intended source name and bytes '+path+': '+str(candidates));source=named[0]
  covered[prefix].add(source)
  mapped.append(dict(path=path,package=prefix,member=source,sha256=sha(data),bytes=len(data)))
 # Deduplication must name a source-qualified already-authenticated destination.
 aliases=[]
 for prefix in ('15-clean-targets','original-single-unit'):
  for name,data in raw[prefix].items():
   if prefix=='15-clean-targets' and '/vendor/' not in name:continue
   desired='14-three-mass' if prefix=='15-clean-targets' else '16-single-unit'
   matches=[m for m in mapped if m['package']==desired and PurePosixPath(m['member']).name==PurePosixPath(name).name and m['sha256']==sha(data)]
   if matches:
    need(len(matches)==1,'unique explicit alias');aliases.append(dict(package=prefix,member=name,path=matches[0]['path'],sha256=sha(data)));covered[prefix].add(name)
 need(sum(a['package']=='15-clean-targets' for a in aliases)==5,'all five vendored aliases')
 # The native two-mass receipt intentionally reuses the older sparse receipt.
 prefix='14-three-mass';existing=REPORT+'/data/13-sparse-lattice-two-mass-arithmetic.json';data=blob(repo,COMMIT,existing)
 candidates=[n for n,b in raw[prefix].items() if b==data]
 need(len(candidates)==1,'one native two-mass receipt alias');aliases.append(dict(package=prefix,member=candidates[0],path=existing,sha256=sha(data)));covered[prefix].add(candidates[0])
 omitted={prefix:[dict(member=n,sha256=sha(data),bytes=len(data)) for n,data in members.items() if n not in covered[prefix]] for prefix,members in raw.items()}
 unchanged={}
 for name in ('article.tex','article.pdf','README.md'):
  a=blob(repo,COMMIT+'^',REPORT+'/'+name);b=blob(repo,COMMIT,REPORT+'/'+name)
  need(a==b,'placement changed assembled source '+name);unchanged[name]=sha(b)
 tex=blob(repo,COMMIT,REPORT+'/article.tex').decode()
 need(r'\part{Three conserved mass' not in tex and 'smc:tm:thm:' not in tex,'new mathematical write not yet present')
 # An exact CRLF source table is deliberately outside Git text normalization.
 csv_path=REPORT+'/data/17-four-mass-binary-four-particle-shuttle.csv';csv=blob(repo,COMMIT,csv_path)
 attr_path='SetTheory/Cardinals/.gitattributes';before=blob(repo,COMMIT+'^',attr_path);after=blob(repo,COMMIT,attr_path)
 attr_delta=after[len(before):] if after.startswith(before) else None
 need(attr_delta is not None and csv.count(b'\r\n')==46 and b'binary-four-particle-shuttle.csv -text' in attr_delta,'explicit CRLF preservation')
 # Static evidence that flattened placement itself is not the original runnable layout.
 runner=blob(repo,COMMIT,REPORT+'/code/14-three-mass-replay.sh').decode()
 need('code/three_mass_collision_generator.py' in runner,'source-relative native entrypoint')
 checker=blob(repo,COMMIT,REPORT+'/code/15-clean-targets-clean_targets.py').decode()
 need('vendor' in checker,'source-relative vendor imports')
 tree=set(git(repo,'ls-tree','-r','--name-only',COMMIT,REPORT).decode().splitlines())
 need(REPORT+'/code/three_mass_collision_generator.py' not in tree and REPORT+'/vendor/certificate.py' not in tree,'flattened release layout distinction')
 counts={prefix:dict(published=len(raw[prefix]),direct=sum(m['package']==prefix for m in mapped),aliases=sum(a['package']==prefix for a in aliases),archive_only=len(omitted[prefix])) for prefix in PACKAGES}
 return dict(status='PASS_PINNED_COMPANION_PLACEMENT_ONLY',arrival=ARRIVAL,commit=COMMIT,archives=packages,mapped=mapped,explicit_aliases=aliases,archive_only=omitted,counts=counts,total_published_members=sum(len(v) for v in raw.values()),placed_physical_files=116,unchanged_assembled_files=unchanged,gitattributes=dict(before_sha256=sha(before),after_sha256=sha(after),appended_text=attr_delta.decode(),csv_crlf_rows=46),scope='Exact bytes and intended package mapping only. No new Parts V/VI source or report README/PDF is written by this placement; no theorem-transfer claim. Original layouts can be restored from pinned Git ZIPs. No author code, build script, PDF renderer or test suite executed; their earlier full reviews and root replays remain the proof/replay boundary.')
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,default=Path.cwd());p.add_argument('--expect',type=Path);p.add_argument('--output',type=Path);a=p.parse_args();r=verify(a.repo)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'typed saved receipt differs')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],physical=r['placed_physical_files'],members=r['total_published_members'],counts=r['counts']),indent=2))
