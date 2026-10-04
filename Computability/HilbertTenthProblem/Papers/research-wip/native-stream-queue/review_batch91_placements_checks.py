import argparse,hashlib,io,json,subprocess,zipfile
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
def need(v,s):
 if not v:raise ValueError(s)
sha=lambda b:hashlib.sha256(b).hexdigest()
git=lambda *xs:subprocess.check_output(['git',*xs])
arrival=git('rev-parse','0d7f51c44').decode().strip()
paths=git('diff','--name-only','--diff-filter=A',arrival+'^',arrival,'--','docs/incoming').decode().splitlines()
index={};archives=[]
for path in paths:
 if not path.endswith('.zip'):continue
 data=git('show',arrival+':'+path);z=zipfile.ZipFile(io.BytesIO(data));members=[]
 for i in z.infolist():
  if i.is_dir():continue
  b=z.read(i);h=sha(b);m=dict(path=i.filename,bytes=len(b),sha256=h);members.append(m)
  index.setdefault(h,[]).append(dict(archive=path,member=i.filename))
 archives.append(dict(path=path,bytes=len(data),sha256=sha(data),members=members))
need(len(archives)==24,'24 original archives')
commits=[]
for short in ['b0a536b63','d750d98dd','22a8ca89e']:
 c=git('rev-parse',short).decode().strip();parent=git('rev-parse',c+'^').decode().strip()
 items=git('diff-tree','--no-commit-id','--name-status','-r','-z',c).split(b'\0');pairs=list(zip(items[0::2],items[1::2]));adds=[];deleted=[]
 for status,pathb in pairs:
  path=pathb.decode()
  if status==b'A':adds.append(path)
  elif status==b'D':deleted.append(path)
  else:raise ValueError('unexpected changed status '+str((status,path)))
 objects={}
 for line in git('ls-tree','-r',c).splitlines():
  meta,path=line.split(b'\t',1);objects[path.decode()]=meta.split()[2].decode()
 refs=[objects[path] for path in adds]
 proc=subprocess.run(['git','cat-file','--batch'],input=('\n'.join(refs)+'\n').encode(),stdout=subprocess.PIPE,check=True);stream=io.BytesIO(proc.stdout)
 placed=[]
 for path,obj in zip(adds,refs):
  header=stream.readline().split();need(header[0].decode()==obj and header[1]==b'blob','batch header');b=stream.read(int(header[2]));need(stream.read(1)==b'\n','batch newline');h=sha(b)
  need(h in index,'unmatched placed file '+path)
  placed.append(dict(path=path,blob=obj,bytes=len(b),sha256=h,matches=index[h]))
 need(not stream.read(),'unused batch bytes')
 hosts=sorted({path.split('/code/')[0].split('/data/')[0].split('/figures/')[0].rsplit('/',1)[0] if not any(x in path for x in ['/code/','/data/','/figures/']) else path.split('/code/')[0].split('/data/')[0].split('/figures/')[0] for path in adds})
 # Every addition is ancillary: none changes or introduces its host article/guide.
 need(all(not path.endswith(('/article.tex','/article.pdf','/README.md')) for path in adds),'no primary publication in these checkpoints')
 unchanged=[]
 for host in hosts:
  for name in ['article.tex','README.md']:
   path=host+'/'+name
   try: before=git('rev-parse',parent+':'+path).decode().strip();after=git('rev-parse',c+':'+path).decode().strip()
   except subprocess.CalledProcessError:continue
   need(before==after,'host changed');unchanged.append(dict(path=path,blob=after))
 need(all(path.endswith('.zip') for path in deleted),'only archive retirements')
 commits.append(dict(commit=c,parent=parent,placed=placed,placed_count=len(placed),placed_bytes=sum(x['bytes']for x in placed),deleted_archives=deleted,unchanged_hosts=unchanged))
receipt=dict(source_sha256=sha(Path(__file__).read_bytes()),arrival=arrival,archives=archives,placements=commits,scope='Exact immutable byte placement only; no mathematical read or archive/predecessor program execution')
with a.output.open('x')as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
print([(x['commit'][:9],x['placed_count'],x['placed_bytes'],len(x['deleted_archives']),len(x['unchanged_hosts']))for x in commits])
