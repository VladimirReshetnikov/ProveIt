from pathlib import Path
import hashlib,json,os
src=Path('/tmp/diophantine-cache-dedup-audit-v5.json');d=json.loads(src.read_text());records=[]
for e in d['records']:
 p,q=Path(e['duplicate']),Path(e['keeper'])
 assert p.is_file() and q.is_file() and not p.is_symlink() and not q.is_symlink()
 assert p.stat().st_size==q.stat().st_size==e['bytes']
 assert hashlib.sha256(p.read_bytes()).hexdigest()==hashlib.sha256(q.read_bytes()).hexdigest()==e['sha256']
 if os.path.samefile(p,q):continue
 assert not p.with_name(p.name+'.dedup-link').exists()
 old=p.stat().st_ino;tmp=p.with_name(p.name+'.dedup-link');os.link(q,tmp);os.replace(tmp,p)
 assert not p.is_symlink() and os.path.samefile(p,q)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==e['sha256']
 records.append(dict(**e,old_inode=old,new_inode=p.stat().st_ino))
out=Path('/tmp/diophantine-cache-dedup-result-v5.json');out.write_text(json.dumps(dict(scope='Content-preserving hardlinks between exact duplicate immutable completed ZFC caches; all paths remain regular files, no bytes/source/active output changed.',audit_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),records=records),indent=2)+'\n')
print(json.dumps(dict(files=len(records),bytes=sum(e['bytes']for e in records),free_bytes=os.statvfs('/tmp').f_bavail*os.statvfs('/tmp').f_frsize,result_sha256=hashlib.sha256(out.read_bytes()).hexdigest())))
