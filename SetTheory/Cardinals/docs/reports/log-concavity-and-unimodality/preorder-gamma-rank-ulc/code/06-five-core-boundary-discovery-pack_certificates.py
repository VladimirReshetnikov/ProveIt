from pathlib import Path
import tarfile,lzma,sys,time,json,hashlib
src=Path(sys.argv[1]);out=Path(sys.argv[2]);t=time.time();files=sorted(src.glob('certificate_*.json'),key=lambda p:int(p.stem.split('_')[-1]));assert not out.exists(),'Do not silently overwrite certificate pack'
with lzma.open(out,'wb',preset=6)as compressed:
 with tarfile.open(fileobj=compressed,mode='w|',format=tarfile.PAX_FORMAT)as tar:
  for p in files:
   info=tar.gettarinfo(str(p),arcname=src.name+'/'+p.name);info.mtime=0;info.uid=0;info.gid=0;info.uname='';info.gname=''
   with p.open('rb')as f:tar.addfile(info,f)
r={'archive':str(out),'files':len(files),'bytes':out.stat().st_size,'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'seconds':round(time.time()-t,2)};print(json.dumps(r,indent=2));out.with_suffix(out.suffix+'.json').write_text(json.dumps(r,indent=2)+'\n')
