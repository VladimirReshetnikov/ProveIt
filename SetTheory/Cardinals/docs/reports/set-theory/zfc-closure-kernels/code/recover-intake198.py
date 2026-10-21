"""Recover both complete intake198 archives from Git without executing them."""
from pathlib import Path,PurePosixPath
import argparse,hashlib,io,json,stat,subprocess,zipfile

SOURCES=[('001695a82b8b3a7bc421aafbe8b87910a5aa0743','K215_Composed_Commands_Selector_2026-10-20.zip',67),
         ('7e8cc0ee93','K215_Composed_Selectors_2026-10-20.zip',82)]

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('output',type=Path);a=ap.parse_args()
 repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip());out=a.output.resolve()
 if out==repo or repo in out.parents:ap.error('Use a new directory outside the repository')
 out.mkdir(parents=True,exist_ok=False);records=[]
 for commit,name,count in SOURCES:
  data=subprocess.check_output(['git','show',commit+':docs/incoming/'+name],cwd=repo);target=out/Path(name).stem;target.mkdir()
  with zipfile.ZipFile(io.BytesIO(data))as z:
   entries=z.infolist();names=[i.filename for i in entries];assert len(names)==len(set(names))
   for i in entries:
    p=PurePosixPath(i.filename)
    assert not p.is_absolute()and'..'not in p.parts and not stat.S_ISLNK(i.external_attr>>16),i.filename
   assert sum(not i.is_dir()for i in entries)==count
   for i in entries:
    if i.is_dir():continue
    p=target.joinpath(*PurePosixPath(i.filename).parts);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(z.read(i))
  records.append({'commit':commit,'archive':name,'members':count,'archive_sha256':hashlib.sha256(data).hexdigest(),'directory':str(target)})
 result={'status':'RECOVERED_WITHOUT_EXECUTION','sources':records};(out/'recovery.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'])
if __name__=='__main__':main()
