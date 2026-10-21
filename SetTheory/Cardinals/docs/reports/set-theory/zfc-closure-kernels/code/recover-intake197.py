"""Recover Source159's complete original layout from Git; execute nothing."""
from pathlib import Path,PurePosixPath
import argparse,hashlib,io,json,stat,subprocess,zipfile

COMMIT='d59b4418821c598c4703f0a60b1f7cbae4f3bcf6'
ARCHIVE='K216_Permuted_Commands_2026-10-21.zip'

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('output',type=Path);a=ap.parse_args()
 repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
 output=a.output.resolve()
 if output==repo or repo in output.parents:ap.error('Use a new directory outside the repository')
 output.mkdir(parents=True,exist_ok=False)
 data=subprocess.check_output(['git','show',COMMIT+':docs/incoming/'+ARCHIVE],cwd=repo)
 target=output/Path(ARCHIVE).stem;target.mkdir()
 with zipfile.ZipFile(io.BytesIO(data)) as z:
  entries=z.infolist();names=[x.filename for x in entries]
  if len(names)!=len(set(names)):raise ValueError('Duplicate ZIP member')
  for x in entries:
   p=PurePosixPath(x.filename)
   if p.is_absolute() or '..' in p.parts or stat.S_ISLNK(x.external_attr>>16):raise ValueError('Unsafe ZIP member: '+x.filename)
  for x in entries:
   if x.is_dir():continue
   p=target.joinpath(*PurePosixPath(x.filename).parts);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(z.read(x))
  count=sum(not x.is_dir() for x in entries)
 if count!=72:raise ValueError('Expected all72 original members')
 result={'status':'RECOVERED_WITHOUT_EXECUTION','commit':COMMIT,'archive':ARCHIVE,'archive_sha256':hashlib.sha256(data).hexdigest(),'members':count,'directory':str(target)}
 (output/'recovery.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
