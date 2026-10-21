"""Capture bounded proof-source evidence, never objects or the live combined run."""
from pathlib import Path
import argparse,hashlib,json,tarfile,io,gzip
HERE=Path(__file__).resolve().parent;ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
TREES={
 'generic':Path('/tmp/k215-normalized-decoder'),
 'generic-peer':Path('/tmp/k215-normalized-decoder-peer'),
 'normalized':Path('/tmp/k215-normalized-migration'),
 'fast':Path('/tmp/k215-fast-sites-migration'),
 'seed':Path('/tmp/k215-seed-semantic-simplification'),
 'seed-peer':Path('/tmp/k215-seed-semantic-peer'),
}
BAD={'.olean','.ilean','.o','.so','.a','.pyc','.pyo','.vo','.vos','.vok','.glob','.exe'}
def sha(b):return hashlib.sha256(b).hexdigest()
def capture():
 contents={};paths={}
 def add(p,name):
  assert not p.is_symlink()and p.is_file();assert not (set(p.suffixes) & BAD)
  data=p.read_bytes();data.decode('utf-8');assert name not in contents
  contents[name]=data;paths[str(p)]=name
 for tag,base in TREES.items():
  for p in sorted(base.rglob('*')):
   rel=p.relative_to(base)
   if p.is_symlink()or not p.is_file()or {'objects','__pycache__'}&set(rel.parts)or bool(set(p.suffixes) & BAD):continue
   add(p,tag+'/'+rel.as_posix())
 for name in ['adoption.json','pre-run-inventory.json']:
  add(Path('/tmp/k215-proof-phase6')/name,'adoption/'+name)
 for name in ['adoption-review.json','review_adoption.py','adoption-review.stdout','adoption-review.stderr']:
  add(HERE/name,'adoption/'+name)
 L=ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
 for name in ['RMDag','RMEquiv','RegisterPath','RMBisim','KFast215','KBoot','KSim','SiteCoverage']:
  add(L/(name+'.lean'),'provider-sources/'+name+'.lean')
 # The compact packet records, but does not duplicate, the full phase5 basis evidence.
 B=Path('/tmp/k215-proof-phase5/lean-run1')
 for name in ['inventory.json','result.json','toolchain.json']:
  add(B/name,'basis-reference/'+name)
 contents['paths.json']=(json.dumps(paths,indent=2)+'\n').encode()
 return contents

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();a.output.mkdir(exist_ok=False)
 contents=capture();index={k:{'sha256':sha(v),'bytes':len(v)}for k,v in sorted(contents.items())}
 archive=a.output/'evidence.tar.gz'
 with archive.open('wb')as f,gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0)as z,tarfile.open(fileobj=z,mode='w')as t:
  for name,data in sorted(contents.items()):
   info=tarfile.TarInfo(name);info.size=len(data);info.mode=0o644;info.mtime=0;t.addfile(info,io.BytesIO(data))
 (a.output/'index.json').write_text(json.dumps(index,indent=2)+'\n')
 summary={'status':'CAPTURED_FEATURE_EVIDENCE_ONLY','archive_sha256':sha(archive.read_bytes()),'index_sha256':sha((a.output/'index.json').read_bytes()),'members':len(index),'expanded_bytes':sum(x['bytes']for x in index.values()),'archive_bytes':archive.stat().st_size,'no_compiled_objects':True,'combined_phase6_status':'not assessed','adoption_sha256':sha(contents['adoption/adoption.json']),'source_controls':'normalized quotient/Program and fast-site Python checks; no concrete migration kernel acceptance inferred','isolated_checks':'two generic attempts; seed PASS9warnings, syntax FAIL, final PASS0warnings','producer_sha256':sha(Path(__file__).read_bytes())}
 (a.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
