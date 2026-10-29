from pathlib import Path
import hashlib,json,subprocess,zipfile
r=Path('/dev/shm/legendre-parity');out=Path('/tmp/legendre-parity-evidence');w=Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency');h=lambda b:hashlib.sha256(b).hexdigest();files={}
def add(n,b):
 assert n not in files,n
 files[n]=b
for p in r.rglob('*'):
 if p.is_file() and p.suffix in ('.lean','.json','.log','.py','.time','.txt') and not any(x.startswith('objects-') for x in p.relative_to(r).parts):add('prototype/'+str(p.relative_to(r)),p.read_bytes())
for phase,rev in [('baseline','1ba9520188^'),('final','1ba9520188')]:
 n='ArithmeticBinomLegendre.lean';b=subprocess.check_output(['git','show',rev+':'+str(w/n)]);assert b==(r/phase/'DiophantineConsistency'/n).read_bytes();add('commit/'+phase+'/'+n,b)
for n in ['ArithmeticBinomPascal','ArithmeticBinomFactorial','ArithmeticBinaryPopulation','ArithmeticHalfBinomialSandwich','ArithmeticBinomExpansion','ArithmeticHalfBinomial']:add('sources/'+n+'.lean',(w/(n+'.lean')).read_bytes())
for name,p in [('binary-half-direct-final-records.json','/tmp/binary-half-direct/final-records.json'),('outer-seed-bound-sharing-prereq2-records.json','/tmp/outer-seed-bound-sharing/prereq2-records.json'),('outer-seed-bound-sharing-build-prereqs2.py','/tmp/outer-seed-bound-sharing/build-prereqs2.py')]:add('providers/'+name,Path(p).read_bytes())
for name in ['review.txt','audit.py','audit.log']:add('independent/'+name,Path('/tmp/legendre-parity-peer-'+name).read_bytes())
archive=out/'inputs-and-logs.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for n,b in sorted(files.items()):z.writestr(n,b)
review=Path('/tmp/legendre-parity-peer-review.txt').read_bytes();(out/'independent-review.txt').write_bytes(review)
m={'schema':'lean-proof-simplification-evidence-v1','source_commit':subprocess.check_output(['git','rev-parse','1ba9520188'],text=True).strip(),'source_parent':subprocess.check_output(['git','rev-parse','1ba9520188^'],text=True).strip(),'scope':'Prove even and odd factors distinct by remainders','validation':'A current-source ArithmeticBinomFactorial provider was rebuilt; paired target and sole tracked direct Lean client ArithmeticHalfBinomial builds pass with identical client objects. Eight exact-target-object-pinned probes report equal target declarations, type/axioms, and sampled default simp and instance registrations. Target source-current BinaryPopulation and Factorial\'s direct Pascal input match prior successful producer receipts. Two existing linter warnings disappear while one remains.','limitations':['Direct client providers ArithmeticHalfBinomialSandwich and ArithmeticBinomExpansion have no source/object producer match in the documented local records search; no staleness conclusion follows. Wider transitive closure remains cached and downstream clients were not rebuilt.','Declaration, type/axiom and sampled registration equality does not establish proof-body identity or equality of all persistent Lean extensions.','Compiled objects excluded. Recorded build and probe paths refer to temporary directories; full replay requires external object dependencies and environment. Intermediate long proof and its overwritten records are exploratory only, as README states.'],'archive':archive.name,'archive_sha256':h(archive.read_bytes()),'independent_review':{'path':'independent-review.txt','sha256':h(review)},'members':{n:{'bytes':len(b),'sha256':h(b)} for n,b in sorted(files.items())}}
(out/'BUNDLE.json').write_text(json.dumps(m,indent=2)+'\n');print(len(files),'members',archive.stat().st_size,'bytes',m['archive_sha256'])
