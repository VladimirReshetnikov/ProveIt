#!/usr/bin/env python3
"""Independent static closure and literal-payload audit of an assembled directory."""
from pathlib import Path
import gzip,hashlib,json,re,sys
R=Path(sys.argv[1]).resolve(); failures=[];count=0
mf=json.loads((R/'MANIFEST_SHA256.json').read_text())['files']
actual={str(p.relative_to(R)) for p in R.rglob('*') if p.is_file() and p.name!='MANIFEST_SHA256.json'}
if actual!=set(mf):failures.append({'manifest_census':{'unlisted':sorted(actual-set(mf)),'missing':sorted(set(mf)-actual)}})
for name,row in mf.items():
 p=R/name
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=row['sha256'] or p.stat().st_size!=row['bytes']:failures.append({'manifest_mismatch':name})
for base in ['scalar','positive','direct']:
 f=R/base/('DELIVERY_WHITELIST.json' if base=='direct' else 'RELEASE_WHITELIST.json')
 for name in json.loads(f.read_text())['files']:
  if not (R/base/name).is_file():failures.append({'whitelist_missing':base+'/'+name})
for row in json.loads((R/'architecture/SOURCE_CLOSURE.json').read_text())['files']:
 p=R/'architecture'/row['path'];count+=1
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=row['sha256'] or p.stat().st_size!=row['bytes']:failures.append({'architecture_closure_mismatch':row['path']})
texedges=[]
for p in R.rglob('*.tex'):
 for typ,target in re.findall(r'\\(input|include)\{([^}]+)\}',p.read_text()):
  q=p.parent/target
  if not q.suffix:q=q.with_suffix('.tex')
  texedges.append({'source':str(p.relative_to(R)),'input':target,'exists':q.exists()})
  if not q.is_file():failures.append({'tex_missing':texedges[-1]})
needed=['calculus.tex','primitives.tex','crt.tex','direct_arithmetic.tex','calibration/inherited_onestack_section.tex']
for n in needed:
 if not (R/'architecture/proofs/inherited'/n).is_file():failures.append({'calibration_missing':n})
coeff=[]
bind=json.loads((R/'scalar/coefficients/BINDING.json').read_text())
for n,row in bind['payloads'].items():
 raw=gzip.decompress((R/'scalar/coefficients'/row['file']).read_bytes());v=int.from_bytes(raw,'little');ok=hashlib.sha256(raw).hexdigest()==row['raw_sha256'] and len(raw)==row['raw_bytes'] and v.bit_length()==row['bits'] and len(raw)==(v.bit_length()+7)//8
 coeff.append({'tuple':'source34','port':n,'exact_digest_bytes_bits_and_minimal_encoding':ok})
 if not ok:failures.append({'coefficient_mismatch':n})
for eq in sorted((R/'positive/equations').glob('*.json')):
 d=json.loads(eq.read_text());binding=d['coefficient_binding']
 for n,row in binding['ports'].items():
  raw=gzip.decompress((R/'positive'/binding['path']/row['file']).read_bytes());v=int.from_bytes(raw,'little');ok=hashlib.sha256(raw).hexdigest()==row['raw_sha256'] and v.bit_length()==row['bits']
  coeff.append({'tuple':eq.stem,'port':n,'exact_digest_and_bits':ok})
  if not ok:failures.append({'coefficient_mismatch':eq.stem+'/'+n})
pdfs=[str(p.relative_to(R)) for p in R.rglob('*.pdf')];excluded=[str(p.relative_to(R)) for p in R.rglob('*') if p.is_file() and (p.suffix in ['.zip','.pyc','.log','.aux','.out','.toc','.fmt'] or '__pycache__' in p.parts)]
if len(pdfs)!=1:failures.append({'pdf_count':len(pdfs)})
if excluded:failures.append({'unwanted':excluded})
res={'status':'PASS' if not failures else 'FAIL','manifest_bound_files':len(mf),'complete_selected_whitelists':True,'architecture_closure_files':count,'tex_inputs':texedges,'retained_calibration_documents':needed,'coefficient_bindings':coeff,'pdfs':pdfs,'license_files':sorted(str(p.relative_to(R)) for p in R.rglob('*') if p.is_file() and ('LICENSE' in p.name or 'NOTICE' in p.name)),'failures':failures}
print(json.dumps(res,indent=2))
if failures:sys.exit(1)
