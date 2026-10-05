"""Reconstruct saved BR cone polynomials without changing the certificate files."""
from build_br import ROOT,profiles,build,BASES,translate
import json,hashlib,time,argparse
parser=argparse.ArgumentParser()
parser.add_argument('--core',type=int,nargs=4,metavar=('U','J','C1','C2'))
args=parser.parse_args();cores=[tuple(args.core)] if args.core else profiles()
results=[];start=time.time()
for core in cores:
 path=ROOT/('br_%s_%s_%s_%s.json'%core);saved=json.loads(path.read_text());poly,meta=build(*core)
 for key,value in meta.items():
  if value!=saved[key]:raise RuntimeError(('metadata differs',core,key))
 records={tuple(r['basis']):r for r in saved['records']}
 if set(records)!=set(BASES):raise RuntimeError(('basis set',core))
 count=0
 for basis in BASES:
  coefficients=translate(poly,basis);record=records[basis]
  if any(c<0 for c in coefficients.values()):raise RuntimeError(('negative coefficient',core,basis))
  if len(coefficients)!=record['terms'] or min(coefficients.values(),default=0)!=record['minimum']:raise RuntimeError(('coefficient count or minimum',core,basis))
  text=json.dumps([[list(e),c] for e,c in sorted(coefficients.items())],separators=(',',':'))
  if hashlib.sha256(text.encode()).hexdigest()!=record['sha256']:raise RuntimeError(('coefficient list differs',core,basis))
  count+=len(coefficients)
 results.append({'core':core,'all_pass':True,'basis_cones':51,'coefficient_entries':count,'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
 print('PASS',core,count,flush=True)
out={'all_pass':True,'full_batch':not args.core,'profiles':len(results),'basis_cones':sum(r['basis_cones'] for r in results),'coefficient_entries':sum(r['coefficient_entries'] for r in results),'seconds':time.time()-start,'records':results}
name='primary_replay.json' if not args.core else 'selected_replay.json'
(ROOT/name).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))
