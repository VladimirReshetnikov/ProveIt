#!/usr/bin/env python3
"""Independent exact audit of the inherited radical/affine compositions."""
from pathlib import Path
import argparse,copy,hashlib,json,sys,zipfile,subprocess,tempfile
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'inherited_radical'))
import audit_projection as a

def read(path):return json.loads(path.read_text())
def require(v,msg):
 if not v:raise ValueError(msg)

def source_bindings():
 answers={}
 for directory,expected in [('inherited_pooled','0e0efbc168fcaac562042778ffcd5bf40f6f74a711ee33915c0ea0750aa10c55'),('inherited_radical','fca2e2090cbde71baa7a992c7962886215c6ded6232eb1a7115989f4eadba89e')]:
  base=ROOT/directory;ledger=read(base/'SOURCE.json');archive=base/ledger['source_archive']
  require(hashlib.sha256(archive.read_bytes()).hexdigest()==expected,'upstream archive binding')
  with zipfile.ZipFile(archive) as z:
   if directory=='inherited_pooled':
    require((base/'source225.json').read_bytes()==z.read(ledger['source_member']),'source225 is not exact archived member')
   else:
    for name in ledger['files']:
     member='ConZFC_Quadratic_Projection_234_2026-10-25/code/'+name
     require((base/name).read_bytes()==z.read(member),'inherited module changed: '+name)
  answers[directory]={'archive_sha256':expected,'status':'PASS'}
 archive=ROOT/'inherited_sources/ConZFC_Factorial_Free_Binomial_CRT_2026-10-25.zip'
 expected='38dfec4f7db8ba4af921fe101714da6a569a3afce1d916325eb550160372c913'
 require(hashlib.sha256(archive.read_bytes()).hexdigest()==expected,'factorial-free archive binding')
 count=0
 with zipfile.ZipFile(archive) as z:
  for member in z.infolist():
   if member.is_dir():continue
   relative=Path(member.filename).relative_to('ConZFC_Factorial_Free_Binomial_CRT_2026-10-25')
   require((ROOT/'baseline'/relative).read_bytes()==z.read(member),'unchanged baseline member: '+str(relative))
   count+=1
 answers['inherited_factorial_free']={'archive_sha256':expected,'exact_baseline_files':count,'status':'PASS'}
 return answers

def upstream_finite_replay():
 flags=['-B']+([] if __debug__ else ['-O'])
 def run(script,args):
  result=subprocess.run([sys.executable,*flags,str(script),*args],check=True,capture_output=True,text=True)
  return json.loads(result.stdout)
 diagonal=run(ROOT/'verify.py',[])
 require(diagonal['status']=='PASS','complete diagonal source finite replay')
 require((ROOT/'diagonal_pool/inputs/source238.json').read_bytes()==(ROOT/'diagonal238/equation.json').read_bytes(),'diagonal pool exact source238 binding')
 require((ROOT/'diagonal_pool/inputs/source238_affine_certificate.json').read_bytes()==(ROOT/'diagonal238/certificate.json').read_bytes(),'diagonal pool affine certificate binding')
 require((ROOT/'diagonal_pool/output/pooled/equation.json').read_bytes()==(ROOT/'pooled223_source.json').read_bytes(),'diagonal pool exact source223 binding')
 with tempfile.TemporaryDirectory(prefix='conzfc-composition-check-') as temp:
  temp=Path(temp)
  pooling=run(ROOT/'diagonal_pool/check.py',['--receipt',str(temp/'pool.json')])
  require(pooling['result']=='PASS','new pooling independent audit')
  archive=ROOT/'inherited_pooled/ConZFC_Pooled_Powers_2026-10-25.zip'
  with zipfile.ZipFile(archive) as z:
   for name in z.namelist():require((temp/name).resolve().is_relative_to(temp.resolve()),'unsafe upstream archive member')
   z.extractall(temp)
  inherited=run(temp/'ConZFC_Pooled_Powers_2026-10-25/verify.py',['--rebuild'])
  require(inherited['result']=='passed','unchanged pooled225 audit and rebuild')
 return {'diagonal_source':diagonal,'new_pooled_source':pooling,'inherited_pooled225':inherited}

def substitute_shear(rows,t,linear):
 """Use Q=A*x_t²+B*x_t+C, independently of producer's monomial substitution."""
 replacement={(t,):1,**{(i,):c for i,c in linear.items()}}
 square=a.product(replacement,replacement)
 answer=[]
 for row in rows:
  aa=row.get((t,t),0);b={};c={}
  for mon,co in row.items():
   count=mon.count(t)
   if count==0:c[mon]=co
   elif count==1:
    key=tuple(i for i in mon if i!=t);b[key]=b.get(key,0)+co
  out=a.linear_combine(c,1,a.product(b,replacement))
  out=a.linear_combine(out,aa,square);answer.append(out)
 return answer

def audit_shears():
 source=read(ROOT/'pooled225_radical/equation.json');target=read(ROOT/'pooled220_sheared/equation.json');cert=read(ROOT/'pooled220_sheared/shear_certificate.json')
 require(cert['schema']=='integral_coordinate_shears_v1','shear schema')
 require(a.sha(source)==cert['input_sha256'],'shear input digest')
 require(source.get('domain')=='unrestricted integers','shear integer domain')
 n=len(source['variables']);original=[a.polynomial(r['terms'],n) for r in source['residuals']];rows=copy.deepcopy(original)
 for t,pairs in cert['operations']:
  require(type(t)is int and 0<=t<n,'shear target')
  require(len(dict(pairs))==len(pairs),'duplicate shear source')
  require(all(type(i)is int and 0<=i<n and i!=t and type(c)is int for i,c in pairs),'nonintegral/noninvertible shear')
  rows=substitute_shear(rows,t,dict(pairs))
 result=copy.deepcopy(source);result['variant']+=':integral_coordinate_shears'
 for r,p in zip(result['residuals'],rows):r['terms']=a.serial(p)
 require(result==target and a.sha(target)==cert['output_sha256'],'shear target coefficients')
 for t,pairs in reversed(cert['operations']):rows=substitute_shear(rows,t,{i:-c for i,c in pairs})
 require(rows==original,'shear inverse coefficient replay')
 expansion=a.expanded_sos(target)
 supplied=read(ROOT/'pooled220_sheared/expanded_polynomial.json')
 require(a.polynomial(supplied['terms'],n,4)==expansion,'shear full quartic')
 require(a.metrics(target,expansion)==read(ROOT/'pooled220_sheared/metrics.json'),'shear metrics')
 return {'status':'PASS','integer_coordinate_shears':len(cert['operations']),'metrics':a.metrics(target,expansion)}

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--receipt',type=Path);args=parser.parse_args()
 output={'status':'PASS','source_bindings':source_bindings(),'upstream_finite_replay':upstream_finite_replay(),'proof_scope':'Complete finite source/checker chain, exact algebraic maps, full coefficient collection and unchanged pooled225 reproduction. Unbounded semantic theorems and logical calibration remain the identified ordinary proofs.','profiles':{}}
 for n in [238,239]:
  name=f'radical{n}';output['profiles'][name]=a.audit(ROOT/f'diagonal{n}_reduced/equation.json',ROOT/name)
  for d in sorted(ROOT.glob(name+'_*')):
   if (d/'row_certificate.json').exists():output['profiles'][d.name]=a.audit_rows(ROOT/name/'equation.json',d)
 output['profiles']['pooled225_radical']=a.audit(ROOT/'inherited_pooled/source225.json',ROOT/'pooled225_radical')
 output['profiles']['pooled220_sheared']=audit_shears()
 for name,source in [('pooled219_affine','pooled220_sheared'),('pooled218_affine','pooled219_affine')]:
  output['profiles'][name]=a.audit_affine(ROOT/source/'equation.json',ROOT/name)
 for name,source in [('pooled225_radical_reduced','pooled225_radical'),('pooled220_sheared_reduced','pooled220_sheared'),('pooled219_reduced','pooled219_affine'),('pooled218_reduced','pooled218_affine')]:
  if (ROOT/name/'equation.json').exists():output['profiles'][name]=a.audit_rows(ROOT/source/'equation.json',ROOT/name)
 for base in ['pooled218','pooled219','pooled220']:
  source={'pooled218':'pooled218_affine','pooled219':'pooled219_affine','pooled220':'pooled220_sheared'}[base]
  for d in sorted(ROOT.glob(base+'_height*')):output['profiles'][d.name]=a.audit_rows(ROOT/source/'equation.json',d)
 source223=ROOT/'pooled223_source.json'
 require(hashlib.sha256(source223.read_bytes()).hexdigest()==read(ROOT/'POOLED223_SOURCE.json')['sha256'],'pooled223 source file binding')
 output['profiles']['pooled223_radical']=a.audit(source223,ROOT/'pooled223_radical')
 for d in sorted(ROOT.glob('pooled217_*')):
  if (d/'row_certificate.json').exists():output['profiles'][d.name]=a.audit_rows(ROOT/'pooled223_radical/equation.json',d)
 for name,entry in output['profiles'].items():
  target=read(ROOT/name/'equation.json');expansion=a.expanded_sos(target)
  used={i for mon in expansion for i in mon}
  require(used==set(range(len(target['variables']))),'unused declared coordinate: '+name)
  entry['live_coordinates']=len(used)
 text=json.dumps(output,indent=2,sort_keys=True)+'\n'
 if args.receipt:args.receipt.write_text(text)
 print(text,end='')

if __name__=='__main__':main()
