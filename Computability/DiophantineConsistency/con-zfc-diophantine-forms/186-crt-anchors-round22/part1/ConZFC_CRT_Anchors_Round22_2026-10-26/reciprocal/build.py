#!/usr/bin/env python3
"""Reconstruct the literal 212-variable decic from the frozen weighted source."""
import argparse,copy,hashlib,json,sys,tempfile,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SIGNED=ROOT.parent/'signed'
binding=json.loads((ROOT/'SOURCE_BINDING.json').read_text())
if binding['relative_component']!='../signed':raise ValueError('noncanonical signed component')
manifest=SIGNED/'MANIFEST_SHA256.json'
if not manifest.is_file():raise ValueError('Extract both ordinary archive parts beside each other: reciprocal212 requires sibling signed/')
if hashlib.sha256((SIGNED/'stages/weighted_source/equation.json').read_bytes()).hexdigest()!=binding['equation_sha256']:raise ValueError('wrong weighted source')
if hashlib.sha256(manifest.read_bytes()).hexdigest()!=binding['manifest_sha256']:raise ValueError('wrong frozen signed manifest')
for relative,expected in json.loads(manifest.read_text()).items():
 if Path(relative).is_absolute()or'..'in Path(relative).parts:raise ValueError('unsafe signed manifest path')
 if hashlib.sha256((SIGNED/relative).read_bytes()).hexdigest()!=expected:raise ValueError('signed source mismatch: '+relative)
sys.path.insert(0,str(SIGNED/'code'));sys.path.insert(0,str(ROOT/'code'))
import operations as O,reduce_radical as R,build_reciprocal as M

def read(p):
 p=str(p);base=SIGNED if p.startswith('inherited_signed/')else ROOT;p=p.removeprefix('inherited_signed/');return json.loads((base/p).read_text())
def put(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(O.raw(x))
def restricted_source(e):
 e=copy.deepcopy(e);names={v['name']:i for i,v in enumerate(e['variables'])};qplus=names['pow2.output']
 for row in e['residuals']:row['terms']=O.terms(O.subst(O.poly(row['terms']),qplus,{(qplus,):3,():2}))
 e['variables'][qplus]['name']='radix.chart_q_third';e['variant']+=':restricted_q_1_mod_3';return e

def label_pools(e):
 e=copy.deepcopy(e);names={v['name']:i for i,v in enumerate(e['variables'])};rs=[O.poly(r['terms'])for r in e['residuals']]
 for group in ['radix','radix_plus_one']:
  K,L=names[group+'.K'],names[group+'.L'];hits=[j for j,p in enumerate(rs)if any(K in m or L in m for m in p)]
  O.need(len(hits)==2,'private pool rows');a=next(j for j in hits if rs[j].get((K,))==1);b=next(j for j in hits if j!=a)
  e['residuals'][a]['label']=group+'.bilinear_aggregate';e['residuals'][b]['label']=group+'.pooled_norm'
 return e

def run(out):
 command=[sys.executable,'-B']+(['-O']if sys.flags.optimize else[])
 with tempfile.TemporaryDirectory(prefix='reciprocal-parent-')as td:
  z=subprocess.run(command+[str(SIGNED/'build.py'),'--output',td],capture_output=True,text=True);O.need(z.returncode==0,z.stderr)
  e=json.loads((Path(td)/'stages/weighted_source/equation.json').read_text());O.need(e==read('inherited_signed/stages/weighted_source/equation.json'),'reconstructed weighted source')
 e=restricted_source(e);put(out/'stages/source.json',e)
 for v in e['variables']:
  if v['name']=='growth.F':v['name']='crt.growth_majorant_F'
 for ops in read('stages/transport_operations.json'):e=O.stage(e,ops)
 e['variant']='anchor221_round21_transport';put(out/'stages/transport.json',e)
 for cert in read('stages/radical_certificate.json')['steps']:
  direction=[0]*len(e['variables'])
  for i,c in cert['direction']:direction[i]=c
  e,actual=R.project(e,direction,cert['pivot'],cert['deleted_row']);O.need(actual==cert,'radical certificate')
 put(out/'stages/radical.json',e);e=label_pools(e);put(out/'stages/pool_parent.json',e)
 final,certificate=M.compile_reciprocal(e);expanded=M.expanded(final);metric=M.metrics(final,expanded)
 put(out/'equations/equation.json',final);put(out/'equations/certificate.json',certificate);put(out/'equations/expanded_polynomial.json',{'schema':'sparse-polynomial-v1','variables':len(final['variables']),'terms':M.serial(expanded)});put(out/'equations/metrics.json',metric)
 return out

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);ap.add_argument('--check',action='store_true');args=ap.parse_args()
 if args.check:
  with tempfile.TemporaryDirectory(prefix='reciprocal-rebuild-')as td:
   out=run(Path(td));files=[]
   for p in out.rglob('*.json'):
    rel=p.relative_to(out);O.need(p.read_bytes()==(ROOT/rel).read_bytes(),'byte reconstruction '+str(rel));files.append(str(rel))
   print(json.dumps({'status':'PASS','reconstructed_files':files},indent=2))
 else:run(args.output or ROOT)
if __name__=='__main__':main()
