#!/usr/bin/env python3
"""Independent raw-row audit, exact projection/coefficients, and isolated rebuild."""
from pathlib import Path
from collections import defaultdict
from copy import deepcopy
import argparse,hashlib,importlib.util,json,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent

def require(ok,msg):
 if not ok:raise ValueError(msg)
def collect(terms):
 d=defaultdict(int)
 for c,m in terms:d[tuple(sorted(m))]+=c
 return [[c,list(m)] for m,c in sorted(d.items()) if c]
def translate(terms,shifted):
 result=[]
 for c,m in terms:
  products=[(c,[])]
  for v in m:
   factors=[(1,[v]),(1,[])] if v in shifted else [(1,[v])]
   products=[(a*b,ma+mb) for a,ma in products for b,mb in factors]
  result+=products
 return collect(result)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def module(name,p):
 sp=importlib.util.spec_from_file_location(name,p);o=importlib.util.module_from_spec(sp);sp.loader.exec_module(o);return o
check=module('independent_psd_check',ROOT/'inherited/check.py')

def raw_audit(source,target,staged):
 names={v['name']:i for i,v in enumerate(source['variables'])}
 require(len(source['variables'])==343 and len(source['residuals'])==291,'Pinned raw dimensions')
 for n,i in {'y':2,'pow0.output':6,'endpoint.r0':11,'shared.W':169,'shared.lower_A':170,'shared.A_slack':171,'index_cap.Y':180,'index_cap.error_square_quotient':338,'index_cap.range_error_quotient':339}.items():require(names[n]==i,'Pinned coordinate '+n)
 removed={333,334,335,336,337,11}|({339} if not staged else set())
 kept=[i for i in range(343) if i not in removed];rename={v:i for i,v in enumerate(kept)}
 variables=[deepcopy(source['variables'][i]) for i in kept]
 variables[rename[6]]['name']='pow0.output_minus_one'
 require(variables==target['variables'],'Target coordinate list')
 indexed={r['label']:r for r in source['residuals'] if r['label'].startswith('index_cap.squared_index_errors.')}
 error0=[(c,m) for c,m in indexed['index_cap.squared_index_errors.0']['terms'] if 338 not in m]
 error1=[(c,m) for c,m in indexed['index_cap.squared_index_errors.1']['terms'] if 339 not in m]
 late=[[16,[]],[1,[16]],[5,[17]],[1,[18]],[1,[19]],[1,[20]],[1,[21]],[1,[22]],[1,[23]],[1,[24]],[2,[29]],[1,[155]]]
 # Independently read each intended upper index from the ten cross terms -2*e*Y.
 actual=[]
 for j in range(5,15):
  yi=names['index'+str(j)+'.Y']
  for c,m in error1:
   if yi in m and m!=[yi,yi]:
    require(c%2==0,'Even cross coefficient');mm=m.copy();mm.remove(yi);actual.append((-c//2,mm))
 require(collect(actual)==collect(late),'Literal ten-index frame enlargement')
 expected=[];unmodified=0
 for r in source['residuals']:
  lab=r['label'];p=translate(r['terms'],{6,171})
  if any(v in {333,334,335,336,337} for c,m in p for v in m):continue
  if lab=='endpoint.first_remainder':lab='endpoint.cofinal_linear_modulus';p=collect([(1,[2]),(-1,[6])])
  elif lab=='shared.frame_definition':
   p=collect([(c if m==[169] else 2*c,m) for c,m in p]+([] if staged else [(-2*c,m) for c,m in late]))
  elif lab=='index_cap.squared_index_errors.0':
   lab='index_cap.staged_one_row_cap.0' if staged else 'index_cap.one_row_all_indices'
   p=collect(error0+([] if staged else error1)+[(1,[170,338]),(1,[171,338]),(1,[169]),(-1,[180])])
  elif lab=='index_cap.squared_index_errors.1':
   if not staged:continue
   lab='index_cap.staged_one_row_cap.1'
   p=collect(error1+[(1,[170,339]),(1,[171,339]),(1,[169]),(-1,[180])])
  else:unmodified+=1
  require(not any(v in removed for c,m in p for v in m),'No deleted-coordinate leak')
  expected.append({'label':lab,'terms':collect([(c,[rename[v] for v in m]) for c,m in p])})
 require(expected==target['residuals'],'Complete raw-row transformation')
 require(target['domain']=='nonnegative integers','Domain')
 require(sum(r['label'].startswith('index') and r['label'].endswith('.norm1') for r in expected)>=15,'Principal norms retained')
 return {'all_raw_rows_checked':len(expected),'all_raw_variables_checked':len(variables),'unchanged_rows_after_two_translations':unmodified,'frame_multiplier':2,'source_index_groups':[5,10],'mode':'two staged cap rows' if staged else 'one full-frame cap row'}

def run(rebuild=False):
 ledger=json.loads((ROOT/'SOURCE_LEDGER.json').read_text())
 for f in ledger['files']:require(digest(ROOT/f['local'])==f['sha256'],'Inherited hash '+f['local'])
 source=json.loads((ROOT/'inherited/source_equation.json').read_text())
 summary={}
 for name,staged,expected in [('natural235',False,(235,184,22185,90911633)),('natural236_sparse',True,(236,185,15645,88233865))]:
  d=ROOT/'equations'/name
  raw,target,cert,poly=[json.loads((d/f).read_text()) for f in ['raw/equation.json','equation.json','elimination_certificate.json','expanded_polynomial.json']]
  audit=raw_audit(source,raw,staged)
  receipt,terms=check.verify(raw,target,cert)
  require(poly['terms']==terms,'Complete polynomial expansion')
  require(len(target['variables'])==expected[0] and len(target['residuals'])==expected[1],'Counts')
  require(len(terms)==expected[2] and max(abs(c) for c,m in terms)==expected[3],'Support/height')
  require(max(len(m) for c,m in terms)==4,'Exact quartic degree')
  controls=[]
  for label in ['shared.frame_definition','endpoint.cofinal_linear_modulus','index_cap.staged_one_row_cap.0' if staged else 'index_cap.one_row_all_indices']:
   bad=deepcopy(raw);r=next(r for r in bad['residuals'] if r['label']==label);r['terms'][0][0]+=1
   try:raw_audit(source,bad,staged)
   except ValueError:controls.append(label)
   else:raise ValueError('Raw mutation accepted: '+label)
  corrupted=deepcopy(cert);corrupted['target_equation_sha256']='0'*64
  try:check.verify(raw,target,corrupted)
  except ValueError:controls.append('projection target hash')
  else:raise ValueError('Projection mutation accepted')
  summary[name]={'metrics':{'variables':expected[0],'rows':expected[1],'degree':4,'terms':expected[2],'height':expected[3]},'raw_audit':audit,'projection':receipt,'rejected_corruptions':controls,'equation_sha256':digest(d/'equation.json'),'polynomial_sha256':digest(d/'expanded_polynomial.json')}
 if rebuild:
  with tempfile.TemporaryDirectory(prefix='conzfc235-replay-') as td:
   dest=Path(td)/'equations'
   cmd=[sys.executable]+(['-O'] if sys.flags.optimize else [])+['-B',str(ROOT/'build.py'),'--output',str(dest)]
   subprocess.run(cmd,check=True,stdout=subprocess.DEVNULL)
   for name in summary:
    for f in ['raw/equation.json','raw/transformation.json','equation.json','elimination_certificate.json','expanded_polynomial.json','VERIFICATION.json']:
     require((dest/name/f).read_bytes()==(ROOT/'equations'/name/f).read_bytes(),'Byte rebuild '+name+'/'+f)
  summary['rebuild']='All twelve normative JSON files regenerated byte for byte in isolated directory'
 summary['mode']='optimized' if sys.flags.optimize else 'normal'
 summary['proof_boundary']='Finite exact algebra and artifact audit; unbounded arithmetic proof is proofs/PROOF.md plus named inherited calibration.'
 return summary
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--rebuild',action='store_true');p.add_argument('--receipt',type=Path);a=p.parse_args();r=run(a.rebuild)
 if a.receipt:a.receipt.write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps(r,indent=2))
