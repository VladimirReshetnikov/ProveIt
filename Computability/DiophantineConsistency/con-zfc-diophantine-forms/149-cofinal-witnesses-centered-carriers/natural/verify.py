#!/usr/bin/env python3
"""Read-only exact independent verification and optional offline rebuild."""
from pathlib import Path
from copy import deepcopy
from hashlib import sha256
import argparse,json,subprocess,sys,tempfile
sys.dont_write_bytecode=True
import check_source as delta
import check_natural as contraction
import render_equation as render
import check_row_basis as rowbasis
ROOT=Path(__file__).resolve().parent
ENDPOINTS={'projected221':('raw',(221,172,6561,83878986)),
 'dimension219':('cofinal_raw',(219,171,9253,560710452)),
 'cofinal221':('cofinal_raw',(221,173,6269,83847181))}
def require(ok,msg):
 if not ok:raise ValueError(msg)
def read(p):return json.loads(p.read_text())
def command(script,*args):
 return subprocess.run([sys.executable,'-B']+([] if __debug__ else ['-O'])+[str(script)]+list(map(str,args)),check=True,text=True,capture_output=True).stdout

def negative_controls(parent,raw,dc,co,cc,endpoint,cert):
 passed=[]
 def rejects(name,fn):
  try:fn()
  except (ValueError,KeyError,IndexError,TypeError):passed.append(name)
  else:raise ValueError('failed negative control '+name)
 bad=deepcopy(raw);bad['domain']='integers';rejects('natural domain not silently widened',lambda:delta.verify(parent,bad,dc))
 bad=deepcopy(raw);r=next(r for r in bad['residuals'] if r['label']=='index_cap.positive_comparison_center');r['terms'][0][0]+=1
 rejects('positive center coefficient corruption',lambda:delta.verify(parent,bad,dc))
 bad=deepcopy(raw);r=next(r for r in bad['residuals'] if r['label']=='pooled_digits.t');r['terms'].pop()
 rejects('missing pooled remainder',lambda:delta.verify(parent,bad,dc))
 bad=deepcopy(cc);bad['old_t0_equals']=[2,-7];rejects('wrong cofinal horizon',lambda:delta.verify_cofinal(raw,co,bad))
 bad=deepcopy(co);r=next(r for r in bad['residuals'] if r['label']=='endpoint.cofinal_beta_bound');r['terms'][0][0]+=1
 bc=deepcopy(cc);bc['target_sha256']=sha256(delta.canonical(bad)).hexdigest()
 rejects('cofinal equation altered even with refreshed hash',lambda:delta.verify_cofinal(raw,bad,bc))
 bc=deepcopy(cert);bc['steps'][0]['restoration'][0][0]+=1
 rejects('natural restoration identity corruption',lambda:contraction.verify(raw,endpoint,bc))
 bc=deepcopy(cert);step=next(s for s in bc['steps'] if s['nonnegative_certificate']['squares']);step['nonnegative_certificate']['squares'][0]['weight'][0]*=-1
 rejects('negative square weight',lambda:contraction.verify(raw,endpoint,bc))
 return passed

def main():
 p=argparse.ArgumentParser();p.add_argument('--rebuild',action='store_true');p.add_argument('--output',type=Path);a=p.parse_args()
 out={'status':'PASS','scope':'Exact finite source mutations, natural restorations, every collected coefficient and rendered residual. Ordinary unbounded proofs/calibration are separate.'}
 sm=read(ROOT/'SOURCE_MAP.json')
 for item in sm['files']:require(sha256((ROOT/item['path']).read_bytes()).hexdigest()==item['sha256'],'source pin '+item['path'])
 out['pinned_inherited_files']=len(sm['files'])
 parent=read(ROOT/'inherited/descending18/source/equation.json');raw=read(ROOT/'raw/equation.json');dc=read(ROOT/'raw/transformation.json')
 rec,exp=delta.verify(parent,raw,dc);require(exp==read(ROOT/'raw/expanded_polynomial.json')['terms'],'raw expansion');out['composition']=rec
 co=read(ROOT/'cofinal_raw/equation.json');cc=read(ROOT/'cofinal_raw/transformation.json')
 rec,exp=delta.verify_cofinal(raw,co,cc);require(exp==read(ROOT/'cofinal_raw/expanded_polynomial.json')['terms'],'cofinal expansion');out['cofinal_source']=rec
 out['endpoints']={}
 for name,(source,metrics) in ENDPOINTS.items():
  d=ROOT/name;eq=read(d/'equation.json');cert=read(d/'elimination_certificate.json')
  rec,exp=contraction.verify(read(ROOT/source/'equation.json'),eq,cert)
  require(exp==read(d/'expanded_polynomial.json')['terms'],'endpoint expansion '+name)
  require(tuple(rec[k] for k in ['variables','rows','expanded_monomials','coefficient_height'])==metrics,'endpoint metrics '+name)
  met=eq['metrics']
  require((met['variables'],met['quadratic_rows'],met['expanded_monomials'],met['max_abs_expanded_coefficient'])==metrics,'embedded metrics '+name)
  require(met['exact_degree']==4 and all(type(c)is int and len(m)<=2 for r in eq['residuals'] for c,m in r['terms']),'ordinary quartic '+name)
  for f,t in render.generate(eq).items():require((d/f).read_text()==t,'literal render '+name+'/'+f)
  render.ROOT=d;rec['parsed_tex_rows']=render.parse_tex(eq);out['endpoints'][name]=rec
 out['row_basis']={}
 for name,origin,metrics in [('natural219','dimension219',(219,171,8267,130686428)),('sparse221','cofinal221',(221,173,5253,65867916)),('balanced221','projected221',(221,172,5586,65892620))]:
  d=ROOT/name;sourcepath=ROOT/origin/'equation.json';rc=read(d/'row_basis_certificate.json')
  require(rc['source']==origin+'/equation.json' and rc['source_sha256']==sha256(sourcepath.read_bytes()).hexdigest(),'row source binding '+name)
  met,lead,exp=rowbasis.verify(read(sourcepath),rc)
  require(rc['equation']==read(d/'equation.json'),'row certificate equation '+name)
  require(read(d/'operations.json')==rc['operations'],'row operations '+name)
  require(tuple(met[k] for k in ['variables','rows','terms','height'])==metrics,'row endpoint metrics '+name)
  require(read(d/'expanded_polynomial.json')==dict(schema='sparse_integer_polynomial_v1',domain='nonnegative integers',variables=metrics[0],terms=[[c,list(m)] for m,c in sorted(exp.items())]),'row SOS '+name)
  eq=rc['equation']
  for f,t in render.generate(eq).items():require((d/f).read_text()==t,'final literal render '+name+'/'+f)
  render.ROOT=d;render.parse_tex(eq)
  out['row_basis'][name]=json.loads(command(ROOT/'check_row_basis.py',sourcepath,d/'row_basis_certificate.json'))
 out['negative_controls']=negative_controls(parent,raw,dc,co,cc,read(ROOT/'projected221/equation.json'),read(ROOT/'projected221/elimination_certificate.json'))
 # Independently replay the complete retained source/compiler closure as well.
 out['inherited']=json.loads(command(ROOT/'inherited/descending18/verify.py',*(['--rebuild'] if a.rebuild else [])))
 if a.rebuild:
  with tempfile.TemporaryDirectory(prefix='natural-round19-') as tmp:
   d=Path(tmp)/'rebuild';command(ROOT/'build.py','--output',d)
   files=[]
   for name in ['raw','cofinal_raw']:
    for f in ['equation.json','expanded_polynomial.json','transformation.json']:
     require((d/name/f).read_bytes()==(ROOT/name/f).read_bytes(),'raw byte rebuild '+name+'/'+f);files.append(name+'/'+f)
   for name in ENDPOINTS:
    for f in ['equation.json','expanded_polynomial.json','elimination_certificate.json','VERIFICATION.json']:
     require((d/name/f).read_bytes()==(ROOT/name/f).read_bytes(),'endpoint byte rebuild '+name+'/'+f);files.append(name+'/'+f)
   for name in ['natural219','sparse221','balanced221']:
    for f in ['equation.json','expanded_polynomial.json','row_basis_certificate.json']:
     require((d/name/f).read_bytes()==(ROOT/name/f).read_bytes(),'row byte rebuild '+name+'/'+f);files.append(name+'/'+f)
   out['byte_identical_rebuild']=files
 if a.output:a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
 print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
