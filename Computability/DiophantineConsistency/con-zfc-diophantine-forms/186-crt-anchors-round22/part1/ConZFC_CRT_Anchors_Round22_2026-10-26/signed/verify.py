#!/usr/bin/env python3
"""Independent coefficient and integer-map verification; no imports from build.py."""
import argparse,copy,hashlib,json,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import operations_audit as A,audit_projection as P

def need(ok,msg):
 if not ok:raise ValueError(msg)
def read(p):return json.loads((ROOT/p).read_text())
def digest(x):return hashlib.sha256((json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest()
def rows(e):return[A.collect(r['terms'])for r in e['residuals']]
def compare(e,n,rs,msg):need(e['variables']==n and rows(e)==rs,msg)
def source(name,override=None):
 original=read('inherited_anchor/source/anchor221/equation.json');target=override if override is not None else read(f'stages/{name}_source/equation.json');expected=copy.deepcopy(original)
 n={v['name']:i for i,v in enumerate(original['variables'])};k=n['growth.index'];t2=n['growth.t_squared'];z=n['cofinal.horizon_root'];c,h,degree=(32,32,4)if name=='weighted'else(1024,1024,2)
 need(h>=16 and h%4==0 and c*h**(degree-1)>=2**20,'majorant contract')
 changed=[];remaining=[]
 for j,r in enumerate(expected['residuals']):
  p=A.collect(r['terms'])
  if r['label']=='cofinal.horizon':
   need(p=={():-128,(0,):1,(z,z):-4},'exact horizon row');p[()]=-h;changed.append(j)
  elif r['label']=='growth.index':
   need(p=={(k,):1,(t2,t2):-1},'exact old index row');p={(k,):1,(t2,t2)if degree==4 else(0,0):-c};changed.append(j)
  elif r['label']=='growth.t_squared'and degree==2:
   need(p=={(t2,):1,(0,0):-1},'private square definition');changed.append(j);continue
  r['terms']=[[a,list(m)]for m,a in sorted(p.items())];remaining.append(r)
 expected['residuals']=remaining
 if degree==2:
  need(t2==len(expected['variables'])-1 and all(t2 not in m for r in remaining for _,m in r['terms']),'only private square wire removed');expected['variables'].pop()
 expected['variant']+=(':weighted_quartic_c32_h32'if degree==4 else':quadratic_growth_1024')
 need(expected==target,'complete source delta');need(len(changed)==(2 if degree==4 else 3),'edit census')
 return target,{'growth_degree':degree,'multiplier':c,'horizon':h,'majorant_margin':c*h**(degree-1)-2**20,'changed_rows':changed}

def row_check(e,certificate,output=None):
 need(digest(e)==certificate['input_sha256'],'row input hash');before=rows(e);rs=copy.deepcopy(before)
 for i,j,k in certificate['operations']:
  need(type(i)is int and type(j)is int and type(k)is int and 0<=i<len(rs)and 0<=j<len(rs)and i!=j,'row operation wellformed')
  rs[i]=A.linear(rs[i],rs[j],k)
 reverse=copy.deepcopy(rs)
 for i,j,k in reversed(certificate['operations']):reverse[i]=A.linear(reverse[i],reverse[j],-k)
 need(reverse==before,'composed inverse row basis')
 if output is not None:
  compare(output,e['variables'],rs,'row target');need(digest(output)==certificate['output_sha256'],'row output hash')
 return rs

def endpoint(name,e):
 target=read(f'{name}/equation.json');need(target==e,'endpoint equation identity');n=len(e['variables']);rs=rows(e);expanded={}
 for p in rs:expanded=A.linear(expanded,A.multiply(p,p),1)
 delivered=read(f'{name}/expanded_polynomial.json');need(delivered['variables']==n and A.collect(delivered['terms'])==expanded,'full collected coefficients')
 need({i for m in expanded for i in m}==set(range(n)),'no dead coordinates')
 metric={'variables':n,'rows':len(rs),'residual_terms':sum(map(len,rs)),'row_height':max(abs(c)for p in rs for c in p.values()),'degree':max(map(len,expanded)),'monomials':len(expanded),'height':max(map(abs,expanded.values()))}
 need(read(f'{name}/metrics.json')==metric,'metric reconstruction')
 return metric

def run(deep=False):
 receipts={};controls=[]
 for rel,expected in read('SOURCE_PINS.json').items():need(hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==expected,'source byte pin '+rel)
 if (ROOT/'MANIFEST_SHA256.json').exists():
  for rel,expected in read('MANIFEST_SHA256.json').items():need(hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==expected,'manifest '+rel)
 for name in ['weighted','quadratic']:
  src,semantic=source(name);e=copy.deepcopy(src)
  bad=copy.deepcopy(src);bad['residuals'][0]['terms'][0][0]+=1
  try:source(name,bad)
  except ValueError:controls.append(name+':unrelated_source_coefficient')
  else:raise ValueError('accepted unrelated source change')
  for v in e['variables']:
   if v['name']=='growth.F':v['name']='crt.growth_majorant_F'
  ops=read(f'stages/{name}_transport/operations.json');ns,rs,count=A.replay(e['variables'],rows(e),ops);e=read(f'stages/{name}_transport/equation.json');compare(e,ns,rs,'independent transport');need(e['variant']=='anchor221_round21_transport','transport tag')
  cert=read(f'stages/{name}_radical/projection_certificate.json')
  for step in cert['steps']:e=P.one_step(e,step)
  need(e==read(f'stages/{name}_radical/equation.json'),'independent radical target')
  for role in (['sparse','norm']if name=='weighted'else['sparse']):
   target=read(f'stages/{name}_{role}/equation.json');row_check(e,read(f'stages/{name}_{role}/row_certificate.json'),target)
   for endpoint_name,desc in read('ENDPOINTS.json').items():
    if desc['profile']!=name or desc['basis']!=role:continue
    final=target
    if desc.get('height_certificate'):
     final=read(f'{endpoint_name}/equation.json');row_check(target,read(desc['height_certificate']),final)
    receipts[endpoint_name]=endpoint(endpoint_name,final)
  # Deliberate source, nonlinear projection, and row corruption controls.
  bad=copy.deepcopy(cert['steps'][0]);bad['direction'][0][1]+=1
  try:P.one_step(read(f'stages/{name}_transport/equation.json'),bad)
  except (ValueError,KeyError):controls.append(name+':radical_direction')
  else:raise ValueError('accepted corrupt radical')
  bad=copy.deepcopy(read(f'stages/{name}_sparse/row_certificate.json'));bad['operations'][0][2]+=1
  try:row_check(e,bad,read(f'stages/{name}_sparse/equation.json'))
  except ValueError:controls.append(name+':row_scalar')
  else:raise ValueError('accepted corrupt row scalar')
  semantic.update(operation_counts=count,radical_projections=len(cert['steps']));receipts[name+'_source']=semantic
 command=[sys.executable,'-B']+(['-O']if sys.flags.optimize else[])
 for script,args in [(ROOT/'build.py',['--check']),(ROOT/'coordinate_maps.py',['check'])]+([(ROOT/'inherited_anchor/verify.py',[])]if deep else[]):
  z=subprocess.run(command+[str(script)]+args,capture_output=True,text=True,cwd=script.parent);need(z.returncode==0,'reconstruction '+str(script)+'\n'+z.stdout+'\n'+z.stderr)
  receipts[script.parent.name+'/'+script.name]=json.loads(z.stdout)
 return {'status':'PASS','optimized':bool(sys.flags.optimize),'deep':deep,'results':receipts,'negative_controls':controls,'scope':'Exact finite source deltas, integer projections and inverse identities, collected coefficients, and reconstruction; ordinary unbounded CRT/Pell/calibration proof is separate.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--deep',action='store_true');ap.add_argument('--receipt',type=Path);args=ap.parse_args();result=run(args.deep)
 if args.receipt:args.receipt.parent.mkdir(parents=True,exist_ok=True);args.receipt.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
