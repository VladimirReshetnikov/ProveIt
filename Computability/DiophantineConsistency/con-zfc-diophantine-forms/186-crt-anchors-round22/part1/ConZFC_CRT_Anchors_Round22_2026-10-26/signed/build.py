#!/usr/bin/env python3
"""Deterministically reconstruct the Round22 weighted-index direct equations."""
import argparse,copy,hashlib,json,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import operations as O,reduce_radical as R

def read(p):return json.loads(p.read_text())
def put(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(O.raw(x))
def profile(base,name):
 e=copy.deepcopy(base);names={v['name']:i for i,v in enumerate(e['variables'])};K=names['growth.index'];T=names['growth.t_squared'];rows=[];changed=[]
 c,h=(32,32)if name=='weighted'else(1024,1024)
 O.need(name in ['weighted','quadratic'],'profile name');O.need(h>=16 and h%4==0,'horizon condition')
 O.need(c*h**(3 if name=='weighted'else 1)>=2**20,'growth majorization')
 for j,r in enumerate(e['residuals']):
  if r['label']=='cofinal.horizon':
   O.need(O.poly(r['terms'])=={():-128,(0,):1,(names['cofinal.horizon_root'],names['cofinal.horizon_root']):-4},'horizon source')
   r['terms']=[[(-h if not m else a),m]for a,m in r['terms']];changed.append(j)
  if r['label']=='growth.index':
   O.need(O.poly(r['terms'])=={(K,):1,(T,T):-1},'index source')
   r['terms']=O.terms({(K,):1,((T,T)if name=='weighted'else(0,0)):-c});changed.append(j)
  if name=='quadratic'and r['label']=='growth.t_squared':
   O.need(O.poly(r['terms'])=={(T,):1,(0,0):-1},'square source');changed.append(j);continue
  rows.append(r)
 O.need(len(changed)==(2 if name=='weighted'else 3),'exact semantic edits');e['residuals']=rows
 if name=='quadratic':
  O.need(T==len(e['variables'])-1 and all(T not in m for r in rows for _,m in r['terms']),'private square wire');e['variables'].pop()
 e['variant']+=(':weighted_quartic_c32_h32'if name=='weighted'else':quadratic_growth_1024')
 return e

def row_operations(e,cert,kind='integer_row_reduction'):
 O.need(R.digest(e)==cert['input_sha256'],'row input pin');new=copy.deepcopy(e);rs=[O.poly(r['terms'])for r in e['residuals']]
 for i,j,k in cert['operations']:O.need(i!=j and type(k)is int,'row operation');rs[i]=O.add(rs[i],rs[j],k)
 for r,p in zip(new['residuals'],rs):r['terms']=O.terms(p)
 new['variant']+=':'+kind;O.need(R.digest(new)==cert['output_sha256'],'row output pin');return new

def emit_endpoint(out,name,e):
 put(out/name/'equation.json',e);expanded,metrics=O.result(e)
 expanded={'schema':'sparse_integer_polynomial_v1','variables':len(e['variables']),'terms':expanded['terms']}
 put(out/name/'expanded_polynomial.json',expanded);put(out/name/'metrics.json',R.metric(e,True))

def run(out):
 # The inherited producer rebuilds the semantic anchor from pinned parent225,
 # rather than treating the delivered anchor221 coefficients as an oracle.
 with tempfile.TemporaryDirectory(prefix='round22-source-')as td:
  command=[sys.executable,'-B']+(['-O']if sys.flags.optimize else[])+[str(ROOT/'inherited_anchor/code/build_anchor.py'),'--output',td,'--quartic-index']
  z=subprocess.run(command,capture_output=True,text=True)
  O.need(z.returncode==0,'inherited source rebuild '+z.stderr)
  base=read(Path(td)/'equation.json');O.need(base==read(ROOT/'inherited_anchor/source/anchor221/equation.json'),'inherited source identity')
 for name in ['weighted','quadratic']:
  e=profile(base,name);put(out/'stages'/f'{name}_source/equation.json',e)
  for v in e['variables']:
   if v['name']=='growth.F':v['name']='crt.growth_majorant_F'
  for stage in read(ROOT/'stages'/f'{name}_transport/operations.json'):e=O.stage(e,stage)
  e['variant']='anchor221_round21_transport';put(out/'stages'/f'{name}_transport/equation.json',e)
  for cert in read(ROOT/'stages'/f'{name}_radical/projection_certificate.json')['steps']:
   direction=[0]*len(e['variables'])
   for i,c in cert['direction']:direction[i]=c
   e,actual=R.project(e,direction,cert['pivot'],cert['deleted_row']);O.need(actual==cert,'projection certificate')
  put(out/'stages'/f'{name}_radical/equation.json',e)
  for role in (['sparse','norm']if name=='weighted'else['sparse']):
   e2=row_operations(e,read(ROOT/'stages'/f'{name}_{role}/row_certificate.json'));put(out/'stages'/f'{name}_{role}/equation.json',e2)
   for endpoint,description in read(ROOT/'ENDPOINTS.json').items():
    if description['profile']!=name or description['basis']!=role:continue
    final=e2
    if description.get('height_certificate'):
     final=row_operations(final,read(ROOT/description['height_certificate']),'height_row_reduction')
    emit_endpoint(out,endpoint,final)
 return out

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);ap.add_argument('--check',action='store_true');args=ap.parse_args()
 if args.check:
  with tempfile.TemporaryDirectory(prefix='round22-build-')as td:
   out=run(Path(td));files=[]
   for f in out.rglob('*.json'):
    rel=f.relative_to(out);O.need(f.read_bytes()==(ROOT/rel).read_bytes(),'reconstruction '+str(rel));files.append(str(rel))
   print(json.dumps({'status':'PASS','reconstructed_files':files},indent=2))
 else:run(args.output or ROOT)
if __name__=='__main__':main()
