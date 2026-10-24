#!/usr/bin/env python3
import pathlib,tempfile,shutil,json,subprocess,sys
D=pathlib.Path(__file__).resolve().parent;source=D.parent/'direct/fixed_base';results=[]
with tempfile.TemporaryDirectory(prefix='direct-negative-') as td:
 r=pathlib.Path(td);sd=r/'direct/fixed_base';ad=r/'direct_audit/fixed_base';sd.mkdir(parents=True);ad.mkdir(parents=True)
 for p in source.glob('*.json'):shutil.copy2(p,sd/p.name)
 for p in (D/'fixed_base').glob('check_*.py'):shutil.copy2(p,ad/p.name)
 shutil.copy2(D/'check_affine.py',ad.parent/'check_affine.py')
 def run(case,file,change,script,args=[]):
  p=sd/file;original=p.read_bytes();j=json.loads(original);change(j);p.write_text(json.dumps(j));z=subprocess.run([sys.executable,str(script),*args],capture_output=True,text=True);p.write_bytes(original)
  if z.returncode==0:raise ValueError('accepted corruption '+case)
  if 'ValueError:' not in z.stderr:raise ValueError('unexpected failure '+case+' '+z.stderr)
  results.append({'case':case,'rejected':True,'reason':z.stderr.split('ValueError:')[-1].strip()})
 run('expanded coefficient','equation.json',lambda j:j['terms'][0].__setitem__(0,j['terms'][0][0]+1),ad/'check_structure.py')
 def badpower(j):
  e=next(x for x in j['equalities'] if x[2]=='natural power');e[0]=e[1]
 run('power tautology','circuit.json',badpower,ad/'check_interfaces.py')
 def badhorn(j):j['branches'][0]['quadratic_residuals'][0][0]['coefficient']=2
 run('Horn rule coefficient','horn_shared_source.json',badhorn,ad/'check_horn.py')
 def badsource(j):j['source_binding']['encoded_environment'][5]=0
 run('encoded row index alias','circuit.json',badsource,ad/'check_source_binding.py')
 def badchoose(j):next(x for x in j['call_ledger'] if x['kind']=='choose')['result']=0
 run('binomial result alias','circuit.json',badchoose,ad/'check_composition.py')
 def badaffine(j):j['node_affine_forms'][0][0][0]+=1
 run('affine substitution coefficient','affine_map.json',badaffine,ad.parent/'check_affine.py',['--fixed-base'])
(D/'NEGATIVE_CHECKS.json').write_text(json.dumps({'status':'PASS','controls':results},indent=2)+'\n');print(json.dumps(results))
