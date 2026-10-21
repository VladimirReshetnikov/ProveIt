from pathlib import Path
import json,shutil,tempfile,subprocess,sys
D=Path(__file__).parent
results=[]
for kind in('changed_exit','changed_source_child','missing_branch','bad_pin'):
 with tempfile.TemporaryDirectory()as t:
  p=Path(t)
  for f in D.iterdir():
   if f.is_file():shutil.copy(f,p/f.name)
  shutil.copytree(D/'inputs',p/'inputs')
  name='pins.json'if kind=='bad_pin'else 'K215_DECODER_MACROS.json'if kind=='changed_exit'else'K215_DECODER_PRODUCT.json'
  f=p/name;x=json.loads(f.read_text())
  if kind=='bad_pin':x['K215']['table_sha256']='0'*64
  elif kind=='changed_exit':x['templates'][0]['output_state']+=1
  elif kind=='missing_branch':x['edges'].pop()
  else:
   e=next(e for e in x['edges']if e['result'][0]=='next');e['result'][1]+=1
  f.write_text(json.dumps(x));r=subprocess.run([sys.executable,str(p/'check_decoder.py')],capture_output=True)
  assert r.returncode!=0,kind
  results.append(dict(mutation=kind,rejected=True))
print(json.dumps(results))
