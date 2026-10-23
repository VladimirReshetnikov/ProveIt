"""Tamper controls and normal/-O parity for the independent checker."""
import tempfile,subprocess,sys,shutil,json,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def main():
 outputs=[]
 for opt in [[],['-O']]:
  r=subprocess.run([sys.executable,*opt,str(ROOT/'verify_certificates.py')],check=True,capture_output=True);outputs.append(r.stdout)
 if outputs[0]!=outputs[1]:raise RuntimeError('normal/-O receipts differ')
 mutations=[('weight',lambda d:d['weights'].__setitem__(0,d['weights'][1])),('target',lambda d:d['targets_by_row'].__setitem__(0,d['targets_by_row'][1])),('orientation',lambda d:d['row_orientations'].__setitem__(1,1)),('height',lambda d:d.__setitem__('convolution_height',d['convolution_height']+1)),('degree',lambda d:d['kernel_degrees'].__setitem__(0,0)),('source_hash',lambda d:d.__setitem__('source_sha256','0'*64))]
 count=0
 with tempfile.TemporaryDirectory() as tmp:
  work=Path(tmp)/'carry';work.mkdir();src=Path(tmp)/'source';src.mkdir()
  for f in ROOT.glob('*.json'):shutil.copy2(f,work/f.name)
  shutil.copy2(ROOT/'verify_certificates.py',work/'verify_certificates.py')
  for n in ['gapN86_source.json','gapNq85_source.json']:shutil.copy2(ROOT/'../source'/n,src/n)
  p=work/'gapNmirror116_H2057_code.json';original=p.read_bytes();kp=work/'gapNmirror116_H2057_kernels.json';ko=kp.read_bytes()
  for label,change in mutations:
   d=json.loads(original);change(d);p.write_text(json.dumps(d));kd=json.loads(ko);kd['code_sha256']=hashlib.sha256(p.read_bytes()).hexdigest();kp.write_text(json.dumps(kd))
   for opt in [[],['-O']]:
    r=subprocess.run([sys.executable,*opt,str(work/'verify_certificates.py')],capture_output=True)
    if r.returncode==0:raise RuntimeError('Tamper not rejected: '+label)
    count+=1
   p.write_bytes(original);kp.write_bytes(ko)
 print(json.dumps({'status':'PASS','normal_optimized_receipts_identical':True,'tamper_mutations':len(mutations),'rejected_runs':count},indent=2))
if __name__=='__main__':main()
