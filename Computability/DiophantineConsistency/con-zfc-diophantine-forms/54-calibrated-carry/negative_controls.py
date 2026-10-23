#!/usr/bin/env python3
"""Deliberate failures in temporary copies; never changes the sealed release."""
import sys
if not __debug__ or sys.flags.optimize:raise SystemExit('REJECT optimized Python')
import pathlib,tempfile,shutil,subprocess,json,hashlib
R=pathlib.Path(__file__).resolve().parent

def fails(args,cwd,needle):
 p=subprocess.run(args,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 if p.returncode==0 or needle not in p.stdout:raise RuntimeError('Failed negative control '+repr(args)+'\n'+p.stdout)
 return {'case':needle,'exit_code':p.returncode}

def main():
 rows=[]
 for opt in ['-O','-OO']:rows.append(fails([sys.executable,opt,str(R/'verify_release.py'),'--integrity-only'],R,'REJECT'))
 with tempfile.TemporaryDirectory(prefix='proveit-calibrated-negative-')as td:
  d=pathlib.Path(td)/'release';shutil.copytree(R,d)
  cmd=[sys.executable,str(d/'verify_release.py'),'--integrity-only']
  p=d/'native/beta.bin.gz';raw=p.read_bytes();p.write_bytes(bytes([raw[0]^1])+raw[1:]);rows.append(fails(cmd,d,'HASH FAILURE'));p.write_bytes(raw)
  p=d/'unexpected.tmp';p.write_text('unexpected');rows.append(fails(cmd,d,'FILE SET FAILURE'));p.unlink()
  p=d/'native/beta.bin.gz';p.unlink();rows.append(fails(cmd,d,'FILE SET FAILURE'));p.write_bytes(raw)
  cert=d/'packing/CERTIFICATE_170_selective12_packed.json';old=cert.read_bytes();obj=json.loads(old);obj['weights'][1]=obj['weights'][0];cert.write_text(json.dumps(obj))
  p=subprocess.run([sys.executable,str(d/'packing/verify_certificates.py'),str(cert)],cwd=d,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  if p.returncode==0:raise RuntimeError('Malformed packing certificate was accepted')
  rows.append({'case':'MALFORMED PACKING REJECT','exit_code':p.returncode});cert.write_bytes(old)
  p=d/'review/postpin/STATUS.md';p.write_bytes(p.read_bytes()+b'\ncorrupt\n');manifest=json.loads((d/'RELEASE_HASHES.json').read_text());manifest[p.relative_to(d).as_posix()]=hashlib.sha256(p.read_bytes()).hexdigest();(d/'RELEASE_HASHES.json').write_text(json.dumps(manifest))
  rows.append(fails(cmd,d,'SOURCE BLOB FAILURE'))
 print(json.dumps({'status':'PASS','negative_controls':rows},indent=2))
if __name__=='__main__':main()
