#!/usr/bin/env python3
"""No-Lean external K comparison with independent radix-polynomial rebuild."""
import ast,gzip,hashlib,json,os,pathlib,re,shutil,subprocess,sys,tempfile
if not __debug__ or sys.flags.optimize or not sys.flags.isolated or not sys.flags.no_site or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('isolated non-optimized Python required')
P=pathlib.Path; root=P.cwd(); base=root/'Computability/DiophantineConsistency'; pkg=base/'research/ordinary12-ipra-bridge/compact44-symbolic-k-external-byte-check'; script=pkg/'check.py'; obs=json.loads((pkg/'observation.json').read_bytes()); H=lambda p:hashlib.sha256(P(p).read_bytes()).hexdigest()
assert H(script)==obs['script_sha256']=='fecbee263c76f5a87d589d16e45f815845d4802534d3a8c6054d142012652e87'
files={
 'rows':('research/ordinary12-ipra-bridge/compact44-943-table-prototype/Compact943Data.lean','10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8'),
 'kernel':('research/ordinary12-ipra-bridge/compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean','f34e96b3d4df160c980632a426aee1340e5c06c93500e899b255610c317da7ae'),
 'param':('research/ordinary12-ipra-bridge/compact44-symbolic-kernel-param-prototype/CompactSymbolicKernelOpaque.lean','fbef8642de957bb39493607cb67edda418f53332af5a92ee594a2a437241e0b8'),
 'mass':('research/ordinary12-ipra-bridge/compact44-coefficient-mass-prototype/CompactCoefficientMass.lean','ca20b0796cbdd1b6c86e6032998fec7d5577b0f775b88d8395db349c7b1b2e6e'),
 'retained':('candidates/ten-positive-shifted-strong/coefficients/K.bin.gz','b70752bb38570b1e93d480469c63ace9ed4b4552f94eb89d96bc600b1e2a4b6a')}
for path,pin in files.values(): assert H(base/path)==pin
rawtext=(base/files['rows'][0]).read_text(); start='-- BEGIN PINNED ORDERED ROWS\n';end='\n-- END PINNED ORDERED ROWS';assert rawtext.count(start)==rawtext.count(end)==1
rows=ast.literal_eval('['+rawtext.split(start)[1].split(end)[0]+']');assert len(rows)==943
kernel=(base/files['kernel'][0]).read_text(); slots=ast.literal_eval('['+re.search(r'^def slots : List ℕ := \[([0-9,]+)\]$',kernel,re.M).group(1)+']');assert len(slots)==len(set(slots))==41 and max(slots)<4393
coeff={}
def add(exp,value): coeff[exp]=coeff.get(exp,0)+value
for exponent in (30,62,1100,2201): add(exponent,1)
for i,(w,n,e,s) in enumerate(rows):
 assert 0<=w<256 and 0<=n<512 and 0<=e<256 and 0<=s<512
 value=w+256*n+131072*e+33554432*s+127*17179869184
 assert 0<=value<2**41
 for target in (4393,5495):add(target-i,1+1024*(2**41-value))
for i,position in enumerate(slots):
 for target in (4393,5495):add(target-position,2**(10+i))
add(8807+42,1)
x=0
for exponent in range(max(coeff),-1,-1): x=(x<<67)+coeff.get(exponent,0)
raw=x.to_bytes((x.bit_length()+7)//8,'little');retained=gzip.decompress((base/files['retained'][0]).read_bytes()); assert raw==retained and len(raw)==74111 and x.bit_length()==592884 and hashlib.sha256(raw).hexdigest()=='c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e'
normal=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=root,capture_output=True,text=True,timeout=120); opt=subprocess.run([sys.executable,'-O','-I','-S','-B',str(script)],cwd=root,capture_output=True,text=True,timeout=120)
assert normal.returncode==0 and normal.stdout==obs['runs'][0]['stdout'] and normal.stderr=='' and obs['runs'][0]['exit_code']==0
assert opt.returncode==1 and opt.stdout=='' and 'ValueError: optimized Python rejected' in opt.stderr and obs['runs'][1]['exit_code']==1 and 'ValueError: optimized Python rejected' in obs['runs'][1]['stderr']
controls={}
with tempfile.TemporaryDirectory(prefix='compact-k-byte-review-') as tmp:
 shadow=P(tmp)/'DiophantineConsistency'; shadow_script=shadow/'research/ordinary12-ipra-bridge/compact44-symbolic-k-external-byte-check/check.py';shadow_script.parent.mkdir(parents=True);shutil.copyfile(script,shadow_script)
 for path,pin in files.values():
  dst=shadow/path;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(base/path,dst)
 for name,(path,pin) in files.items():
  f=shadow/path; original=f.read_bytes();f.write_bytes(original+b'\n')
  r=subprocess.run([sys.executable,'-I','-S','-B',str(shadow_script)],cwd=root,capture_output=True,text=True,timeout=120)
  assert r.returncode!=0 and r.stdout=='' and ('hash mismatch: '+name) in r.stderr
  controls[name]={'exit':r.returncode,'expected_hash_mismatch':True};f.write_bytes(original)
for path,pin in files.values():assert H(base/path)==pin
print(json.dumps({'status':'PASS_EXTERNAL_K_RECIPE_INDEPENDENT_REVIEW','reviewed_commit':'1dfc3e20e7','script_sha256':H(script),'source_pins':{k:v[1] for k,v in files.items()},'independent_method':'ast row/slot parse and radix-2^67 Horner polynomial','raw_bytes':len(raw),'raw_sha256':hashlib.sha256(raw).hexdigest(),'bit_length':x.bit_length(),'normal_exit':normal.returncode,'optimized_exit':opt.returncode,'tamper_controls':controls,'lean_launched':False,'scope':'External finite reconstruction only; no Lean kernel equality, serialization theorem, other port binding, machine semantics or internal PRA proof.'},indent=2,sort_keys=True))
