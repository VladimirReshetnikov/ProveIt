#!/usr/bin/env python3
"""Independent selected receipt and finite residue calculation, no Lean replay."""
import gzip,hashlib,json,math,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/direct-bfs-halt-canonical-packing-prototype';O=P/'observations/directbfshaltcanonical-attempt02';s=P/'DirectBFSHaltCanonicalPacking.lean'
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
t=json.loads((O/'terminal.json').read_text());root=pathlib.Path(t['output_root']);pins=t['pins']
need(t['exit']==0 and t['reason'] is None and pins==t['after'] and t['direct_imports']==t['direct_imports_after'],'receipt state')
need(sha(s)==pins['source']==sha(O/'source.txt')==sha(root/s.name),'source')
need(sha(P/'run.py')==pins['runner'] and sha(t['command'][0])==pins['lean'],'runner/lean')
need(sha(root/'DirectBFSHaltCanonicalPacking.olean')==t['object_sha256']=='31e3a8809bda91bf75c9b4accecb7dabaf257dfb32e070b6769f0dda00cd9654','object')
need(sha(O/'stdout')==t['stdout_sha256'] and sha(O/'stderr')==t['stderr_sha256'],'logs')
need((O/'stdout').read_text()=="'DirectBFSHaltCanonicalPacking.halt_pack' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (O/'stderr').read_text()=='','axioms/diagnostics')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==[x['module'] for x in t['direct_imports']],'imports')
for x in t['direct_imports']:
 rel=x['module'].replace('.','/')+'.olean';p=next((pathlib.Path(z)/rel for z in t['lean_path'].split(':') if (pathlib.Path(z)/rel).is_file()),None)
 need(p and p.resolve()==pathlib.Path(x['path']).resolve() and sha(p)==x['sha256'],'selected '+x['module'])
need(t['direct_imports'][0]['sha256']=='c1ad37e318c176a0ae9b46e3b0be74b5bcc813ae120a3636d282aaeba5726d86','packing provider')
for x in t['stage_receipts']:need(sha(x['path'])==x['sha256'],'stage receipt')
K=D/'candidates/ten-positive-qcube-product-square/coefficients/K.bin.gz';raw=gzip.decompress(K.read_bytes());need(hashlib.sha256(raw).hexdigest()=='0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f','kernel payload')
need(len(raw)==74111 and int.from_bytes(raw,'little').bit_length()==592884,'byte order')
L=590069*581197
# Independently stream little-endian bytes to avoid converting the payload to an integer.
kr=0
for byte in reversed(raw):kr=(256*kr+byte)%L
source=D/'research/direct-bfs-lean-kernel-prototype/DirectBFSSymbolicKernel.lean';slotsrc=D/'research/ordinary12-ipra-bridge/compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean'
need(sha(source)=='8a1cd03117bae77e3ed13a853f5bff658ba3acf6ef7dd77bff520cd5cc7f1129' and sha(slotsrc)=='f34e96b3d4df160c980632a426aee1340e5c06c93500e899b255610c317da7ae','kernel source')
z=source.read_text().split('def rows :',1)[1].split('theorem rows_length',1)[0];rows=[tuple(map(int,x)) for x in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)',z)]
slots=list(map(int,re.findall(r'\d+',slotsrc.read_text().split('def slots :',1)[1].split('theorem slots_length',1)[0])))
need(len(rows)==943 and len(slots)==41,'row/slot count')
total=sum(pow(2,67*e,L) for e in [30,62,1100,2201,8849])
for i,(w,n,e,south) in enumerate(rows):
 need(w<256 and n<512 and e<256 and south<512,'row field width')
 payload=w+(n<<8)+(e<<17)+(south<<25)+(127<<34); c=1+1024*((1<<41)-payload)
 total+=c*(pow(2,67*(4393-i),L)+pow(2,67*(5495-i),L))
for i,k in enumerate(slots):total+=(1<<(10+i))*(pow(2,67*(4393-k),L)+pow(2,67*(5495-k),L))
need(total%L==kr==264033855341,'kernel residue')
q=pow(2,590069,L);rho=pow(2,67*1063,L);gamma=(rho*(q*q-1)*(1+q*(kr+q)))%L
need(q==290226301192 and rho==298529384010 and gamma==299052170727 and math.gcd(gamma,L)==1 and pow(gamma,581196,L)==1,'controller residue')
need(kr!=284898815895,'kernels differ modulo L')
print(json.dumps({'status':'PASS','canonical_object_sha256':t['object_sha256'],'direct_imports':t['direct_imports'],'stage_receipts':len(t['stage_receipts']),'kernel_residue':kr,'modulus':L,'q':q,'rho':rho,'gamma':gamma,'gamma_gcd':math.gcd(gamma,L),'gamma_power':pow(gamma,581196,L),'lean_replayed':False},indent=2,sort_keys=True))
