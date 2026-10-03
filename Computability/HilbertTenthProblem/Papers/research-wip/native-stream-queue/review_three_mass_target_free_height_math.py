#!/usr/bin/env python3
"""Small independent mathematical challenge; no maintained compiler/API audit."""
import argparse
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path

PINS = {
 'three_mass_target_free_height_probe.py':'3086d72c884652e1fb8c6036d4c2537633caaaca803488e089c3dcb006659f8d',
 'three_mass_target_free_height_probe.json':'c612e2928b52dbfed2753d94aed2c75feab0d09ddb96ccfc644484cfe0f59b22',
 'three_mass_target_free_height_probe.md':'0019c51a0eb25902fd49019180911e756bdadb0a31726dadb3f9b4a4b9efa1da',
 'three_mass_unbounded_endpoint_projection.json':'a7856463c879e8c479facf713a66c0756705d84f0dd74639f28395227ebc2457',
 'three_mass_unbounded_endpoint_projection.md':'8a17b626dc4c2b3498614c0c2e8511c9adbd9765c4b3fd157f77a06d8174bd6c',
 'residue_affine_packed_history.md':'0b6c533e8ef6c26b3ed5419dbb2baa44bc1509255c4bcf5226e5f85d37683882',
 'three_mass_unbounded_interface.md':'d336c8c12d3328eb4b6857ee382f91b2c9363f50effba5a7b1bf75308f25df45',
 'native_binary_masked_selection63.md':'c2e08f2d9fdaaf2e17880d7a131254492afd7ef21b035985714734cbc158c53e',
 'native_pell_factored_first_coefficient.md':'b1ec2a04fc92fe41b3c84fb33c6b74931e7643259bdd570a0426ed9256c67528',
}

def check(cond, msg):
 if not cond: raise AssertionError(msg)

def verify(root, probe_root):
 blobs={}
 for name, pin in PINS.items():
  path=(probe_root/name) if name.startswith('three_mass_target_free_height_probe.') else (root/name)
  data=path.read_bytes()
  check(hashlib.sha256(data).hexdigest()==pin, 'pin '+name)
  blobs[name]=data
 parent=json.loads(blobs['three_mass_unbounded_endpoint_projection.json'])
 probe=json.loads(blobs['three_mass_target_free_height_probe.json'])
 counts=Counter(); forms=[]
 for oldform,new in zip(parent['forms'],probe['forms'],strict=True):
  old=oldform['packet']; check(old['variant']==new['variant'],'variant')
  h=old['interfaces']['height']; rows=old['source']; d={n:(op,a,b) for n,op,a,b in rows}
  first=d['bridge_height_without_time'][1]; K=old['mapping']['K']; qh=old['mapping']['halt']
  check(d[first]==('+','bridge_input','bridge_target'),'input/target sum')
  check(d['bridge_height_without_time']==('+',first,'height_slack'),'old eta')
  check(d['endpoint_raised_height']==('+','bridge_height_without_time',K),'old raise')
  check(d[h]==('+','endpoint_raised_height','T'),'old time')
  for name,consumer in [(first,'bridge_height_without_time'),('bridge_height_without_time','endpoint_raised_height'),('endpoint_raised_height',h),('height_slack','bridge_height_without_time')]:
   check([n for n,op,a,b in rows if name in (a,b)]==[consumer],'private cone')
   check(all(name not in pair for pair in old['comparisons']),'private comparison')
  rebuilt=[]
  for n,op,a,b in rows:
   if n in (first,'endpoint_raised_height'): continue
   if n=='bridge_height_without_time': op,a,b='+','bridge_input','height_slack'
   if n==h: op,a,b='+','bridge_height_without_time','T'
   rebuilt.append([n,op,a,b])
  check(rebuilt==new['source'],'literal two-addition change')
  check(old['comparisons']==new['comparisons'] and len(new['comparisons'])==19,'all comparisons')
  check(old['polynomial_source'][len(rows):]==new['polynomial_source'][len(rebuilt):],'same full finalizer tail')
  check(old['parameters']==new['parameters'] and old['auxiliaries']==new['auxiliaries'],'same coordinates')
  # Height affine coefficients in n0,y,T,eta,1, after the signed eta shift.
  before=[1,K,1,1,qh]; shift=[0,-K,0,0,-qh]
  check([a+b for a,b in zip(before,shift)]==[1,0,1,1,0],'signed height identity')
  m=old['mapping']['modulus']
  C=next(a for n,op,a,b in rows if op=='*' and b=='bridge_height_square')
  check(C>=max(4,m+1,2384*m+2,1+max(a+b for a,b in old['mapping']['table'])),'radix assumptions')
  check(C&(C-1)==0,'fixed dyadic C')
  for height in [2,4,8,16,32,128,1024]:
   B=C*height*height
   for duration in [1,2,3]:
    P=B**duration; J=(P-1)//(B-1); g=len({a for a,b in old['mapping']['table']})-1
    check((height-1)*J<P,'range lane')
    check((B-2*height)*J-g>0,'global slack')
    check(2384*m*height*height<B-1 and height<B-1,'clock no-wrap')
    check(m*height<B and 2384*height<B,'typed state/tick bounds')
    counts['actual_radix_boundary_cases']+=1
  counts['literal_height_cuts']+=1
  forms.append({'variant':new['variant'],'m':m,'C':C,'unchanged_comparisons':19,'removed_additions':2})
 # Independent complete small-word cancellation: nf is permitted any integer.
 # Divisibility checks existence of such an integer without assuming its sign.
 for B in range(2,7):
  for t in range(1,4):
   words=[(v,sum(d*B**i for i,d in enumerate(v))) for v in itertools.product(range(1,B),repeat=t)]
   for c,Cw in words:
    for n,Nw in words:
     for n0 in range(1,B):
      numerator=B*Nw+n0-Cw; P=B**t
      ok=numerator%P==0
      chronological=c[0]==n0 and all(n[i]==c[i+1] for i in range(t-1))
      check(ok==chronological,'complete low-digit cancellation')
      if ok: check(numerator//P==n[-1]>0,'positive terminal forced')
      counts['signed_target_cancellation_cases']+=1
      counts['chronological_cases']+=int(ok)
 # Independent concrete one-step nop and the two signed pullbacks.
 x,y,K,qi,qh=40,41,5,1,2
 n0=K*x+qi; nf=K*(y-1)+qh; T=192*y+8; height=8192; eta=height-n0-T
 check((n0,nf,T,eta,eta-nf,eta-K*y-qh)==(201,202,7880,111,-91,-96),'nop signed boundary')
 return {'status':'PASS bounded mathematical challenge; no maintained API or native Pell witness audit',
         'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pins':PINS,
         'forms':forms,'counts':dict(counts),'nop_boundary':{'x':x,'y':y,'T':T,'h':height,'eta':eta,'coefficient_parent_eta':eta-nf,'endpoint_parent_eta':eta-K*y-qh,'native_pell_witnesses_materialized':False}}

if __name__=='__main__':
 ap=argparse.ArgumentParser(); ap.add_argument('--root',type=Path,required=True); ap.add_argument('--probe-root',type=Path,default=Path('/tmp')); ap.add_argument('--output',type=Path); ap.add_argument('--expect',type=Path)
 a=ap.parse_args(); r=verify(a.root,a.probe_root); encoded=json.dumps(r,sort_keys=True,indent=2)+'\n'
 if a.expect: check(a.expect.read_text()==encoded,'saved exact receipt')
 if a.output: a.output.write_text(encoded)
 print(json.dumps({'status':r['status'],'counts':r['counts']}))
