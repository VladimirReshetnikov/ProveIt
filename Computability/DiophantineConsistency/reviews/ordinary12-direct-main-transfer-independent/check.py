#!/usr/bin/env python3
"""Independently verify conditional semiring identities and author evidence."""
from hashlib import sha256
import json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-direct-main-probe';O=P/'observations/transfer-attempt01';Q=P/'observations/attempt01/terminal.json';B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
PIN={P/'TRANSFER.md':'5f5816b95286b8d4a89c0ba2985300b3c830bc1b8055fa16fa3ed7d54bb8e323',
 P/'DirectMainTransfer.lean':'2308aa52cbb8e05c412f96f511805cb9f759ef9dcefb2665b6c061544d29e055',
 P/'run-transfer.py':'917ac0a51b4de76df14df818f561fac1ad6690df6faf7458598ece3f88f06fcc',
 O/'terminal.json':'10731de7542de3e018dd14dfb295d74496320c59f9bc4b47b54184696ca5c04c',
 O/'source.txt':'2308aa52cbb8e05c412f96f511805cb9f759ef9dcefb2665b6c061544d29e055',
 O/'stdout':'08fca54760cdeec6e9168590aba18d71c4592772acff438cdf07866b3360cf39',
 Q:'2bf0934017209ddb4fab587740a9e680e80ce0f878f490856f5928e9fb66c81e',
 B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def need(v,m):
 if not v:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
for p,h in PIN.items():need(sha(p)==h,'input mismatch '+str(p))
s=(P/'DirectMainTransfer.lean').read_text();r=json.loads((O/'terminal.json').read_text());proj=json.loads(Q.read_text());base=json.loads(B.read_text())
need(s.splitlines()[0]=='import DirectMainProjection','direct import mismatch')
for frag in ('theorem transfer {V : Type*} [CommSemiring V] (U X a c H G R k main w : V)',
 '(hroot : U*(X+a*c)+H*(U*G+R+1)=H*k+U*main)',
 'H*(U*w+R+1)+U*(X+a*c+H*G)=H*k+U*(main+H*w)',
 'theorem old_contribution {V : Type*} [CommSemiring V] (q s w : V)',
 '((q*w)*(q^3*s))*q=(q^5*s)*w'):
 need(frag in s,'theorem statement mismatch '+frag)
# Verify the transfer as two positive-coefficient polynomial identities over
# independent variables. This works without subtracting or canceling in V.
nvars=10;z=(0,)*nvars
def c(n):return {} if n==0 else {z:n}
def var(i):
 m=list(z);m[i]=1;return {tuple(m):1}
def add(a,b):
 out=dict(a)
 for m,v in b.items():out[m]=out.get(m,0)+v
 return {m:v for m,v in out.items() if v}
def mul(a,b):
 out={}
 for x,a0 in a.items():
  for y,b0 in b.items():
   m=tuple(i+j for i,j in zip(x,y));out[m]=out.get(m,0)+a0*b0
 return {m:v for m,v in out.items() if v}
U,X,a,C,H,G,R,k,main,w=(var(i) for i in range(nvars));one=c(1)
premise_l=add(mul(U,add(X,mul(a,C))),mul(H,add(add(mul(U,G),R),one)))
premise_r=add(mul(H,k),mul(U,main));extra=mul(U,mul(H,w))
concl_l=add(mul(H,add(add(mul(U,w),R),one)),mul(U,add(add(X,mul(a,C)),mul(H,G))))
concl_r=add(mul(H,k),mul(U,add(main,mul(H,w))))
need(concl_l==add(premise_l,extra) and concl_r==add(premise_r,extra),'semiring transfer identity')
q,s0,w=(var(i) for i in range(3))
def pow_nat(x,k):
 result=one
 for _ in range(k):result=mul(result,x)
 return result
need(mul(mul(mul(q,w),mul(pow_nat(q,3),s0)),q)==mul(mul(pow_nat(q,5),s0),w),'q-power identity')
need(r['exit']==0 and r['reason'] is None and r['union_unchanged'] and r['union_count']==1291,'author run failed')
need(r['source_sha256']==r['source_after']==sha(P/'DirectMainTransfer.lean')==sha(O/'source.txt'),'source mismatch')
need(r['runner_sha256']==r['runner_after']==sha(P/'run-transfer.py'),'runner mismatch')
lean=Path(r['command'][0]);need(r['lean_sha256']==r['lean_after']==sha(lean),'Lean binary mismatch')
need(r['base_receipt_sha256']==sha(B) and base['exit']==0 and base['union_unchanged'],'base receipt mismatch')
expected="'DirectMainTransfer.transfer' depends on axioms: [propext]\n'DirectMainTransfer.old_contribution' depends on axioms: [propext]\n"
need((O/'stdout').read_text()==expected and not (O/'stderr').read_bytes() and sha(O/'stdout')==r['stdout_sha256'] and sha(O/'stderr')==r['stderr_sha256'],'log mismatch')
out=Path(r['command'][r['command'].index('-o')+1]);compiled=Path(r['command'][r['command'].index('-o')-1])
need(sha(out)==r['object_sha256']=='f6c24060e4a91ad3710bab840133e4c70987c55f3e95246a5d4452de48852f78' and sha(compiled)==sha(P/'DirectMainTransfer.lean'),'compiled output mismatch')
paths=r['lean_path'].split(':');prior=Path(proj['output_root'])/'DirectMainProjection.olean'
need(Path(paths[0])==prior.parent and sha(prior)==r['projection_producer_sha256']==proj['object_sha256'],'projection import mismatch')
need(proj['exit']==0 and proj['reason'] is None and proj['union_unchanged'],'projection producer receipt failed')
need(len(r['preflight']['lean'])==1 and len(r['samples'])==2 and all(len(x['lean'])==2 for x in r['samples']) and min(x['mem_available_kib'] for x in r['samples'])==18196964,'overlap sample mismatch')
lib=Path(paths[1])
def verify_union():
 actual={p.relative_to(lib).as_posix():p for p in lib.rglob('*') if p.is_file()};need(set(actual)==set(base['union']) and len(actual)==1291,'selected union membership')
 for rel,p in actual.items():
  v=base['union'][rel];need(p.is_symlink() and os.readlink(p)==v['link'] and str(p.resolve())==v['resolved'] and sha(p)==v['sha256'],'selected object drift '+rel)
verify_union()
prev=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ordinary12-direct-main-independent/check.py')],capture_output=True,check=True)
need(not prev.stderr and json.loads(prev.stdout)['status']=='PASS','previous projection/norm review failed')
verify_union()
for p,h in PIN.items():need(sha(p)==h,'input changed during review '+str(p))
need(sha(out)==r['object_sha256'] and sha(prior)==r['projection_producer_sha256'],'proof object changed')
print(json.dumps({'status':'PASS','transfer_semiring_identities':2,'power_semiring_identity':True,
 'author_exit':r['exit'],'projection_import_matches':True,'selected_union_objects':1291,
 'preexisting_lean_processes':1,'sampled_lean_processes':2,
 'scope':'conditional algebra only; no graph equivalence or iPRA theorem'},indent=2))
