#!/usr/bin/env python3
import hashlib,itertools,json,subprocess,sys
from collections import defaultdict
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-folded-root86-positive-reverse'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'check.py':'e2f7261422edff50aee22e8ce37fdbc2ac01efb7a0f4cfea8a13eaea731559d4','result.json':'cc56581d3ad533740148441f9f9ccd19d68973f8f5c8ad158907be9605f261d4'}.items():assert sha(p/n)==h
# Only the exact appended review link is stripped in memory, while both
# the final README and originally reviewed mathematical text stay pinned.
readme=(p/'README.md').read_bytes()
assert hashlib.sha256(readme).hexdigest()=='f49b64ee3c5f67fdffcbc9e94b67bcb17f12c65ad627664181e7281d7597a1f2'
tail=(b'\nIndependent external review is recorded in\n'
      b'`../../reviews/ordinary13-folded-root86-positive-reverse-independent/`.\n')
assert readme.endswith(tail)
assert hashlib.sha256(readme[:-len(tail)]).hexdigest()=='3e34f7c5f13ad664e951993e1b1e742f438c176867457d986559f85bfcca562a'
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
old=base/'research/ordinary13-four-square88-30/candidate.json';new=base/'research/ordinary13-folded-root86-probe/candidate.json';review=base/'reviews/ordinary13-folded-root86-probe-independent/check.py'
for q,h in [(old,'daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420'),(new,'e44c211efa0f124dc00414a475b2dca0d576117aaed7f4a371aa5a687be0a540'),(review,'b0896aa3f87844a7ecdee11ff2d2100f62a38982dc7094fb331762de3dc580bc')]:assert sha(q)==h
subprocess.run([sys.executable,'-I','-S','-B',str(review)],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
a=json.loads(old.read_text());b=json.loads(new.read_text());assert a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals'] and len(a['source'])==88 and len(b['source'])==86
expected=[]
for row in a['source']:
 if row[0] in ('folded_kBt','folded_g31'):continue
 expected.append(['g32','*','M','g31'] if row[0]=='g32' else row)
assert expected==b['source'] and [r[0] for r in a['source'] if 'r' in r[2:]]==['g31']
deps={'r'}
for n,op,x,y in a['source']:
 if x in deps or y in deps:deps.add(n)
assert 'Bt' not in deps and 'k' not in deps
rows={r[0]:r for r in b['source']}
for row in [['qm','*','J','beta'],['q','+',1,'qm'],['q2','*','q','q'],['q3','*','q','q2'],['M','*','q3','qm'],['k','+','eta','zeta'],['kY','*','Y','k'],['E','*','X','Y'],['ell','*','E','kY'],['g30','+','ell','k'],['g31','+','g30','r'],['g32','*','M','g31'],['g33','*','Y','qm'],['g34','+','g32','g33'],['folded_q3Bt','*','q3','Bt'],['Z','-','g34','folded_q3Bt'],['g38','*','Z','Z'],['g39','*','M','M'],['g40','*','ell','g30'],['g41','+',1,'g40'],['g42','*','g39','g41'],['A0','-','g38','g42'],['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['Fam2','*','Fam','Fam'],['Fsm2','*','g72','g72'],['out','+','sum01','sum23']]:assert rows[row[0]]==row
# Exact free-ring verification of the strictly positive difference in the
# contradiction, independently expanded from (ell+k)^2−1−ell(ell+k).
def atom(x):return {(x,):1}
def add(a,b,s=1):
 z=defaultdict(int,a)
 for k,v in b.items():z[k]+=s*v
 return {k:v for k,v in z.items() if v}
def mul(a,b):
 z=defaultdict(int)
 for x,u in a.items():
  for y,v in b.items():z[tuple(sorted(x+y))]+=u*v
 return {k:v for k,v in z.items() if v}
ell,k=atom('ell'),atom('k');one={():1};v=add(add(mul(add(ell,k),add(ell,k)),one,-1),mul(ell,add(ell,k)),-1);assert v==add(add(mul(ell,k),mul(k,k)),one,-1)
# Finite controls include negative arbitrary Bt and no assumptions on other ports.
count=0
for beta,J,X,Y,eta,zeta,rho,Bt in itertools.product(range(1,3),range(1,3),range(1,3),range(1,3),range(1,3),range(1,3),range(1,3),range(-2,1)):
 bm=J*beta;q=1+bm;q3=q**3;M=q3*bm;kk=eta+zeta;ell=X*Y*Y*kk;Z=M*(ell+kk+rho)+Y*bm-q3*Bt
 assert Z>M*(ell+kk)>0 and Z*Z>M*M*(1+ell*(ell+kk));count+=1
print(json.dumps({'status':'PASS_SCOPED_POSITIVE_TRANSFER','author_receipt_reproduced':True,'input_rows':[86,88],'independent_finite_controls':count,'scope':'Positive 86 zero -> positive 88 zero for beta>0; no converse, Lean or file binding.'},indent=2))
