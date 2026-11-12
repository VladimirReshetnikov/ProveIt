#!/usr/bin/env python3
from pathlib import Path
from math import factorial
import gzip,hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-root74-natural-cancel86';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'a6d82afee8cff6fc884506721dacbb0f3d77f6c5122d5f07c8f22d5852480b05',A/'candidate.json':'0211a1bcac635af617090facdc3b7f98d18ad94579027df840532d87ae5a5170',A/'check.py':'a2d45e7346c9d41e157318b67cf19a412e5a4f35b4a031c1a7073d5c8058ab05',A/'result.json':'f19c4f42c52605ccebef713e7fbe3705ab2145c8136a783e90a884158bc47eda',D/'research/ordinary14-root74-natural-shift88/candidate.json':'85675d2db0c6a40e0f759b9b67351cc74d8bc374ea7f85f85ea754eae8f9276d',D/'reviews/ordinary14-root74-natural-shift88-independent/check.py':'30acd6354bfd6c79c4edc7c54c939112397c16b372e3a747dc37279639a0b2ad',D/'reviews/ordinary14-root74-natural-shift88-independent/observation.json':'3b0210feab7eeb4a8f015d0ec3d0162092717a91ebdba2a870e41b64940631e1'}
tail=b"\nIndependent external review: [natural cancellation 86](../../reviews/ordinary14-root74-natural-cancel86-independent/README.md).\n"
for p,h in pins.items():
 if p==A/'README.md':
  data=p.read_bytes();assert hashlib.sha256(data).hexdigest()=='e54b8918f86cf83431445e33fb5056bf8496f8079fc6a8d5c0ec48bb1ad55064'
  assert data.endswith(tail) and hashlib.sha256(data[:-len(tail)]).hexdigest()==h
 else:assert H(p)==h,(str(p),H(p),h)
a=json.loads((D/'research/ordinary14-root74-natural-shift88/candidate.json').read_bytes());b=json.loads((A/'candidate.json').read_bytes());assert a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals'];assert a['domain']==b['domain']=='nonnegative integers' and len(a['source'])==88 and len(b['source'])==86
old={r[0]:r[1:] for r in a['source']};new={r[0]:r[1:] for r in b['source']};assert len(old)==88 and len(new)==86
assert set(old)-set(new)=={'F','h'} and not (set(new)-set(old));assert {n for n in new if old[n]!=new[n]}=={'qF','guard_base','bt_quotient'}
assert {n:old[n] for n in ('q','F','h','qF','guard_base','bt_quotient','guard')}=={'q':['+',1,'qm'],'F':['+','n_F',1],'h':['+','n_h',1],'qF':['-','q','F'],'guard_base':['+','g27','qF'],'bt_quotient':['*','qm','h'],'guard':['-','guard_base','bt_quotient']}
assert {n:new[n] for n in ('qF','guard_base','bt_quotient','guard')}=={'qF':['-','qm','n_F'],'guard_base':['-','g27','n_F'],'bt_quotient':['*','qm','n_h'],'guard':['-','guard_base','bt_quotient']}
uses=lambda name:[r[0] for r in a['source'] if name in r[2:]]
assert uses('F')==['qF'] and uses('h')==['bt_quotient'] and uses('guard_base')==['guard'] and uses('bt_quotient')==['guard']
# Independent exact sparse polynomial check of the two cut identities.
zero=(0,0,0,0)
def var(i):return {tuple(int(i==j) for j in range(4)):1}
def add(x,y,sgn=1):
 out=x.copy()
 for k,v in y.items():out[k]=out.get(k,0)+sgn*v
 return {k:v for k,v in out.items() if v}
def mul(x,y):
 out={}
 for a,v in x.items():
  for b,w in y.items():
   k=tuple(i+j for i,j in zip(a,b));out[k]=out.get(k,0)+v*w
 return {k:v for k,v in out.items() if v}
beta,F,h,G=[var(i) for i in range(4)];one={zero:1}
oldqf=add(add(one,beta),add(F,one),-1);newqf=add(beta,F,-1);assert oldqf==newqf
oldguard=add(add(G,oldqf),mul(beta,add(h,one)),-1);newguard=add(add(G,F,-1),mul(beta,h),-1);assert oldguard==newguard
# Induction through unchanged rows after the two established cuts; the two
# differing intermediate guard nodes have no users other than guard itself.
agreed=set(a['witnesses']+a['fixed_numerals']);checked=[]
for n,op,x,y in a['source']:
 if n in ('F','h','guard_base','bt_quotient'):continue
 if n=='qF':assert {'qm','n_F'}<=agreed
 elif n=='guard':assert {'g27','qm','n_F','n_h','qF'}<=agreed
 else:
  assert old[n]==new[n] and all(type(z) is int or z in agreed for z in (x,y)),n
 agreed.add(n);checked.append(n)
assert 'out' in agreed and len(checked)==84
known=set(b['witnesses']+b['fixed_numerals']);assert len(known)==18
for n,op,x,y in b['source']:
 assert n not in known and op in ('+','-','*') and all(type(z) is int or z in known for z in (x,y));known.add(n)
live={'out'}
for n,op,x,y in reversed(b['source']):
 if n in live:live.update(z for z in (x,y) if isinstance(z,str))
assert all(n in live for n,_,_,_ in b['source']) and set(b['witnesses']+b['fixed_numerals'])<=live
# The independently reviewed 88 upper bound is replayed; exact ring identity
# above transfers its degree bound to this candidate.
prior=D/'reviews/ordinary14-root74-natural-shift88-independent';r=subprocess.run([sys.executable,'-I','-S','-B',str(prior/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(prior/'observation.json').read_bytes();assert json.loads(r.stdout)['upper_degree']==107
# Reauthenticate P72/P115 bytes and recover the diagonal leading coefficient
# by 108 evaluations and the 107th finite difference, not polynomial lists.
base=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';p=base/'ACTIVE_BINDING.json';q=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json';assert H(p)=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf' and H(q)=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01';binding=json.loads(p.read_bytes());other=json.loads(q.read_bytes());prime=1000000007;fixed={}
for name,meta in binding['ports'].items():
 assert meta['sha256_raw']==other['ports'][name]['sha256_raw'] and meta['sha256_gzip']==other['ports'][name]['sha256_gzip']
 data=(base/meta['path']).read_bytes();assert hashlib.sha256(data).hexdigest()==meta['sha256_gzip'];raw=gzip.decompress(data);assert len(raw)==meta['raw_bytes'] and hashlib.sha256(raw).hexdigest()==meta['sha256_raw'];fixed[name]=int.from_bytes(raw,'little')%prime
assert set(fixed)==set(b['fixed_numerals'])
def calc(t):
 env={n:t for n in b['witnesses']};env.update(fixed)
 for n,op,x,y in b['source']:
  x=x if type(x) is int else env[x];y=y if type(y) is int else env[y];env[n]=({'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]())%prime
 return env['out']
vals=[calc(t) for t in range(108)]
for _ in range(107):vals=[(vals[i+1]-vals[i])%prime for i in range(len(vals)-1)]
lead=vals[0]*pow(factorial(107),-1,prime)%prime;assert lead==419359493
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(A/'result.json').read_bytes()
print(json.dumps({'scope':'external exact-DAG graph review at authenticated specialized bytes; no Lean, PDF binding or minimality','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'operations':86,'inputs':14,'inductively_checked_nodes':len(checked),'degree_upper_from_reviewed_88':107,'finite_difference_order':107,'prime':prime,'leading_coefficient':lead,'author_receipt_replayed':True},sort_keys=True,indent=2))
