#!/usr/bin/env python3
import gzip,hashlib,json,subprocess,sys
from collections import Counter,defaultdict
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-four-square88-30'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'candidate.json':'daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420','check.py':'3f8c1fafd86c6f7b3e9fa3892ecf89c1d9bcf6eda5d9768260391a611ac9a819','result.json':'9db99db45bfaeb6269e5520f42fb49e9b4233ee1c8c03f8ca1bca82210f4cb3c'}.items():assert sha(p/n)==h
# Only the exact post-review link/ray note is stripped in memory; the
# previously reviewed mathematical README bytes remain pinned unchanged.
readme=(p/'README.md').read_bytes()
assert hashlib.sha256(readme).hexdigest()=='6a506aab95a26b154ec97bae3a5a6cf229157cbb1f42315b38b477491094e299'
tail=(b'\nIndependent external review is recorded in\n'
      b'`../../reviews/ordinary13-four-square88-30-independent/`; it uses a distinct\n'
      b'weighted full-graph ray with degree 30 and leader 592789705 modulo 1,000,000,007.\n')
assert readme.endswith(tail)
assert hashlib.sha256(readme[:-len(tail)]).hexdigest()=='89b05e66a186a9423b06327488f1bb83d57e793379d726e48dbe9233f824c308'
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
parent=base/'research/ordinary13-ordinary-pair88-46/freej88.json';review=base/'reviews/ordinary13-ordinary-pair88-46-independent/check.py';p72=base/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';p115=base/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json'
for q,h in [(parent,'fc4627a15edc10f4cfcd3e6acf7df0896bb552a5f00cf238af6f1b5a349975bb'),(review,'8d4629946284f383d149fe00b631ced0f3ec957f9ca9bff1880d8090ca42e74b'),(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'),(p115,'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')]:assert sha(q)==h
subprocess.run([sys.executable,'-I','-S','-B',str(review)],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
old=json.loads(parent.read_text());g=json.loads((p/'candidate.json').read_text());rs=old['source'];assert rs[-7:]==[['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['pair','*','Fa','Fs'],['pairm','-','pair',1],['pair2','*','pairm','pairm'],['sum01','+','A0sq','A1sq'],['out','+','sum01','pair2']]
expected=[row for row in rs[:-7] if row[0]!='Fs']+[['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['Fam','-','Fa',1],['Fam2','*','Fam','Fam'],['Fsm2','*','g72','g72'],['sum01','+','A0sq','A1sq'],['sum23','+','Fam2','Fsm2'],['out','+','sum01','sum23']]
assert g['source']==expected and g['witnesses']==old['witnesses'] and g['fixed_numerals']==old['fixed_numerals'] and g['witnesses'][0]=='J' and len(g['witnesses'])==13 and len(g['fixed_numerals'])==4
assert len(expected)==88 and Counter(r[1] for r in expected)=={'*':48,'+':23,'-':17}
have=set(g['witnesses']+g['fixed_numerals']);deg={x:1 for x in g['witnesses']};deg.update({x:0 for x in g['fixed_numerals']})
for n,op,a,b in expected:
 assert n not in have and all(type(x)==int or x in have for x in (a,b));d=lambda x:0 if type(x)==int else deg[x];deg[n]=d(a)+d(b) if op=='*' else max(d(a),d(b));have.add(n)
need={g['output']}
for n,op,a,b in reversed(expected):
 if n in need:need.update((a,b))
assert all(n in need for n,_,_,_ in expected) and set(g['witnesses']+g['fixed_numerals'])<=need
assert [deg[n] for n in ('A0','A1','Fa','g72','out')]==[16,14,13,10,32]
assert [deg[n] for n in ('M','ell','k','r','Bt','Y','qm','q3')]==[4,4,1,1,2,1,1,3]
source={x[0]:x for x in expected}
for row in [['g30','+','ell','k'],['g31','+','g30','r'],['folded_kBt','*','k','Bt'],['folded_g31','-','g31','folded_kBt'],['g32','*','M','folded_g31'],['g33','*','Y','qm'],['g34','+','g32','g33'],['folded_q3Bt','*','q3','Bt'],['Z','-','g34','folded_q3Bt'],['g38','*','Z','Z'],['g39','*','M','M'],['g40','*','ell','g30'],['g41','+',1,'g40'],['g42','*','g39','g41'],['A0','-','g38','g42'],['g72','-','g71','Q']]:assert source[row[0]]==row
# Independently verify the A0 cancellation in a free integer polynomial ring.
def at(s):return {(s,):1}
def add(a,b,s=1):
 d=defaultdict(int,a)
 for k,v in b.items():d[k]+=s*v
 return {k:v for k,v in d.items() if v}
def mul(a,b):
 d=defaultdict(int)
 for x,u in a.items():
  for y,v in b.items():d[tuple(sorted(x+y))]+=u*v
 return {k:v for k,v in d.items() if v}
one={():1};M,ell,k,d=map(at,('M','ell','k','d'));z=add(mul(M,ell),d)
a=add(mul(z,z),mul(mul(M,M),add(one,mul(ell,add(ell,k)))),-1)
b=add(add(mul({():2},mul(mul(M,ell),d)),mul(d,d)),mul(mul(M,M),add(one,mul(ell,k))),-1);assert a==b
# deg d<=max(4+3,1+1,3+2)=7, deg M*ell<=8.
assert max(8+7,2*7,2*4+max(0,4+1))==15
# Confirm actual-port bytes against both pinned bindings.
B=json.loads((p72/'ACTIVE_BINDING.json').read_text());C=json.loads(p115.read_text());P=1000000007;assert all(P%d for d in range(2,int(P**.5)+1));fixed={};assert set(B['ports'])==set(C['ports'])==set(g['fixed_numerals'])
for n,m in B['ports'].items():
 assert C['ports'][n]['sha256_raw']==m['sha256_raw'] and C['ports'][n]['sha256_gzip']==m['sha256_gzip']
 z=(p72/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(z);assert hashlib.sha256(raw).hexdigest()==m['sha256_raw'] and len(raw)==m['raw_bytes'];value=int.from_bytes(raw,'little');assert value>0 and value.bit_length()==m['bits'];fixed[n]=value%P
# Independently evaluate the entire graph on weighted affine inputs.
def ap(a,b,s):
 z=[((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%P for i in range(max(len(a),len(b)))]
 while len(z)>1 and not z[-1]:z.pop()
 return z
def mp(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%P
 while len(z)>1 and not z[-1]:z.pop()
 return z
v={x:[i+2,i+1] for i,x in enumerate(g['witnesses'])};v.update({n:[x] for n,x in fixed.items()})
for n,op,a,b in expected:
 A=[a%P] if type(a)==int else v[a];B=[b%P] if type(b)==int else v[b];v[n]=mp(A,B) if op=='*' else ap(A,B,1 if op=='+' else -1)
assert len(v['out'])==31 and v['out'][-1]!=0
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','author_receipt_reproduced':True,'live_gates':88,'exact_degree':30,'weighted_affine_ray_leader_mod_prime':v['out'][-1],'prime':P,'scope':'External free-J graph and all-integer zero equivalence; no Lean, file binding, global frontier, or same-valuation P73 identification.'},indent=2))
