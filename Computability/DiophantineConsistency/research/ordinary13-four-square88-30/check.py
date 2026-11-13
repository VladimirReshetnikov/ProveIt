#!/usr/bin/env python3
"""Exact graph cut and compact-port degree check; no Lean."""
import gzip,hashlib,json,itertools
from collections import Counter
from pathlib import Path
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
parent=D/'research/ordinary13-ordinary-pair88-46/freej88.json';raw=parent.read_bytes();assert hashlib.sha256(raw).hexdigest()=='fc4627a15edc10f4cfcd3e6acf7df0896bb552a5f00cf238af6f1b5a349975bb'
g=json.loads(raw);rows=g['source'];assert rows[69:71]==[['g72','-','g71','Q'],['Fs','+',1,'g72']]
assert rows[-7:]==[['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['pair','*','Fa','Fs'],['pairm','-','pair',1],['pair2','*','pairm','pairm'],['sum01','+','A0sq','A1sq'],['out','+','sum01','pair2']]
new=[x for x in rows[:-7] if x[0]!='Fs']+[['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['Fam','-','Fa',1],['Fam2','*','Fam','Fam'],['Fsm2','*','g72','g72'],['sum01','+','A0sq','A1sq'],['sum23','+','Fam2','Fsm2'],['out','+','sum01','sum23']]
assert len(new)==88
candidate_raw=(H/'candidate.json').read_bytes(); assert hashlib.sha256(candidate_raw).hexdigest()=='daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420'
candidate=json.loads(candidate_raw);assert candidate['source']==new and candidate['witnesses']==g['witnesses'] and candidate['fixed_numerals']==g['fixed_numerals'] and candidate['operations']==88 and candidate['exact_degree']==30
ready=set(g['witnesses']+g['fixed_numerals']);degree={x:1 for x in g['witnesses']};degree.update({x:0 for x in g['fixed_numerals']})
for n,op,a,b in new:
 assert n not in ready and op in ('+','-','*') and all(isinstance(x,int) or x in ready for x in (a,b))
 da=0 if isinstance(a,int) else degree[a];db=0 if isinstance(b,int) else degree[b];degree[n]=da+db if op=='*' else max(da,db);ready.add(n)
needed={'out'}
for n,op,a,b in reversed(new):
 if n in needed:needed.update((a,b))
assert all(n in needed for n,_,_,_ in new) and all(x in needed for x in g['witnesses']+g['fixed_numerals'])
assert [degree[x] for x in ['A0','A1','Fa','g72','out']]==[16,14,13,10,32]
assert [degree[x] for x in ['M','ell','k','r','Bt','Y','qm','q3']]==[4,4,1,1,2,1,1,3]
expected=[['g30','+','ell','k'],['g31','+','g30','r'],['folded_kBt','*','k','Bt'],['folded_g31','-','g31','folded_kBt'],['g32','*','M','folded_g31'],['g33','*','Y','qm'],['g34','+','g32','g33'],['folded_q3Bt','*','q3','Bt'],['Z','-','g34','folded_q3Bt'],['g38','*','Z','Z'],['g39','*','M','M'],['g40','*','ell','g30'],['g41','+',1,'g40'],['g42','*','g39','g41'],['A0','-','g38','g42']]
source={r[0]:r for r in rows}
for row in expected: assert source[row[0]]==row
# Global unit exclusion for the two factored ordinary norms.
for a,f,I,V,y in itertools.product(range(4),repeat=5):
 delta=(a*a+4*a+3)%4;Q=(delta*(f*f-1))%4
 Fa=(y*y-Q*(y*y-V*V))%4;Fs=(1+I*I-Q)%4
 assert Fa!=3 and Fs!=3
# The new finalizer is precisely a sum of four residual squares over any ring.
# Check an exact sparse expansion with independent residual variables.
from collections import defaultdict
def poly(m):return {m:1}
def add(a,b):
 z=defaultdict(int,a)
 for m,c in b.items():z[m]+=c
 return {m:c for m,c in z.items() if c}
def mul(a,b):
 z=defaultdict(int)
 for m,c in a.items():
  for n,d in b.items():z[tuple(sorted(m+n))]+=c*d
 return {m:c for m,c in z.items() if c}
a0,a1,fa,fs=map(lambda x:poly((x,)),['A0','A1','Fam','Fsm'])
actual=add(add(mul(a0,a0),mul(a1,a1)),add(mul(fa,fa),mul(fs,fs)))
assert actual=={('A0','A0'):1,('A1','A1'):1,('Fam','Fam'):1,('Fsm','Fsm'):1}
def sub(a,b):return add(a,{m:-c for m,c in b.items()})
def prod(*parts):
 z={():1}
 for part in parts:z=mul(z,part)
 return z
M,ell,k,r0,Bt,Y,qm,q3=map(lambda x:poly((x,)),['M','ell','k','r','Bt','Y','qm','q3'])
rest=add(sub(add(k,r0),mul(k,Bt)),{})
delta=add(mul(M,rest),sub(mul(Y,qm),mul(q3,Bt)))
Z=add(mul(M,ell),delta)
A0=sub(mul(Z,Z),mul(mul(M,M),add({():1},mul(ell,add(ell,k)))))
alt=add(sub(add(prod({():2},M,ell,delta),mul(delta,delta)),mul(mul(M,M),add({():1},mul(ell,k)))),{})
assert A0==alt
# Authenticate the compact44 tuple and compute all-variables-equal modular ray.
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';bind=p72/'ACTIVE_BINDING.json';br=bind.read_bytes();assert hashlib.sha256(br).hexdigest()=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'
b=json.loads(br);p=1000000007;fixed={}
p115=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json'; braw=p115.read_bytes(); assert hashlib.sha256(braw).hexdigest()=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'
b115=json.loads(braw);assert set(b['ports'])==set(b115['ports'])==set(g['fixed_numerals'])
for n,m in b['ports'].items():assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip']
for n,m in b['ports'].items():
 z=(p72/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];x=gzip.decompress(z);assert len(x)==m['raw_bytes'] and hashlib.sha256(x).hexdigest()==m['sha256_raw'];fixed[n]=int.from_bytes(x,'little')%p
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def plus(a,b,s):return trim([((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%p for i in range(max(len(a),len(b)))])
def times(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%p
 return trim(z)
vals={x:[0,1] for x in g['witnesses']};vals.update({n:[x] for n,x in fixed.items()})
def value(x):return [x%p] if isinstance(x,int) else vals[x]
for n,op,a,b in new: vals[n]=times(value(a),value(b)) if op=='*' else plus(value(a),value(b),1 if op=='+' else -1)
assert len(vals['out'])-1==30 and vals['out'][-1]!=0
result={'parent_sha256':hashlib.sha256(raw).hexdigest(),'operations':len(new),'counts':dict(sorted(Counter(x[1] for x in new).items())),'all_gates_inputs_ports_live':True,'raw_syntactic_degree':32,'proved_degree_upper':30,'prime':p,'ray_degree':len(vals['out'])-1,'ray_leader':vals['out'][-1],'scope':'external source/ring and fixed-byte degree checks; mathematical zero equivalence separate; no Lean/PDF theorem'}
print(json.dumps(result,sort_keys=True,indent=2))
