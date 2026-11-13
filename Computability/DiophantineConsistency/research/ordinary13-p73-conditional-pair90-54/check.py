#!/usr/bin/env python3
"""Check exact graph transfer, mod-4 controls, authenticated ports and degree."""
import gzip,hashlib,itertools,json
from collections import Counter
from pathlib import Path
H=Path(__file__).resolve().parent;ROOT=H.parents[1];p72=ROOT/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';p61=ROOT/'con-zfc-diophantine-forms/61-congruence-carriers/positive'
def pin(p,d):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==d,p
 return b
sphere_sha='3760eb7f48966ff5e550c28a28bb78d23166888679d91ee3b9928f8d79f52242';new_sha='3946b8c328d692e829d1f556ffcf78cc559e885f3715ee3509f241f4e75c47c0'
old=json.loads(pin(ROOT/'research/ordinary13-p73-conditional-sphere91/polynomial.json',sphere_sha))
review=json.loads(pin(ROOT/'reviews/ordinary13-p73-conditional-sphere91-independent/result.json','f2ffa082b6fe2919e147677041d06e0c0760474eac3e0b7704dafcc4376670b2'))
assert review['status']=='PASS_SCOPED_INDEPENDENT_REVIEW' and review['live_gates']==91 and review['exact_degree']==30
pin(ROOT/'reviews/ordinary13-p73-conditional-sphere91-independent/check.py','227fa4add87e478f7b3476c838f3d0cfffcbb8dfe428548a874a90d01170799c')
g=json.loads(pin(H/'polynomial.json',new_sha));assert g['parent_sha256']==sphere_sha
binding=json.loads(pin(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
bind61=json.loads(pin(p61/'ACTIVE_BINDING.json','99a0944bbf09b368b227413312bc94e9c439578cc99582de18e2ca1339ff33b9'))
rows=[]
for row in old['source']:
 n=row[0]
 if n in ('g90','g91','output'):continue
 if n=='As':rows.append(['Fs','-','f2','g72'])
 elif n=='g80':rows.append(['g80','+','g78','V'])
 elif n=='g81':rows.append(['g81','*','u','g80'])
 elif n=='g88':rows.extend([['pair_product','*','g83','Fs'],['pair_residual','-','pair_product',1],['g88','*','pair_residual','pair_residual']])
 else:rows.append(row)
assert rows==g['source'] and len(rows)==g['operations']==90 and g['output']=='g89'
assert g['witnesses']==old['witnesses'] and len(g['witnesses'])==13 and g['fixed_numerals']==old['fixed_numerals']
assert {x[0]:x for x in old['source']}['As']==['As','-','f2m','g72']
ready=set(g['witnesses']+g['fixed_numerals']);deg={x:1 for x in g['witnesses']};deg.update({x:0 for x in g['fixed_numerals']})
for n,op,a,b in rows:
 assert n not in ready and op in ('+','-','*') and all(isinstance(x,int) or x in ready for x in (a,b))
 def dv(x):return 0 if isinstance(x,int) else deg[x]
 deg[n]=dv(a)+dv(b) if op=='*' else max(dv(a),dv(b));ready.add(n)
needed={g['output']}
for n,op,a,b in reversed(rows):
 if n in needed:needed.update((a,b))
assert all(n in needed for n,_,_,_ in rows) and all(n in needed for n in g['witnesses']+g['fixed_numerals'])
assert {k:deg[k] for k in ['g81','g83','Fs','pair_residual','g89']}=={'g81':7,'g83':13,'Fs':14,'pair_residual':27,'g89':54}
# Exact sparse integer-ring checks of gap and Fs identities.
def var(x):return {(x,):1}
def add(a,b):
 z=dict(a)
 for m,c in b.items():z[m]=z.get(m,0)+c
 return {m:c for m,c in z.items() if c}
def neg(a):return {m:-c for m,c in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 z={}
 for m,x in a.items():
  for n,y in b.items():
   t=tuple(sorted(m+n));z[t]=z.get(t,0)+x*y
 return {m:c for m,c in z.items() if c}
one={():1};f2,g72,V,u=map(var,['f2','g72','V','u']);As=sub(sub(f2,one),g72);Fs=sub(f2,g72);assert Fs==add(one,As)
y=add(V,u);assert sub(mul(y,y),mul(V,V))==mul(u,add(y,V))
# Modulo-4 checks are finite controls; the proof is in README.
for a,f,I,V0,y0 in itertools.product(range(4),repeat=5):
 delta=(a*a+4*a+3)%4;Q=delta*(f*f-1)%4
 assert Q in (0,1)
 Fa=(y0*y0-Q*(y0*y0-V0*V0))%4
 Fsv=(f*f-delta*I*I)%4
 assert Fa in (0,1) and Fsv in (0,1,2)
prime=1000000007;ports={}
assert set(binding['ports'])==set(bind61['ports'])=={'beta','K0','MC','MF'}
for n,m in binding['ports'].items():
 assert bind61['ports'][n]['sha256']==m['sha256_raw'] and bind61['ports'][n]['gzip_sha256']==m['sha256_gzip']
 raw=gzip.decompress(pin(p72/m['path'],m['sha256_gzip']));assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw']
 value=int.from_bytes(raw,'little');assert value>0 and value.bit_length()==m['bits']
 if n=='beta':assert value==(1<<590069)-1
 ports[n]=value%prime
def trim(v):
 while len(v)>1 and v[-1]==0:v.pop()
 return v
def sadd(a,b,sign):return trim([((a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def smul(a,b):
 out=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%prime
 return trim(out)
vals={x:[0,1] for x in g['witnesses']};vals.update({k:[v] for k,v in ports.items()})
def v(x):return [x%prime] if isinstance(x,int) else vals[x]
for n,op,a,b in rows:vals[n]=smul(v(a),v(b)) if op=='*' else sadd(v(a),v(b),1 if op=='+' else -1)
assert len(vals['g83'])-1==13 and vals['g83'][-1]==666379690
assert len(vals['Fs'])-1==14 and vals['Fs'][-1]==999999991
assert len(vals[g['output']])-1==54 and vals[g['output']][-1]==832098066
print(json.dumps({'status':'PASS','graph_sha256':new_sha,'parent_sphere_sha256':sphere_sha,'operations':len(rows),'operation_counts':dict(sorted(Counter(x[1] for x in rows).items())),'live_gates':len(rows),'witnesses':len(g['witnesses']),'formal_identities':['Fs=1+As','y²−V²=u*(y+V)'],'degree_upper':54,'ray_modulus':prime,'ray_degree':len(vals[g['output']])-1,'ray_leading_coefficient':vals[g['output']][-1],'scope':'external graph, exact ring identities, finite residue control and degree; no Lean or rendered file binding'},indent=2,sort_keys=True))
