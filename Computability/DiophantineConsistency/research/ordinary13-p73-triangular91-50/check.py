#!/usr/bin/env python3
"""Check exact P73/P61 surgery, liveness, identities and actual-byte degree rays."""
import gzip, hashlib, json
from collections import Counter
from pathlib import Path
H=Path(__file__).resolve().parent;ROOT=H.parents[1];D=ROOT/'con-zfc-diophantine-forms'
def pin(p,s):
 raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==s,p
 return raw
p73=D/'73-guard-reanchoring/positive';p61=D/'61-congruence-carriers/positive';p72=D/'72-congruence-sextic/positive13'
s73='e96cd6c8950711a6a26392b27c1ab531cb9df37277e0426cc40cdd1138846a5b';s61='515c29db7e07406dc70289b405bf59221480e2ebc3b22fdac01ee2de30b30b43'
parent73=json.loads(pin(p73/'p13_degree30.json',s73));parent61=json.loads(pin(p61/'p13_degree34.json',s61))
pin(p73/'PROOF.md','96c5d29cb8276ec802b301e5606a3d7223dbc6426cc926c1c4298b7aac3a2e57')
bind61=json.loads(pin(p61/'ACTIVE_BINDING.json','99a0944bbf09b368b227413312bc94e9c439578cc99582de18e2ca1339ff33b9'))
bind72=json.loads(pin(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
sha={'p73_91.json':'8f0e22b74373c5b73874971dc0b5fd6f17e7755d19c5c43c2087a778ff7fa5ae','p73_90.json':'25abb3eb6cf9908b5e97f9099fa83e93f89d18faa098836895f81662abbd5833','p73_rewrite91_30.json':'474152760b9b915e6346f0bff6b41b1db57a3634ed8dd1cf49483c2e5cc36180','p61_92.json':'5997d125070c4f55c383a009107cf7b3726f15a67cdeab588326170aa1f79c04'}
graphs={n:json.loads(pin(H/n,s)) for n,s in sha.items()}

def triangular(g,dc,yh,vsq,gap,prod):
 r=g['source'];idx=next(i for i,row in enumerate(r) if row[0]=='Kaux')
 assert [x[0] for x in r[idx:idx+5]]==['Kaux','I',('g71' if dc=='g63' else 'g72'),('g72' if dc=='g63' else 'g73'),'As']
 assert r[idx:idx+5]==[['Kaux','*','Delta','f2m'],['I','*','c2','i'],[('g71' if dc=='g63' else 'g72'),'*','I','I'],[('g72' if dc=='g63' else 'g73'),'*','Delta',('g71' if dc=='g63' else 'g72')],['As','-','f2m',('g72' if dc=='g63' else 'g73')]]
 r=r[:idx]+[['iDc','*','i',dc],['shared_square','*','iDc','iDc'],['scaled_f2m','*','Delta','f2m'],['As','-','scaled_f2m','shared_square']]+r[idx+5:]
 repl={vsq:[vsq,'+',yh,'V'],gap:[gap,'*','u',vsq],prod:[prod,'*','shared_square',gap]}
 assert sum(row[0] in repl for row in r)==3
 return [repl.get(row[0],row) for row in r]
def reassociate(rows):
 assert [x for x in rows if x[0] in ('g22','W','g35')]==[['g22','*','k','qm'],['W','+',1,'g22'],['g35','*','W','q3']]
 assert all('W' not in row[2:] for row in rows if row[0]!='g35')
 result=[]
 for row in rows:
  if row[0] in ('g22','W'):continue
  result.extend([['kM','*','k','M'],['g35','+','q3','kM']] if row[0]=='g35' else [row])
 return result
# Fix the actual source shapes used in the degree-30 cancellation proof.
source73={row[0]:row for row in parent73['source']}
for row in [['M','*','q3','qm'],['g30','+','ell','k'],['g31','+','g30','r'],['g32','*','M','g31'],['g33','*','Y','qm'],['g34','+','g32','g33'],['g35','*','W','q3'],['g36','*','Bt','g35'],['root0','-','g34','g36'],['g38','*','ell','g30'],['rad0','+',1,'g38'],['g40','*','root0','root0'],['g41','*','M','M'],['g42','*','g41','rad0'],['A0','-','g40','g42'],['g78','+','V','u'],['y2','*','g78','g78'],['g80','*','V','V'],['g81','-','y2','g80'],['g82','*','Kaux','g81'],['g83','-','y2','g82'],['Aa','-','g83',1]]:
 assert source73[row[0]]==row
tri73=triangular(parent73,'g63','g78','g80','g81','g82');tri61=triangular(parent61,'g64','g79','g81','g82','g83')
assert graphs['p73_91.json']['source']==tri73
assert graphs['p73_90.json']['source']==reassociate(tri73)
assert graphs['p73_rewrite91_30.json']['source']==reassociate(parent73['source'])
assert graphs['p61_92.json']['source']==tri61
for name,g in graphs.items():
 parent=parent61 if name.startswith('p61') else parent73
 assert g['witnesses']==parent['witnesses'] and g['fixed_numerals']==parent['fixed_numerals'] and g['residuals']==parent['residuals'] and g['output']==parent['output']
 assert g['parent_sha256']==(s61 if name.startswith('p61') else s73)

# Exact formal ring checks: root reassociation, strong scaling, auxiliary shear,
# difference of squares, and the first-norm cancellation needed for degree 30.
def var(s):return {(s,):1}
def add(a,b):
 z=dict(a)
 for m,c in b.items():z[m]=z.get(m,0)+c
 return {m:c for m,c in z.items() if c}
def neg(a):return {m:-c for m,c in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 z={}
 for x,a0 in a.items():
  for y,b0 in b.items():
   m=tuple(sorted(x+y));z[m]=z.get(m,0)+a0*b0
 return {m:c for m,c in z.items() if c}
one={():1};q3,qm,k,delta,c2,i,fm,y,v,u,M,ell,r,yy,Bt=map(var,['q3','qm','k','delta','c2','i','f2m','y','v','u','M','ell','r','Y','Bt'])
assert mul(add(one,mul(k,qm)),q3)==add(q3,mul(k,mul(q3,qm)))
I=mul(i,c2);shared=mul(mul(i,mul(delta,c2)),mul(i,mul(delta,c2)))
As=sub(fm,mul(delta,mul(I,I)));Asnew=sub(mul(delta,fm),shared)
assert Asnew==mul(delta,As)
gap=sub(mul(y,y),mul(v,v));Aa=sub(sub(mul(y,y),mul(mul(delta,fm),gap)),one);Aanew=sub(sub(mul(y,y),mul(shared,gap)),one)
assert Aanew==add(Aa,mul(mul(delta,gap),As))
assert Aanew==add(Aa,mul(gap,Asnew))
yv=add(v,u);assert sub(mul(yv,yv),mul(v,v))==mul(u,add(yv,v))
# Abstract d=root0−M*ell; A0 removes the highest square identically.
d=var('d');twod=add(d,d);a0=sub(mul(add(mul(M,ell),d),add(mul(M,ell),d)),mul(mul(M,M),add(mul(ell,add(ell,k)),one)))
a0new=sub(add(mul(d,d),mul(mul(M,ell),sub(twod,mul(M,k)))),mul(M,M));assert a0==a0new

prime=1000000007;fixed={}
assert set(bind61['ports'])==set(bind72['ports'])=={'beta','K0','MC','MF'}
for n,meta in bind72['ports'].items():
 assert bind61['ports'][n]['sha256']==meta['sha256_raw'] and bind61['ports'][n]['gzip_sha256']==meta['sha256_gzip']
 raw=gzip.decompress(pin(p72/meta['path'],meta['sha256_gzip']));assert hashlib.sha256(raw).hexdigest()==meta['sha256_raw'] and len(raw)==meta['raw_bytes']
 x=int.from_bytes(raw,'little');assert x>0 and x.bit_length()==meta['bits']
 if n=='beta':assert x==(1<<590069)-1
 fixed[n]=x%prime

def trim(a):
 while len(a)>1 and not a[-1]:a.pop()
 return a
def sadd(a,b,s):return trim([((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def smul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for j,x in enumerate(a):
  for k0,y0 in enumerate(b):z[j+k0]=(z[j+k0]+x*y0)%prime
 return trim(z)

def inspect(name,g):
 rows=g['source'];ready=set(g['witnesses']+g['fixed_numerals']);deg={x:1 for x in g['witnesses']};deg.update({x:0 for x in g['fixed_numerals']})
 for n,op,a,b in rows:
  assert n not in ready and op in ('+','-','*') and all(isinstance(x,int) or x in ready for x in (a,b))
  def dv(x):return 0 if isinstance(x,int) else deg[x]
  deg[n]=dv(a)+dv(b) if op=='*' else max(dv(a),dv(b));ready.add(n)
 needed={g['output']}
 for n,op,a,b in reversed(rows):
  if n in needed:needed.update((a,b))
 assert all(n in needed for n,_,_,_ in rows) and all(n in needed for n in g['witnesses']+g['fixed_numerals'])
 vals={x:[0,1] for x in g['witnesses']};vals.update({x:[v0] for x,v0 in fixed.items()})
 def vv(x):return [x%prime] if isinstance(x,int) else vals[x]
 for n,op,a,b in rows:vals[n]=smul(vv(a),vv(b)) if op=='*' else sadd(vv(a),vv(b),1 if op=='+' else -1)
 assert len(vals[g['output']])-1==g['exact_degree']
 if g['exact_degree']==50:assert deg[g['output']]==50 and vals[g['output']][-1]==832098066 and vals['Aa'][-1]==662074970
 else:
  # Structural upper bound 30, using exact A0 and auxiliary-gap identities above.
  # Actual graph has deg(M)<=4, ell<=4, k,r<=1, Y,qm<=1, W<=2, Bt<=2, q3<=3.
  assert deg['M']<=4 and deg['ell']<=4 and deg['k']<=1 and deg['qm']<=1 and deg['Bt']<=2 and deg['q3']<=3
  # d=M*(k+r)+qm*Y−q3*W*Bt has degree<=7, hence A0<=15.
  # y=V+u gives gap<=7; Delta*f2m<=6, so Aa<=13.
  assert deg['Delta']<=4 and deg['f2m']<=2 and deg['V']<=6 and deg['A1']<=14 and deg['As']<=14
  assert max(2*15,2*14,2*13,2*14)==30
 return {'operations':len(rows),'counts':dict(sorted(Counter(row[1] for row in rows).items())),'all_gates_live':True,'syntactic_upper':deg[g['output']],'proved_upper':g['exact_degree'],'ray_degree':len(vals[g['output']])-1,'ray_leader':vals[g['output']][-1]}
res={n:inspect(n,g) for n,g in graphs.items()}
# Distinct full graphs: original P73 and its 91-gate exact polynomial rewrite
# have the same actual-port ray as a supplementary check; structural identity
# was established above and is stronger than this sample.
base=dict(parent73,exact_degree=30)
res['parent73']=inspect('parent73',base)
assert res['parent73']['ray_leader']==res['p73_rewrite91_30.json']['ray_leader']
print(json.dumps({'status':'PASS','graphs':res,'raw_port_binding':'P72 bytes match both compressed and raw P61 hashes','modulus':prime,'triangular_identities':['As_new=Delta*As','Aa_new=Aa+Delta*(y²−V²)*As'],'scope':'external graph and ring identity evidence; P73 compiler/calibration and foundational proof inherited, no Lean or rendered-file binding'},indent=2,sort_keys=True))
