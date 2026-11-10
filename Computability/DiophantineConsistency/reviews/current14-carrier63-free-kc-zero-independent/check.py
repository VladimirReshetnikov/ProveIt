#!/usr/bin/env python3
import collections,gzip,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier63-free-kc-zero';p=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';old=json.loads(p.read_bytes());new=json.loads((pkg/'graph.json').read_bytes());rows=old['source'];assert [r for r in rows if r[0] in ('k','c')]==[['k','+','eta','zeta'],['c','+','kY','eta']] and [r[0] for r in rows if 'eta' in r[2:]]==['k','c'] and [r[0] for r in rows if 'zeta' in r[2:]]==['k']
assert new['source']==[r for r in rows if r[0] not in ('k','c')] and new['witnesses']==[{'eta':'c','zeta':'k'}.get(x,x) for x in old['witnesses']] and new['fixed_numerals']==old['fixed_numerals'] and new['output']==old['output'] and len(new['source'])==63 and collections.Counter(r[1] for r in new['source'])=={'*':37,'+':14,'-':12}
deps={n:(a,b) for n,_,a,b in new['source']};seen=set();stack=[new['output']]
while stack:
 x=stack.pop()
 if x in seen:continue
 seen.add(x)
 if x in deps:stack.extend(deps[x])
assert all(x in seen for x in list(deps)+new['witnesses']+new['fixed_numerals'])
ports={}
for name,m in old['coefficient_binding']['ports'].items():
 z=(p.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'];raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['raw_sha256'];ports[name]=int.from_bytes(raw,'big')
beta,K,lo,mf=(ports[n] for n in ('beta','K0','MC','MF'));B=beta.bit_length();q=beta+1;e=88042;C=17;assert B==94517 and beta==(1<<B)-1 and K>0 and 0<lo<beta<mf<2*beta
M=(K+pow(2,e,beta))%beta;F=(C*M)%beta;alpha=q-F-C;G=beta*(q-F)+alpha;R=G*(q*q-1)+lo+q*mf;N=(R-1)//2
assert F>0 and alpha>0 and q-F-alpha==C and R>3*B and R>=2*B and N>=2 and R>=8 and R%4==3 and (R-B)%B==e and (M*C-F)%beta==0 and R.bit_count()==283450 and N.bit_count()-1==283448<3*B and 3*B<R-1
# s=1 gives Y=q³; R>3B implies X>Y. With N>=2 and X>=144,
# (X/6)^N >= X²/36 >= 4X > 2(Y+1), hence c>(Y+1)k and recovered zeta<0.
# w>=q>F and C>0 ensure positive integral transport z. All Pell units are positive;
# first/main/strong/auxiliary and R mod 4 Chebyshev identities are independent of the ratio window.
for f in ('current14-carrier63-free-y-zero-independent','current14-carrier64-toy-full-zero-independent','current14-carrier64-pell-floor-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)==json.loads((pkg/'result.json').read_text()) and json.loads(r.stdout)['checker_sha256']==sha(pkg/'check.py')
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','B':B,'rank_bit_length':R.bit_length(),'rank_population':R.bit_count(),'scope':'distinct free-(k,c) 63-gate candidate symbolic positive zero at current payloads; no old same-q,R zero via floor; no maintained zero or existential nonequivalence'},indent=2))
