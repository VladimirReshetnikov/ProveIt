#!/usr/bin/env python3
"""Current-port one-row C-fold, exact root identity and degree controls; no Lean."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json,random
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
PINS={
'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean':'0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794',
'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean':'636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390',
'Lean/DiophantineConsistency/Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',
'Lean/DiophantineConsistency/Compact44/FreeJMainOrientation.lean':'d02beb02122e682deef3e89c3dcb8e3e6aea31ddfbc4f320fe6af9a3df7f9a6b',
'Lean/DiophantineConsistency/Compact44/FreeJEarlyIndex.lean':'ab9b8e34903eff1e33e81b6a75438797eef1f2dab84595e23516b44de774ea3d',
'Lean/DiophantineConsistency/Compact44/FreeJPowerFinish.lean':'e4b2e84586b6232b9accc7775f094d4e1047453f1e8337f6241d39a6657d8816',
'research/adaptive87-four-square-current88-30/graph.json':'293dac5175d4924812177a1e73a316bf5cc16bf1b5cef636388d9e110eebb7ed',
'research/adaptive87-current-cfold88-degree28/graph.json':'26b5bc4c14320b0fe2891f3aeca0e216f26e555ee1206cefd71d7fcc7b674b36',
'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json':'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e',
'research/adaptive-direct-ordinate86/DEGREE-87-PARENT.md':'55661bba60da190c5b0a2bfe746daca2d7fbb7fe9253bdb11cfed8dd374eb55f',
'research/ordinary13-cfold88-28/README.md':'3deb526c584e0c0fa532bffcc98a651c50454871848e67529fccb55fe6de4842',
'research/ordinary14-shifted-guard87-calibration/README.md':'005fd2c04cef4c997383bf373cc48acd326e829eb01ff4d30c218dadaf9f758a',
'reviews/ordinary14-shifted-guard87-calibration-math-independent/README.md':'9e4d3f69e78a4b31569fec7fff01764a998f06292ee01e8623976f4ad72f5aa2',
'reviews/ordinary13-cfold88-28-independent/README.md':'dfcce545fa9c4818e1c76b3c01dd361889981635fdee8fec190fab8cc8cd9aa6',
'research/ordinary13-folded-root86-negated-positive-bt/README.md':'c7eb54d7750c1b8db428d48408e61e1868c5feaf0584b6e31054f5acf4df0bff',
'research/ordinary13-folded-root86-negated-forward/README.md':'c4bd9700bcbedbff97f6777a7ac714cc50a3b1febe021498afa2fb87600be6ef'}
for n,h in PINS.items():assert hashlib.sha256((ROOT/n).read_bytes()).hexdigest()==h,n
for name,pattern in [
 ('Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean','theorem scalar_rank_window (q beta MC MF J F alpha : V)'),
 ('Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean','theorem power_bound (X Y r k c eta zeta : V)'),
 ('Lean/DiophantineConsistency/Compact44/P72Exact.lean',"theorem indices_ordinary (q X Y k R g c a y0 i' f T u n s μ m η : V)"),
 ('Lean/DiophantineConsistency/Compact44/FreeJMainOrientation.lean','theorem rank_congruence_from_main (p : Fin 4 → ℕ)'),
 ('Lean/DiophantineConsistency/Compact44/FreeJEarlyIndex.lean','theorem early_index_of_facts (p : Fin 4 → ℕ)')]:
 assert pattern in (ROOT/name).read_text(),name
old=json.loads((ROOT/'research/adaptive87-four-square-current88-30/graph.json').read_bytes());g=json.loads((HERE/'graph.json').read_bytes())
assert g['source_parent_sha256']==PINS['research/adaptive87-four-square-current88-30/graph.json']
assert g['witnesses']==old['witnesses'] and g['fixed_numerals']==old['fixed_numerals'] and g['output']==old['output']
assert g['source']==[['root_skew','*','k','C'] if r[0]=='root_skew' else r for r in old['source']]
assert ['root_skew','*','k','Bt'] in old['source']
known=set(g['witnesses']+g['fixed_numerals']);rows={}
for n,op,a,b in g['source']:
 assert n not in known and op in ('+','-','*') and all(not isinstance(v,str) or v in known for v in (a,b));known.add(n);rows[n]=(op,a,b)
needed={g['output']}
for n,_,a,b in reversed(g['source']):
 if n in needed:needed.update(z for z in (a,b) if isinstance(z,str))
assert set(rows)<=needed and set(g['witnesses']+g['fixed_numerals'])<=needed and len(rows)==88
# Exact sparse free-commutative-ring check of the coordinate substitution,
# treating M, ell, k, rho, Bt, C, Y, b and q3 as independent indeterminates.
N=9
def atom(i):return {tuple(int(j==i) for j in range(N)):1}
def add(a,b,sgn=1):
 c=a.copy()
 for m,v in b.items():c[m]=c.get(m,0)+sgn*v
 return {m:v for m,v in c.items() if v}
def mul(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():
   z=tuple(x+y for x,y in zip(m,n));c[z]=c.get(z,0)+v*w
 return {m:v for m,v in c.items() if v}
M,ell,k,rho,Bt,C,Y,b,q3=map(atom,range(N))
r_old=add(rho,mul(k,add(Bt,C,-1)))
old_inner=add(add(add(ell,k),r_old),mul(k,Bt),-1)
new_inner=add(add(add(ell,k),rho),mul(k,C),-1)
oldZ=add(add(mul(M,old_inner),mul(Y,b)),mul(q3,Bt),-1)
newZ=add(add(mul(M,new_inner),mul(Y,b)),mul(q3,Bt),-1)
assert oldZ==newZ
portpath=ROOT/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';meta=json.loads(portpath.read_bytes())['coefficient_binding']['ports'];ports={}
for n,m in meta.items():
 data=(portpath.parent/'coefficients'/m['file']).read_bytes();raw=gzip.decompress(data)
 assert hashlib.sha256(data).hexdigest()==m['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==m['raw_sha256'] and len(raw)==m['raw_bytes']
 ports[n]=int.from_bytes(raw,'big')
assert ports['beta']>=46 and ports['K0']>=0 and 0<ports['MC']<ports['beta'] and 0<ports['MF']<2*ports['beta']
prime=1000000007

def trim(x):
 while len(x)>1 and x[-1]==0:x.pop()
 return x
def pa(x,y,s):return trim([((x[i] if i<len(x) else 0)+s*(y[i] if i<len(y) else 0))%prime for i in range(max(len(x),len(y)))])
def pm(x,y):
 z=[0]*(len(x)+len(y)-1)
 for j,a in enumerate(x):
  for k,b in enumerate(y):z[j+k]=(z[j+k]+a*b)%prime
 return trim(z)
p={**{n:[v%prime] for n,v in ports.items()},**{n:[0,1] for n in g['witnesses']}}
for n,op,a,b in g['source']:
 va=p[a] if isinstance(a,str) else [a%prime];vb=p[b] if isinstance(b,str) else [b%prime]
 p[n]=pm(va,vb) if op=='*' else pa(va,vb,1 if op=='+' else -1)
assert len(p[g['output']])-1==28 and p[g['output']][-1]==437565601

def calc(graph,v):
 d=dict(v)
 for n,op,a,b in graph['source']:
  x=d[a] if isinstance(a,str) else a;y=d[b] if isinstance(b,str) else b
  d[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return d
rng=random.Random(882811);count=0
for _ in range(50):
 v={n:rng.randrange(-4,5) for n in g['witnesses']+g['fixed_numerals']};new=calc(g,v)
 v['r']+=new['k']*(new['Bt']-new['C']);oldv=calc(old,v)
 assert all(new[n]==oldv[n] for n in ('Z','A0','A1','Fa','g72','output'));count+=1
print(json.dumps({'status':'PASS','pins':PINS,'operation_counts':dict(Counter(r[1] for r in g['source'])),'live_rows':len(rows),'exact_formal_root_identity':True,
 'current_port_bounds':{'beta_at_least_46':True,'K0_nonnegative':True,'MC_between_zero_and_beta':True,'MF_between_zero_and_two_beta':True},
 'diagonal_degree':len(p['output'])-1,'diagonal_leading_coefficient_mod_prime':p['output'][-1],'prime':prime,'wiring_controls':count,
 'limits':['Zero-equivalence uses the explicitly cited mathematical calibration; controls do not prove it.',
 'Source-level theorem applicability and all-model/Lean/iPRA status are not established by this checker.',
 'Degree upper bound is explained in README and relies on the pinned unchanged-factor certificate.']},sort_keys=True,indent=2))
