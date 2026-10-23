"""New deterministic Bose--Chowla B2 constructor and exhaustive verifier."""
import json,pathlib,itertools,math,hashlib
ROOT=pathlib.Path(__file__).resolve().parent
M=1023;poly=1033 # x^10+x^3+1

def mul(a,b):
 r=0
 while b:
  if b&1:r^=a
  b>>=1;a<<=1
  if a&1024:a^=poly
 return r

def powr(a,n):
 r=1
 while n:
  if n&1:r=mul(r,a)
  a=mul(a,a);n>>=1
 return r
logs={};x=1
for i in range(M):
 if x in logs:raise ValueError('not primitive')
 logs[x]=i;x=mul(x,2)
if x!=1 or len(logs)!=1023:raise ValueError('not field primitive')
subgen=powr(2,33);sub=[0]+[powr(subgen,i) for i in range(31)]
if len(set(sub))!=32 or any(powr(a,32)!=a for a in sub):raise ValueError('subfield failed')
raw=[logs[2^a] for a in sub];base=[(v-raw[0])%M for v in raw]
best=(-1,0,0)
for u in range(1,M):
 if math.gcd(u,M)!=1:continue
 a=sorted(x*u%M for x in base)
 for i,x in enumerate(a):
  gap=(a[(i+1)%32]+(M if i==31 else 0))-x
  if gap>best[0]:best=(gap,u,a[(i+1)%32])
gap,u,shift=best;w=sorted((x*u-shift)%M for x in base)
codes={}
for pair in itertools.combinations_with_replacement(range(32),2):
 z=sum(w[j] for j in pair)%M
 if z in codes:raise ValueError('not B2')
 codes[z]=pair
out={'field_degree':10,'modulus_polynomial_bits':poly,'generator':2,'multiplicative_order':M,'order_prime_factors':[3,11,31],'subfield_generator':subgen,'subfield_elements':sub,'logarithms':raw,'affine_multiplier':u,'affine_translation':-shift,'largest_gap':gap,'weights_with_padding_zero':w,'weights':w[1:],'maximum_weight':max(w),'two_multiset_count':len(codes),'target_spacing':2*max(w)+1,'twenty_two_target_maximum':22*(2*max(w)+1),'algorithm':'Bose-Chowla GF(32^2), exhaustive affine unit/arc minimization'}
(ROOT/'B2_CERTIFICATE.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
