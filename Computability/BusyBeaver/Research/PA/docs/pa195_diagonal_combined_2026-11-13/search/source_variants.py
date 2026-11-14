import json
from pathlib import Path
P=Path(__file__).resolve().parent
base=json.loads((P.parent/'machine/emitter_tokens.json').read_text())
I=lambda a,b:('I',a,b)
M=lambda a,b:('M',a,b)
U=lambda a,b:('U',a,b)
E=lambda a,b:('E',a,b)
N=lambda a:I(a,1)
Ex=lambda a,b:N(U(a,N(b)))
D,H,A='D','H','A'
heads=[I(Ex(D,U(D,H)),H),I(U(D,U(A,H)),U(A,U(D,H))),I(M(H,D),I(E(H,A),M(A,D))),I(E(H,D),I(M(A,H),M(A,D))),Ex(D,E(H,D)),I(U(D,A),I(U(D,I(A,H)),U(D,H)))]
def emit(t):
 if isinstance(t,str):return ['copy'+t]
 if t==1:return ['push','incT']
 op,x,y=t
 if op=='U':x,y=y,x
 return emit(x)+emit(y)+['cons']+['incT']*{'I':0,'M':1,'U':2,'E':3}[op]
segments=[emit(t) for t in heads]
assert sum(segments,[])==base[18:121]
variants=[]
for j in [2,3,5]:
 t=heads[j]
 assert t[0]=='I' and t[2][0]=='I'
 replacement=I(t[2][1],I(t[1],t[2][2]))
 word=base[:18]+sum([emit(replacement) if k==j else s for k,s in enumerate(segments)],[])+base[121:]
 variants.append(dict(name=f'head{j+1}_antecedents_exchanged',word=word,old_formula=heads[j],new_formula=replacement,proof='A -> (B -> C) and B -> (A -> C) are interderivable by fixed classical implicational proof templates; the same parameter guards and stack slot are retained.'))
# The two parameters of rho8 not constrained by domination may be exchanged.
rho=base[:]
for j in range(6,18):
 if rho[j]=='copyA':rho[j]='copyH'
 elif rho[j]=='copyH':rho[j]='copyA'
variants.append(dict(name='rho8_free_parameters_exchanged',word=rho,old_formula='((H -> d) -> D) -> ((D -> H) -> (A -> H))',new_formula='((A -> d) -> D) -> ((D -> A) -> (H -> A))',proof='The rho8 family is unchanged under permutation of free arguments A,H; the restricted argument pair d <= D is unchanged. During synthesis h is reset to zero, so x,y,c can realize every required tuple.'))
# All combinations of these exact source substitutions.
for mask in range(1,16):
 word=base[:]
 hh=heads[:]
 for bit,j in enumerate([2,3,5]):
  if mask>>bit&1:
   t=hh[j];hh[j]=I(t[2][1],I(t[1],t[2][2]))
 word=base[:18]+sum([emit(t) for t in hh],[])+base[121:]
 if mask&8:
  for j in range(6,18):
   if word[j]=='copyA':word[j]='copyH'
   elif word[j]=='copyH':word[j]='copyA'
 variants.append(dict(name=f'combo_{mask:04b}',word=word))
for v in variants:assert len(v['word'])==191
(P/'safe_variants.json').write_text(json.dumps(variants,indent=2)+'\n')
(P/'head_segments.json').write_text(json.dumps([dict(start=18+sum(map(len,segments[:j])),end=18+sum(map(len,segments[:j+1])),word=s,formula=heads[j]) for j,s in enumerate(segments)],indent=2)+'\n')
print(len(variants), 'variants saved',P/'safe_variants.json')
for x in json.loads((P/'head_segments.json').read_text()):print(x['start'],x['end'],x['formula'])
extra=[]
for name,formula,proof in [('diagonal_contrapositive',I(N(U(A,A)),N(A)),'Fixed classical contraposition proves equivalence to the original Gamma(A).'),('diagonal_negative',I(N(A),U(A,N(A))),'Vacuity passes to negation using generalization, distribution and head1. Applied twice plus double-negation equivalence, negative vacuity is equivalent to original Gamma(A).')]:
 word=base[:121]+emit(formula)+base[128:]
 extra.append(dict(name=name,word=word,new_formula=formula,proof=proof))
(P/'dual_diagonal_variants.json').write_text(json.dumps(extra,indent=2)+'\n')
