#!/usr/bin/env python3
"""Bounded source and exact scalar identity audit; no Lean or model theorem."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(path,digest):
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==digest,path;return b
p=json.loads(pin('research/ordinary13-qcube-unscale84/candidate.json','2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77'))
c=json.loads(pin('research/ordinary13-residue-first82/candidate.json','bb90faa3815c5ff46f5fdbf41c2d001790d565baa17d97c79514c33fa928f1d2'))
aux=json.loads(pin('research/ordinary13-aux-root87-36/candidate.json','abdd93cebd85dc2194478a76297d16ea04ca06855265420abf0b6c1b7e70db51'))
sq=json.loads(pin('research/ordinary13-four-square88-30/candidate.json','daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420'))
assert len(p['source'])==84 and len(c['source'])==82 and len(aux['source'])==87 and len(sq['source'])==88
assert p['witnesses']==c['witnesses'] and p['fixed_numerals']==c['fixed_numerals'] and p['output']==c['output']
rows=[]
for n,o,a,b in p['source']:
 if n in {'g25','g28'}:continue
 if n=='g26':rows.append(['g26','+','X','K0'])
 elif n=='Bt':rows.append(['Bt','-','g27','F'])
 else:rows.append([n,o,a,b])
assert rows==c['source']
# Small exact free-ring polynomial arithmetic.
def var(n):return {(n,):1}
def con(n):return {():n} if n else {}
def add(a,b,s=1):
 z=dict(a)
 for k,v in b.items():z[k]=z.get(k,0)+s*v
 return {k:v for k,v in z.items() if v}
def mul(a,b):
 z={}
 for x,a0 in a.items():
  for y,b0 in b.items():
   k=tuple(sorted(x+y));z[k]=z.get(k,0)+a0*b0
 return {k:v for k,v in z.items() if v}
b,C,X,K,F,k,ell,r=map(var,['b','C','X','K','F','k','ell','r']);q=add(con(1),b)
Bp=add(mul(C,add(X,K)),F,-1);B=add(mul(C,add(X,mul(K,q))),mul(F,q),-1);D0=add(mul(C,K),F,-1)
assert B==add(Bp,mul(b,D0))
rold=add(r,mul(add(mul(k,b),con(1)),D0))
def carrier(P,R):return add(mul(b,add(add(add(ell,k),R),mul(k,P),-1)),P,-1)
assert carrier(B,rold)==carrier(Bp,r)
# Scalar counterexample has no full-graph claim.
q0,b0,F0,alpha0,K0,X0=47,46,1,45,0,47
C0=q0-F0-alpha0;old=C0*(X0+K0*q0)-F0*q0;new=C0*(X0+K0)-F0
assert q0==1+b0 and C0==1 and old==0 and new==46 and new%b0==0
sources={
 'Lean/DiophantineConsistency/Compact44/FreeJ13Halt.lean':('18b17a1c81e6ff58d74fd6a7160948b75c71203ee8f5c3bd29e4d3fc9a76218a',['theorem positive_model_iff','InternalZero (graph CompactSymbolicModelIff.p).output']),
 'Lean/DiophantineConsistency/Compact44/IPRAOrdinary13.lean':('c6b54e6098062be18966a9fd5891284909bd1454d6d6ee8b0db26e808045a735',['theorem native_equivalence','∼mappedNativeRefutation embedding']),
 'Lean/DiophantineConsistency/Compact44/FreeJMainOrientation.lean':('d02beb02122e682deef3e89c3dcb8e3e6aea31ddfbc4f320fe6af9a3df7f9a6b',['def FreeJMainCongruence','theorem rank_congruence_from_main']),
 'Lean/DiophantineConsistency/Compact44/FreeJPellIndices.lean':('9e098156d8aff2540e00ee31667954d7288844aad859c9df74f988c7fe0611ac',['def FreeJIndices','magnitude (pairEval (core (fun j => (p j:ℤ))).z v)=M*first']),
 'Lean/DiophantineConsistency/Compact44/FreeJEarlyIndex.lean':('ab9b8e34903eff1e33e81b6a75438797eef1f2dab84595e23516b44de774ea3d',['theorem early_index_of_facts']),
 'Lean/DiophantineConsistency/Compact44/P72Exact.lean':('a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',['theorem indices_ordinary','(haux :']),
 'Lean/DiophantineConsistency/Compact44/FreeJPowerFinish.lean':('e4b2e84586b6232b9accc7775f094d4e1047453f1e8337f6241d39a6657d8816',['theorem graph_power','(hz : InternalZero (literal']),
 'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean':('636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390',['theorem power_bound','theorem projection_quotient']),
 'research/ordinary14-aux-root-model-draft/AuxRootBridge.lean':('796819c48d53665e1ee9c90d8d1bfd0fbd00cd4ca5535fe4fad1a3462d74c8b7',['theorem positive_aux_coordinate_iff']),
 'research/ordinary14-aux-norms-to-bounds-draft/NormsToBounds.lean':('c93161930052792db7b9ebb08f04f897e70d70fa84d390926521b7b4e28a70f8',['theorem aux_bounds_of_natural_norms']),
 'research/ordinary13-freej88-four-square-lean-draft/P88FourSquareModel.lean':('1fb9d7a6d1b906c87877c3146787c5fea5558f2473aac029b7be702763df7192',['theorem zero_iff']),
 'research/ordinary13-freej88-lean-draft/P88PairModel.lean':('21d468a34cf1dfc8df9b2fa4e4ad359294a1047f28ac3aec39bb4f2cc054001a',['theorem zero_iff'])}
for path,(h,need) in sources.items():
 text=pin(path,h).decode()
 for entry in need:assert entry in text,(path,entry)
print(json.dumps({'scope':'source-pinned graph delta, formal polynomial identities and scalar counterexample; not a full zero or a Lean proof','graph_operations':[84,82,87,88],'B_difference_identity':True,'signed_r_identity':True,'counterexample':{'beta':46,'J':1,'q':q0,'F':F0,'alpha':alpha0,'K0':K0,'X':X0,'Bprime':new,'B':old,'Bprime_divisible_by_b':True,'is_full_zero':False},'source_signatures_pinned':len(sources),'lean_elaboration':False},sort_keys=True,indent=2))
