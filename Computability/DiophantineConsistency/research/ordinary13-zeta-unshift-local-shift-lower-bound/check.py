from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-zeta-unshift-local-shift-lower-bound')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
g=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text());r={x[0]:x for x in g['source']}
for row in [['kbase','+','n_eta','n_zeta'],['R','+','g47','g50'],['r0base','-','kbase','R'],['r0','-','r0base',1],['g54','*','U','n_gamma'],['shift','-','g54','r0']]:assert r[row[0]]==row
# Exact sparse polynomial arithmetic over Z[x,R,k]. Inputs are x=g54,
# R, k, and independently available constants 0,1,3,4. Gate count assumes
# only these values are already computed; this is not a full-circuit bound.
def pol(d):return tuple(sorted((e,c) for e,c in d.items() if c))
def add(a,b,sgn=1):
 d=dict(a)
 for e,c in b:d[e]=d.get(e,0)+sgn*c
 return pol(d)
def mul(a,b):
 d={}
 for e,c in a:
  for f,v in b:
   m=tuple(x+y for x,y in zip(e,f));d[m]=d.get(m,0)+c*v
 return pol(d)
zero=pol({});one=pol({(0,0,0):1});x=pol({(1,0,0):1});R=pol({(0,1,0):1});k=pol({(0,0,1):1})
base={zero,one,pol({(0,0,0):3}),pol({(0,0,0):4}),x,R,k}
target=add(add(add(x,R),one),k,-1)
onegate=set(base)
for a in base:
 for b in base:onegate.update((add(a,b),add(a,b,-1),mul(a,b)))
assert target not in onegate
# One newly computed intermediate then one final gate; the intermediate may
# be reused twice, and all combinations/orderings of initial leaves are tried.
twogate=set(onegate)
for a in onegate:
 for b in base|{a}:
  twogate.update((add(a,b),add(a,b,-1),add(b,a,-1),mul(a,b)))
assert target not in twogate
# Construct three gates, exactly matching the literal structure.
r0base=add(k,R,-1);r0=add(r0base,one,-1);out=add(x,r0,-1)
assert out==target
print(json.dumps({'local_shift_two_gate_impossible_over_Z':True,'local_three_gate_construction':True,'initial_terminal_count':len(base),'distinct_up_to_one_gate':len(onegate),'distinct_up_to_two_gates':len(twogate),'full_circuit_minimality_proved':False,'zero_set_equivalence_proved':False,'lean_executed':False},sort_keys=True,indent=2))
