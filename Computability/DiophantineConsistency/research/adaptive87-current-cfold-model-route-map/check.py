#!/usr/bin/env python3
"""Read-only source/graph interface and exact substitution audit; no Lean."""
import hashlib,json,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
r=Path(__file__).resolve().parents[2];d=Path(__file__).resolve().parent;sha=lambda x:hashlib.sha256(x).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
pins=json.loads((d/'pins.json').read_bytes())
for f,h in pins.items():need(sha((r/f).read_bytes())==h,'pin '+f)
def read(f):return (r/f).read_text()
p=json.loads(read('research/adaptive87-four-square-current88-30/graph.json'));c=json.loads(read('research/adaptive87-current-cfold88-degree28/graph.json'))
changed=[(a,b) for a,b in zip(p['source'],c['source']) if a!=b]
need(len(p['source'])==len(c['source'])==88 and p['witnesses']==c['witnesses'] and p['fixed_numerals']==c['fixed_numerals'] and changed==[(['root_skew','*','k','Bt'],['root_skew','*','k','C'])],'graph cut')
checks={
 'Lean/DiophantineConsistency/ArithmeticAdaptiveScaledNorms2011.lean':['def currentPorts : Fin 4 → ℕ','theorem currentPorts_cast'],
 'Lean/DiophantineConsistency/ModelThirteenCarrier.lean':['theorem port0','theorem port1','theorem port2','theorem port3'],
 'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean':['theorem scalar_rank_window','theorem current_bounds_nat','15≤CurrentMasks2011.beta'],
 'Lean/DiophantineConsistency/ArithmeticAdaptivePowerLowerBound2011.lean':['private theorem beta_lower_nat : 46≤CurrentMasks2011.beta'],
 'Lean/DiophantineConsistency/AdaptiveFirstRootFactor87Literal.lean':['theorem split_expression_eq','theorem current_natural_zero_iff'],
 'Lean/DiophantineConsistency/ArithmeticAdaptiveTransport2011.lean':['theorem expressionAt_transport_positive'],
 'Lean/DiophantineConsistency/ArithmeticAdaptiveFirstDivisibility2011.lean':['theorem current_Y_quotient','theorem positive_Y_quotient_of_facts'],
 'Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean':['theorem scaled_quotient (m z n : V)'],
 'Lean/DiophantineConsistency/Compact44/P72Root.lean':['theorem ι_magnitude_sq'],
 'Lean/DiophantineConsistency/Compact44/ReducedNormSigned.lean':['theorem natural_magnitude_square'],
 'Lean/DiophantineConsistency/Compact44/FreeJMainOrientation.lean':['theorem rank_congruence_from_main'],
 'Lean/DiophantineConsistency/Compact44/P72Exact.lean':['theorem indices_ordinary'],
 'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean':['theorem y_succ','theorem ordinate_strictMono'],
 'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean':['theorem power_bound','theorem projection_quotient'],
 'Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean':['def SameNoZero','theorem bridge'],
 'research/ordinary14-aux-ring-norm-extraction-draft/RingNormExtraction.lean':['theorem root_of_scaled_ring_square'],
 'research/ordinary13-residue-first-index-model-draft/ResidueFirstIndexModel.lean.src':['theorem early_index_of_natural_norm'],
 'research/ordinary13-residue-qbalance-graph-draft/ResidueQBalance.lean.src':['theorem q_balance'],
 'research/ordinary13-positive84-power-model-draft/Positive84Power.lean.src':['theorem sixteen_of_three','theorem growth'],
 'research/ordinary13-positive84-power-model-draft/Positive84OrientedPower.lean.src':['theorem power_of_oriented_balance'],
 'research/ordinary13-positive81-carrier-data-model-draft/PositiveCarrierData.lean.src':['theorem root_data'],
 'research/ordinary13-unscale84-first-margin-draft/UnscaleFirstMargin.lean.src':['theorem qcube_margin'],
 'research/adaptive87-four-square-local-mod4-model-draft/FourSquare88Model.lean.src':['theorem unshifted_same_zero','theorem bridge (hp :']}
for f,ts in checks.items():
 s=read(f)
 for t in ts:need(t in s,'interface '+f+' '+t)
# Free ring identities of the two intended coordinate maps. These are not
# positivity proofs and do not evaluate Lean expressions.
N=9
def var(i):return {tuple(int(i==j) for j in range(N)):1}
def const(k):return {(0,)*N:k} if k else {}
def add(a,b,k=1):
 z=a.copy()
 for n,v in b.items():z[n]=z.get(n,0)+k*v
 return {n:v for n,v in z.items() if v}
def mul(a,b):
 z={}
 for m,v in a.items():
  for n,w in b.items():
   k=tuple(i+j for i,j in zip(m,n));z[k]=z.get(k,0)+v*w
 return {n:v for n,v in z.items() if v}
def prod(*a):
 z=const(1)
 for x in a:z=mul(z,x)
 return z
b,q3,ell,k,rho,C,Bt,s,tau=[var(i) for i in range(N)];M=mul(q3,b);Y=mul(q3,s)
r_old=add(rho,mul(k,add(Bt,C,-1)))
old=add(add(prod(M,add(add(add(ell,k),r_old),mul(k,Bt),-1)),mul(Y,b)),mul(q3,Bt),-1)
new=add(add(prod(M,add(add(add(ell,k),rho),mul(k,C),-1)),mul(Y,b)),mul(q3,Bt),-1)
need(old==new,'candidate to parent formal identity')
# Bt=b*t, rho=k(C−1)+t+tau−ell−s.
t=var(4);Bt=mul(b,t);rho=add(add(add(mul(k,add(C,const(-1))),t),tau),add(ell,s),-1)
new=add(add(prod(M,add(add(add(ell,k),rho),mul(k,C),-1)),mul(Y,b)),mul(q3,Bt),-1)
need(new==mul(M,tau),'parent to positive-root formal identity')
print(json.dumps({'scope':'source markers and formal witness-coordinate identities only; no Lean or model proof','pins_sha256':sha((d/'pins.json').read_bytes()),'changed_gate':'root_skew: k*Bt -> k*C','source_interfaces':len(checks),'candidate_to_parent_ring_identity':True,'parent_to_candidate_positive_root_identity':True,'beta_46_existing_lemma_private':True},sort_keys=True,indent=2))
