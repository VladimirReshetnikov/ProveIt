#!/usr/bin/env python3
"""Check structural bridge-plan claims independently; no Lean or lift claim."""
import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';oldp=research/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json';newp=research/'nine-sharing-sign16-degree112-v-candidate/seed.json';plan=newp.parent/'PROOF_PLAN.md';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(oldp)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac' and sha(newp)=='564ac66abad0fb5e286e5c0c05b5c3cbd05de13e68c9c9ac0b7c3a20a0c0b624' and sha(plan)=='bc984ccad33f48e32168bd110050cac1dfc0a0be4d655babe5015a8cee3d7af0'
old,new=json.loads(oldp.read_text()),json.loads(newp.read_text());r={x['gate']:x['expr'] for x in old['residuals']};assert len(old['residuals'])==8 and len(new['residuals'])==7
v=r['V'];assert v[0]=='sub' and v[1]==['var',17];replacement=v[2];assert replacement==new['lift_expression'];f=['add',['var',5],['num',1]];c=replacement[2];assert replacement[0]=='sub' and replacement[1]==['mul',['mul',f,f],['var',16]]
beta=['port','beta'];J=['add',['var',1],['num',1]];F=['add',['var',2],['num',1]];alpha=['add',['var',3],['num',1]];T=['add',['var',7],['num',1]];q=['add',['mul',beta,J],['num',1]];Y=['mul',['add',['var',8],['num',1]],['mul',['mul',q,q],q]];expectedc=['add',['mul',['add',['add',['var',11],['num',1]],['add',['var',12],['num',1]]],Y],['add',['var',11],['num',1]]];assert c==expectedc
# Check the plan's compact R identity by an independent sparse multivariate
# integer expansion, because the seed's transport expression is rearranged.
def P(t):
 if t[0]=='num':return {():t[1]} if t[1] else {}
 if t[0] in ('var','port'):return {(str(t),):1}
 a,b=P(t[1]),P(t[2]);z={}
 if t[0] in ('add','sub'):
  for k,x in a.items():z[k]=z.get(k,0)+x
  for k,x in b.items():z[k]=z.get(k,0)+(x if t[0]=='add' else -x)
 else:
  assert t[0]=='mul'
  for x,i in a.items():
   for y,j in b.items():
    key=tuple(sorted(x+y));z[key]=z.get(key,0)+i*j
 return {k:x for k,x in z.items() if x}
R=['add',['mul',['add',['mul',['sub',q,['num',1]],['sub',q,F]],alpha],['sub',['mul',q,q],['num',1]]],['mul',['add',['port','MC'],['mul',q,['port','MF']]],J]]
assert r['cTminusR'][:2]==['sub',['var',16]]
assert P(r['cTminusR'][2])==P(['sub',['mul',c,T],R])
na=r['Na']
def counts(t):
 if t[0]=='var':return int(t[1]==17),0
 if t[0] in ('num','port'):return 0,0
 x,y=counts(t[1]),counts(t[2]);return x[0]+y[0],x[1]+y[1]+int(t==['mul',['var',17],['var',17]])
for gate,t in r.items():
 if gate!='V':assert counts(t)==((2,1) if gate=='Na' else (0,0))
# Inspect the named ingredients, explicitly preserving their premises.
paths={'window':research/'nine-sharing-sign33-windows-retry01/src/DiophantineConsistency/Sign33Windows.lean','ring':research/'nine-sharing-sign33-inner-v-ring-check/src/DiophantineConsistency/Sign33InnerVRing.lean','absdiff':research/'nine-sharing-sign33-absdiff-square-check/src/DiophantineConsistency/Sign33AbsDiffSquare.lean'}
w=paths['window'].read_text();g=paths['ring'].read_text();d=paths['absdiff'].read_text()
for t in ('theorem windows_from_maintained_norms','(hbeta : 0<beta) (hMC : MC<beta) (hMF : MF<2*beta)','I*I*u*u+y*y=1+I*I*y*y →','0<q-F-alpha ∧ R+2<E ∧ 2*R<c'):assert t in w
for t in ('theorem inner_v_of_window_and_strong','(hhalf : 2*r<c)','(hstrict : f*f=1+delta a*(i*c*c)*(i*c*c))','0 ≤ ι f*ι f*(ι c*ι T-ι r)-ι c'):assert t in g
assert 'theorem absdiff_sq' in d and '(ι x-ι y)*(ι x-ι y)' in d
# Replay the already independently authored external AST/degree check to an
# in-memory buffer only; never overwrite its frozen packet.
p=root/'reviews/nine-sharing-sign16-external-independent/check.py';assert sha(p)=='3d0c64011a08b94a1cf5ec51c921777401ae8447557eabec4c8936a353b48f59';z=subprocess.run([sys.executable,'-I','-S','-B',str(p)],capture_output=True,text=True,check=True,timeout=120);result=json.loads(z.stdout);assert result['status']=='PASS_EXTERNAL_INDEPENDENT' and result['Na_coefficient_t56']=={'beta^34':64}
print(json.dumps({'status':'PASS_CONDITIONAL_PLAN_REVIEW','old_sha256':sha(oldp),'candidate_sha256':sha(newp),'plan_sha256':sha(plan),'lemma_source_sha256':{k:sha(v) for k,v in paths.items()},'plan_claim':'compact cT-R and V identities independently expanded, Na contains deleted V only squared','scope':'preliminary proof route only; retained rows imply window hypotheses, nonnegative lift, model bridge, unconditional equivalence and iPRA remain unproved'},sort_keys=True,indent=2))
