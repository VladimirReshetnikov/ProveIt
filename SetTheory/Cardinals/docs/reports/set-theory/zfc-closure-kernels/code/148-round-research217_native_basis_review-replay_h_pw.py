"""Replay fixed H/PW certificate using supplied explicit substitutions only.
No received code imported or executed; no unification or formula search.
"""
from pathlib import Path
import json,re,hashlib
root=Path(__file__).resolve().parent.parent
source=root/'research217_three_variable_axioms'
rows=json.loads((source/'H_PW_certificate.json').read_text())
audit=json.loads((source/'H_PW_VERIFIED.json').read_text())
def prefix(s,ns):
 def at(k):
  if s[k]!='C':return ns+s[k],k+1
  a,k=at(k+1);b,k=at(k);return (a,b),k
 a,k=at(0);assert k==len(s);return a
def infix(s):
 toks=re.findall(r'\(|\)|->|[a-z]+',s)
 def at(k):
  if toks[k]!='(':return toks[k],k+1
  a,k=at(k+1);assert toks[k]=='->';b,k=at(k+1);assert toks[k]==')';return (a,b),k+1
 a,k=at(0);assert k==len(toks);return a
def vars(t):return {t} if isinstance(t,str) else vars(t[0])|vars(t[1])
def sub(t,env):
 if isinstance(t,str):return env.get(t,t)
 return (sub(t[0],env),sub(t[1],env))
assert rows[0]['polish']=='CCpqCCqrCpr' and rows[1]['polish']=='CCCpqpCrp'
past={r['id']:r for r in rows};checks=[]
for step in audit['steps']:
 idx=step['id'];row=past[idx];assert row['parents']==step['parents']
 major_id,minor_id=row['parents'];assert major_id<idx and minor_id<idx
 major=prefix(past[major_id]['polish'],'m');minor=prefix(past[minor_id]['polish'],'n')
 env={k:infix(v) for k,v in step['substitution'].items()}
 assert all(not (vars(v)&set(env)) for v in env.values()),'substitution is not fully simultaneous/normalized'
 actual_major=sub(major,env);actual_minor=sub(minor,env);target=prefix(row['polish'],'t')
 assert isinstance(actual_major,tuple)
 assert actual_major[0]==actual_minor and actual_major[1]==target
 assert actual_major==infix(step['major_instance'])
 assert actual_minor==infix(step['minor_instance'])
 assert target==infix(step['conclusion'])
 checks.append({'line':idx,'major':major_id,'minor':minor_id,'explicit_mp':True})
assert len(checks)==10 and past[10]['polish']=='CCCpqpp' and past[12]['polish']=='CpCqp'
report={'status':'PASS_FIXED_EXPLICIT_SUBSTITUTION_REPLAY','steps':checks,'executed_received_code':False,
 'formula_search':False,'native_interpretation':'Interpret each free schematic variable as an arbitrary natural and each pair-node as native I=4P. Structural equalities remain exact numerical equalities, including I(0,0)=0. Each earlier schema is re-instantiated at numeric constructor terms; no object-language theorem substitution or label renaming is assumed.',
 'scope':'Independently replays K and Peirce from H/PW; the further H/K/Peirce-to-S bridge is separately reviewed in NATIVE_CALIBRATION.md, not included in this ten-step receipt.',
 'inputs':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [source/'H_PW_certificate.json',source/'H_PW_VERIFIED.json']}}
(root/'research217_native_basis_review/H_PW_NATIVE_REPLAY.json').write_text(json.dumps(report,indent=2)+'\n')
print(report['status'],len(checks),'MP steps')
