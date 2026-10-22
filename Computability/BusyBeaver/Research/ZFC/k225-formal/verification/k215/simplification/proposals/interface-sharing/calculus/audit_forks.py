"""Owned source parser/audit; no Lean compilation or received script execution."""
if not __debug__:raise SystemExit('Assertions required: disable optimized Python')
from pathlib import Path
import json,hashlib,re
B=Path(__file__).resolve().parent;P=B/'inputs'
pairs=[('KQ1Model','QuotientModel'),('KQ1Separation','QuotientSeparation'),('KQ1Basic','QuotientBasic'),('KQ1Power','QuotientPower'),('KQ1Replacement','QuotientReplacement'),('KQ1Collect','QuotientCPGIC')]
res=[]
for k,q in pairs:
 s=(P/(k+'.lean')).read_text();t=(P/(q+'.lean')).read_text()
 assert 'Forked by' in s
 res.append({'fork':k,'origin':q,'fork_lines':len(s.splitlines()),'fork_bytes':len(s.encode()),'origin_lines':len(t.splitlines()),'origin_bytes':len(t.encode())})
k=(P/'KQ1Model.lean').read_text();q=(P/'QuotientModel.lean').read_text()
def block(s,a,b):return s[s.index(a):s.index(b)]
# Formula syntax and logical satisfaction induction are exact copies.
a=block(k,'def memberForm','theorem relSat_congr');b=block(q,'def memberForm','theorem relSat_congr')
assert a==b
# Both quotients use the same relation; proof fields may differ but are Prop.
assert 'r := Eqv mem' in block(k,'def modelSetoid','abbrev Domain')
assert 'r := Eqv mem' in block(q,'def modelSetoid','abbrev Domain')
# Both quotient membership definitions use the identical lifted binary predicate.
for s in (k,q):assert 'Quotient.liftOn₂ x y (Member mem)' in block(s,'def quotientMember','theorem mk_eq_iff')
out={'pin':'57541fe0cfe3af62b4cb58747d8d1d7c16b338d5','pairs':res,'gross_fork_lines':sum(r['fork_lines'] for r in res),'gross_fork_bytes':sum(r['fork_bytes'] for r in res),'exact_shared_syntax_lines':len(a.splitlines()),'exact_shared_syntax_bytes':len(a.encode()),'same_setoid_relation_and_lifted_predicate':True,'inputs':[{'file':p.name,'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(P.glob('*.lean'))],'status':'Source checks only; definitional compatibility examples and adapter remain uncompiled.'}
(B/'AUDIT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ('inputs','pairs')},indent=2))
