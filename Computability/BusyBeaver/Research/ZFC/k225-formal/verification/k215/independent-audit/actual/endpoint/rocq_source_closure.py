#!/usr/bin/env python3
"""Comment-aware census of planned actual Rocq inputs; no compiler invocation."""
from pathlib import Path
import json,re,hashlib
plan=Path('/tmp/k215-rocq-complete/plan.json');p=json.loads(plan.read_text())
def strip(s):
 out=[];i=0;dep=0;quoted=False
 while i<len(s):
  if dep:
   if s[i:i+2]=='(*':dep+=1;out+=[' ',' '];i+=2
   elif s[i:i+2]=='*)':dep-=1;out+=[' ',' '];i+=2
   else:out.append('\n'if s[i]=='\n'else' ');i+=1
  elif quoted:
   if s[i:i+2]=='""':out+=[' ',' '];i+=2
   elif s[i]=='"':quoted=False;out.append(' ');i+=1
   else:out.append('\n'if s[i]=='\n'else' ');i+=1
  elif s[i:i+2]=='(*':dep=1;out+=[' ',' '];i+=2
  elif s[i]=='"':quoted=True;out.append(' ');i+=1
  else:out.append(s[i]);i+=1
 assert dep==0 and not quoted
 return ''.join(out)
rows=[];hits=[]
for n in p['order']:
 info=p['modules'][n];q=Path(info['source']);b=q.read_bytes();s=strip(b.decode())
 row={'module':n,'path':str(q),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'expected_reference_sha256':info.get('expected_reference_sha256')};rows.append(row)
 if row['expected_reference_sha256']:assert row['sha256']==row['expected_reference_sha256'],n
 for m in re.finditer(r'\b(?:Admitted|admit|Axiom|Axioms|Parameter|Parameters|Conjecture|native_compute)\b',s):
  line=s[:m.start()].count('\n')+1;hits.append({'module':n,'line':line,'keyword':m[0],'context':s.splitlines()[line-1].strip()})
out={'scope':'Static planned source closure, not loaded-object or final axiom dependency evidence. Module-type parameters can be lawful interfaces; endpoint Print Assumptions remains authoritative.','target':p['target'],'modules_count':len(rows),'plan_sha256':hashlib.sha256(plan.read_bytes()).hexdigest(),'modules':rows,'lexical_hits':hits}
Path('/tmp/k215-endpoint-audit/rocq-source-closure.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'modules':len(rows),'hits':hits},indent=2))
