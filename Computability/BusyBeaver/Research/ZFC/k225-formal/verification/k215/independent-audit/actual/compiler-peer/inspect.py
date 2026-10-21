#!/usr/bin/env python3
"""Independent source-only binding; no compiler/generator or supplied-code execution."""
from pathlib import Path
import json,re,hashlib
R=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/k225-formal');E=R/'rocq/rocq-extension';names=['EnumPerm','L1_SoundPerm','L1_CompPerm','SeedPerm'];rows=[]
def pin(p):
 b=p.read_bytes();return{'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
def strip(s):
 out=[];i=0;depth=0;quoted=False
 while i<len(s):
  if depth:
   if s[i:i+2]=='(*':depth+=1;i+=2;out.extend('  ')
   elif s[i:i+2]=='*)':depth-=1;i+=2;out.extend('  ')
   else:out.append('\n'if s[i]=='\n'else' ');i+=1
  elif quoted:
   if s[i:i+2]=='""':out.extend('  ');i+=2
   elif s[i]=='"':quoted=False;i+=1;out.append(' ')
   else:out.append('\n'if s[i]=='\n'else' ');i+=1
  elif s[i:i+2]=='(*':depth=1;i+=2;out.extend('  ')
  elif s[i]=='"':quoted=True;i+=1;out.append(' ')
  else:out.append(s[i]);i+=1
 assert depth==0 and not quoted;return ''.join(out)
for n in names:
 p=R/'rocqperm'/f'{n}.v';q=E/'coq/215'/f'{n}.v';raw=p.read_text();gen=q.read_text();header=f'(** k225-formal/rocqperm/{n}.v (SHA256 {pin(p)["sha256"]}) under namespace K215F. *)\n';expect=header+raw.replace('From NS Require','From K215F Require');assert gen==expect,n
 rows.append({'module':n,'original':pin(p),'generated':pin(q),'exact_header_and_namespace_only':True})
man=json.loads((E/'manifest.json').read_text());ns=man['variants']['215']['compile_order'];assert len(ns)==42
allrows=[]
for n in ns:
 p=E/'coq/215'/f'{n}.v';raw=p.read_text();clean=strip(raw)
 assert not re.search(r'\b(?:NS|K217F|K218F|K219F|K216F|K221F)\.',clean),(n,'stale qualified namespace')
 assert not re.search(r'From\s+(?:NS|K217F|K218F|K219F|K216F|K221F)\s',clean),(n,'stale imported namespace')
 imports=[]
 for m in re.finditer(r'From\s+K215F\s+Require(?:\s+(?:Import|Export))?\s+([\w\s.]+?)\.(?=\s|$)',clean):
  for mod in m[1].split():assert mod in ns,(n,mod);imports.append(mod)
 allrows.append({'module':n,**pin(p),'local_imports':imports})
out={'status':'PASS_STATIC_NAMESPACE_BINDINGS','four_exact_namespace_only_copies':rows,'all42_scanned_for_stale_local_namespaces':allrows,'scope':'The four command compiler/soundness/seed files received full manual source review. Other generated42 modules only namespace/import inventory here; earlier endpoint/table audit is separate. No compiler invocation or proof outcome claimed.'}
Path('/tmp/k215-rocq-compiler-peer/bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'four_exact_copies':len(rows),'generated_namespace_scans':len(allrows)}))
