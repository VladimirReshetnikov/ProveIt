"""Enumerate and hash successful Lean package object/companion opens from strace.

Run Lean under `strace -f -qq -e trace=open,openat -o TRACE ...` first. The
trace is scoped to that invocation; this records actual opens, not an assertion
of complete package source provenance or an audit of unobserved executions.
"""
from pathlib import Path
import hashlib,json,re,sys
if len(sys.argv)!=3:raise SystemExit('usage: audit-loaded-package.py TRACE OUTPUT_JSONL')
trace=Path(sys.argv[1]);out=Path(sys.argv[2]);prefix='/tmp/ha87-full-source-jrvxi6bb/package-lib/'
loaded=set()
for line in trace.read_text(errors='replace').splitlines():
 if ' = -1 ' in line:continue
 match=re.search(r'open(?:at)?\([^\"]*"([^\"]+)"',line)
 if not match:continue
 p=match.group(1)
 if p.startswith(prefix) and ('.olean' in p or p.endswith('.ir')):loaded.add(p)
with out.open('w') as f:
 for i,name in enumerate(sorted(loaded)):
  path=Path(name);h=hashlib.sha256()
  with path.open('rb') as z:
   for chunk in iter(lambda:z.read(1048576),b''):h.update(chunk)
  f.write(json.dumps({'path':name,'resolved':str(path.resolve()),'sha256':h.hexdigest()},sort_keys=True)+'\n')
  if (i+1)%1000==0:print(i+1,flush=True)
print('PASS',len(loaded),flush=True)
