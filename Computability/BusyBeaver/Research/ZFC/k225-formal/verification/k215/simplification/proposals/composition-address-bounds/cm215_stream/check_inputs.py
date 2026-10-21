#!/usr/bin/env python3
"""Check the exact input identities and finite table representation."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent

def check():
 manifest=json.loads((ROOT/'source_manifest.json').read_text())
 for rel,digest in manifest['files'].items():
  assert hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==digest,rel
 machine={}
 for line in (ROOT/'marker215.tm').read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,n=line.split();key=int(q),int(b)
  assert key not in machine
  machine[key]=int(w),d,int(n)
 assert set(machine)=={(q,b) for q in range(215) for b in (0,1)}
 assert all(w in (0,1) and d in ('L','R') and 0<=n<=215 for w,d,n in machine.values())
 def parse_table(path):
  rows=re.findall(r'\((true|false), ([LR]), (\d+), (true|false), ([LR]), (\d+)\)',path.read_text())
  return {(q,b):(int(row[3*b]=='true'),row[3*b+1],int(row[3*b+2])) for q,row in enumerate(rows) for b in (0,1)}
 assert parse_table(ROOT/'CM215Table.v')==machine
 old=parse_table(ROOT/'vendor/K215F/Table215.v')
 changes=[{'state':q,'read':b,'K215':list(old[q,b]),'CM215':list(machine[q,b])} for q,b in sorted(old) if old[q,b]!=machine[q,b]]
 assert len(changes)==6
 return {'status':'PASS','working_states':215,'rows':430,'changed_rows':changes,'exact_source_files':len(manifest['files'])}
if __name__=='__main__': print(json.dumps(check(),indent=2))
