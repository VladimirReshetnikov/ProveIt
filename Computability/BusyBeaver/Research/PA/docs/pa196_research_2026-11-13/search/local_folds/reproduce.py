#!/usr/bin/env python3
"""Recompute the supplied context and local-synthesis receipts (about 5 minutes).
Python 3, a C++17 compiler, and the bundled inputs suffice. No network is used.
"""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile
H=Path(__file__).resolve().parent;I=H/'inputs'
def run(args):return subprocess.run([str(x)for x in args],check=True,text=True,capture_output=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def verify_control(raw):
 T={}
 for line in (H/'synthetic.tm').read_text().splitlines():
  q,b,w,d,t=line.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(t))
 count=0
 for line in raw.splitlines():
  f=line.split();kind=f.pop(0);a=list(map(int,f));drop,keep=a[:2]
  patch={tuple(a[k:k+2]):tuple(a[k+2:k+5])for k in range(2,len(a),5)}
  project=lambda q:keep if q==drop else q
  for q in {drop,keep}|{k[0]for k in patch}:
   for mask in range(32):
    b=(mask>>2)&1;w,d,t=T[q,b];goal=(project(t),d,(mask&~4)|(w<<2))
    state,head,tape=project(q),0,mask
    for step in range(16):
     assert 0<=state<4 and -2<=head<=2
     bit=(tape>>(head+2))&1;w,d,t=patch.get((state,bit),T[state,bit])
     tape=(tape&~(1<<(head+2)))|(w<<(head+2));head+=d;state=project(t)
     if(state,head,tape)==goal:break
    else:raise AssertionError(('control did not match',line,q,mask))
  count+=1
 assert count==6 and 'ONE 2 0 1 1 1 -1 3' in raw
 return count
manifest=json.loads((I/'source_manifest.json').read_text())
for name,item in manifest['files'].items():assert sha(I/name)==item['sha256'],name
with tempfile.TemporaryDirectory(prefix='pa196-source-contexts-')as tmp:
 tmp=Path(tmp)
 print('Recomputing all 4,959 symbolic contracts and window refinement...',flush=True)
 context=run([sys.executable,H/'source_contexts.py','--output',tmp]);print(context.stdout,end='')
 assert (tmp/'source_contexts.txt').read_bytes()==(H/'source_contexts.txt').read_bytes()
 got=json.loads((tmp/'source_contexts_receipt.json').read_text());old=json.loads((H/'source_contexts_receipt.json').read_text())
 got.pop('seconds');old.pop('seconds');assert got==old
 print(run([sys.executable,H/'validate_contexts.py']).stdout,end='')
 results={}
 for name,cpp,expected in [('helper',I/'scan_helper.cpp',H/'helper_counts.txt'),('two_row',I/'scan_two_rows.cpp',H/'two_row_counts.txt'),('two_arbitrary',H/'two_arbitrary_rows.cpp',H/'two_arbitrary_counts.txt')]:
  exe=tmp/name;run(['g++','-O3','-std=c++17',cpp,'-o',exe]);answer=run([exe,I/'pa196.tm',H/'source_contexts.txt',tmp/(name+'.txt'),196]);assert answer.stdout==expected.read_text(),name
  assert (tmp/(name+'.txt')).read_bytes()==(H/(name+'_results.txt')).read_bytes(),name
  results[name]=answer.stdout.strip();print(name+': '+answer.stdout,end='',flush=True)
 exe=tmp/'control';run(['g++','-O3','-std=c++17',H/'two_arbitrary_control.cpp','-o',exe])
 answer=run([exe,H/'synthetic.tm',H/'synthetic_contexts.txt',tmp/'control.txt',4,4])
 assert answer.stdout==(H/'control_counts.txt').read_text()
 raw=(tmp/'control.txt').read_text();assert raw==(H/'control_results.txt').read_text()
 count=verify_control(raw)
 print(json.dumps({'status':'REPRODUCTION_PASS','contexts':2219,'source_contracts':4959,'positive_controls_independently_replayed':count,'screen_counts':results},indent=2))
