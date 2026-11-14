#!/usr/bin/env python3
"""Independent exact-table census and local-helper proof audit.

Run from any directory; uses the accompanying selected inputs directory.
All checks use explicit exceptions and stay enabled under python -O.
"""
from pathlib import Path
from collections import deque
import json,hashlib,argparse

def require(x,msg):
 if not x:raise ValueError(msg)
def read(path):
 rows={};start=0
 for line in path.read_text().splitlines():
  if line.startswith('#! start'):start=int(line.split()[-1])
  if not line.strip() or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
  require((q,b) not in rows,'duplicate row')
  require(b in [0,1] and w in [0,1] and d in ['L','R'],'bad symbol/action')
  rows[q,b]=(w,1 if d=='R' else -1,z)
 states={q for q,b in rows};halts={z for w,d,z in rows.values()}-states
 require(len(halts)==1,'exactly one halt label required')
 require(len(rows)==2*len(states),'two rows per state required')
 return rows,start,next(iter(halts))
def canonical(rows,start,halt):
 order=[start];names={start:0};edges=[]
 for q in order:
  for b in (0,1):
   w,d,z=rows[q,b]
   if z!=halt and z not in names:names[z]=len(order);order.append(z)
   edges.append([w,d,-1 if z==halt else names[z]])
 require(len(names)==len(rows)//2,'some states unreachable in graph')
 return hashlib.sha256(json.dumps(edges,separators=(',',':')).encode()).hexdigest(),names

def helper_check(base,candidate,p):
 drop,keep,bit,x0,x1,w0,w1=p
 pi=lambda q:keep if q==drop else q
 expected={(q,b):(w,d,pi(z)) for (q,b),(w,d,z) in base.items() if q!=drop}
 expected[keep,bit]=(bit,-1,500)
 expected[500,0]=(w0,1,pi(x0));expected[500,1]=(w1,1,pi(x1))
 require(candidate==expected,'helper table differs from patch')
 require(0 not in (drop,keep) and 500 not in {q for q,b in base},'helper/start conflicts')
 cases=[]
 for q in (drop,keep):
  inc=[(k,v) for k,v in base.items() if v[2]==q]
  require(inc and all(v[1]==1 for k,v in inc),'all incoming must move right')
  tags={v[0] for k,v in inc};require(len(tags)==1,'predecessor tag must be unique');tag=tags.pop()
  for b in (0,1):
   tape={-1:tag,0:b};after=dict(tape);ow,od,oz=base[q,b];after[0]=ow
   h=0;s=keep
   for n in range(1,8):
    require(h in tape,'reads opaque exterior')
    require((s,tape[h]) in candidate,'interior halt')
    w,d,z=candidate[s,tape[h]];tape[h]=w;h+=d;s=z
    if (s,h,tape)==(pi(oz),od,after):break
   else:raise ValueError('local macro mismatch')
   cases.append({'old_state':q,'symbol':b,'tag':tag,'steps':n})
 return cases

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--inputs',type=Path,default=Path(__file__).parent/'inputs');ap.add_argument('--output',type=Path,default=Path(__file__).parent/'comparison_results.json');args=ap.parse_args()
 manifest=json.loads((args.inputs/'manifest.json').read_text());records=[];class_names={};baselines={}
 for item in manifest['machines']:
  path=args.inputs/item['file'];require(hashlib.sha256(path.read_bytes()).hexdigest()==item['sha256'],'input hash mismatch')
  rows,start,halt=read(path);digest,mapping=canonical(rows,start,halt)
  if item['kind']=='original208':
   class_names.setdefault(digest,chr(65+len(class_names)))
  record={**item,'states':len(rows)//2,'rows':len(rows),'start':start,'halt':halt,'canonical_sha256':digest,'state_to_bfs':mapping}
  if 'helper' in item:
   baselabel=item['helper']['base'];base=read(args.inputs/manifest['helper_baselines'][baselabel])[0]
   record['local_blocks']=helper_check(base,rows,item['helper']['parameters'])
  records.append(record)
 original=[r for r in records if r['kind']=='original208'];helpers=[r for r in records if r['kind']=='helper208']
 require(len(original)==9 and len({r['canonical_sha256'] for r in original})==2,'original class count')
 require(len(helpers)==18 and len({r['canonical_sha256'] for r in helpers})==18,'helper class count')
 require(not {r['canonical_sha256'] for r in original}&{r['canonical_sha256'] for r in helpers},'helper duplicates original')
 for r in original:r['graph_class']=class_names[r['canonical_sha256']]
 result={'status':'PASS','original208_presentations':9,'original208_graph_classes':2,'additional208_presentations':18,'additional208_graph_classes':18,'total_accepted208_graph_classes':20,'machines':records}
 args.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k!='machines'},indent=2))
if __name__=='__main__':main()
