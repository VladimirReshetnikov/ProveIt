from pathlib import Path
import json,gzip,hashlib,re,argparse
if not __debug__:raise SystemExit('Assertions required')
R=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
def parse(text):
 start=re.search(r'start\s+(\d+)',text);start=int(start.group(1))if start else 0
 rows=[]
 for line in text.splitlines():
  if not line.strip()or line.startswith('#'):continue
  q,b,w,d,z=line.split();rows.append([int(q),int(b),int(w),d,int(z)])
 return start,rows
def fingerprint(rows,start,reflection=False):
 T={(q,b):(w,d,z)for q,b,w,d,z in rows};working={q for q,b in T};labels={start:0};todo=[start];out=[]
 for q in todo:
  pair=[]
  for b in(0,1):
   w,d,z=T[q,b]
   if z not in working:target='HALT'
   else:
    if z not in labels:labels[z]=len(labels);todo.append(z)
    target=labels[z]
   if reflection:d='L'if d=='R'else'R'
   pair.append([w,d,target])
  out.append(pair)
 return json.dumps(out,separators=(',',':')),len(labels)
start,rows=parse((R/'forced215/machine.native.tm').read_text());target,n=fingerprint(rows,start);assert n==215
corpus=json.loads(gzip.decompress((R/'inputs/prior_215_tables.json.gz').read_bytes()));records=[]
for item in corpus['tables']:
 direct,count=fingerprint(item['rows'],item['start']);mirror,_=fingerprint(item['rows'],item['start'],True)
 records.append(dict(path=item['path'],reachable=count,equal=direct==target,reflection_equal=mirror==target,source_sha256=item['original_sha256']))
for path,text in json.loads((R/'inputs/additional_prior_tables.json').read_text()):
 s,r=parse(text);direct,count=fingerprint(r,s);mirror,_=fingerprint(r,s,True)
 records.append(dict(path=path,reachable=count,equal=direct==target,reflection_equal=mirror==target,source_sha256=hashlib.sha256(text.encode()).hexdigest()))
out=dict(status='FINITE_CORPUS_ROOTED_GRAPH_COMPARISON',target_sha256=hashlib.sha256((R/'forced215/machine.native.tm').read_bytes()).hexdigest(),frozen_corpus_commit=corpus['commit'],frozen_corpus_tables=len(corpus['tables']),additional_tables=len(records)-len(corpus['tables']),matches=[x for x in records if x['equal']or x['reflection_equal']],records=records,scope='Root-preserving symbol-labelled deterministic transition graph isomorphism, also allowing global direction reflection. Finite corpus only; not a global novelty theorem.')
a.output.write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items()if k!='records'});assert not out['matches']
