#!/usr/bin/env python3
"""Read-only rooted/reflection table census against an exact frozen corpus."""
import argparse,hashlib,json,os,pathlib,sys
if not __debug__ or sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):
 raise RuntimeError('Assertions must be enabled; clear PYTHONOPTIMIZE and do not use -O.')
def sha(raw): return hashlib.sha256(raw).hexdigest()
def graph(raw,reflect=False):
 rows={};start=None
 for line in raw.decode('ascii').splitlines():
  if line.startswith('#! start '): start=int(line.split()[-1]);continue
  if not line or line.startswith('#'): continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
  assert b in(0,1)and w in(0,1)and d in('L','R')and(q,b)not in rows
  rows[q,b]=(w,d,z)
 states={q for q,b in rows};assert set(rows)=={(q,b)for q in states for b in(0,1)}and start in states
 halts={z for w,d,z in rows.values()}-states;assert len(halts)==1;halt=halts.pop()
 order=[start];index={start:0};out=[]
 for q in order:
  for b in(0,1):
   w,d,z=rows[q,b]
   if z!=halt and z not in index:index[z]=len(index);order.append(z)
   if reflect:d='L' if d=='R' else 'R'
   out.append((w,d,-1 if z==halt else index[z]))
 return out,len(states),len(order)
def main():
 p=argparse.ArgumentParser();p.add_argument('candidate',type=pathlib.Path);p.add_argument('--corpus',type=pathlib.Path,default=pathlib.Path(__file__).resolve().parent/'comparison-corpus');p.add_argument('--out',type=pathlib.Path);a=p.parse_args()
 manifest=json.loads((a.corpus/'manifest.json').read_text());raw=a.candidate.read_bytes();g,n,r=graph(raw);assert n==r==215
 matches=[];graphs=set();count=0
 for item in manifest['tables']:
  b=(a.corpus/item['file']).read_bytes();assert sha(b)==item['sha256'];other,ns,reach=graph(b);assert ns==215
  canon=sha(json.dumps(other,separators=(',',':')).encode());assert canon==item['graph_sha256'];graphs.add(canon);count+=1
  if other==g or graph(b,True)[0]==g:matches.append(item)
 out={'status':'EXACT_ROOTED_GRAPH_DISTINCTNESS_PASS'if not matches else 'ROOTED_OR_REFLECTION_MATCH','candidate_sha256':sha(raw),'candidate_states':n,'candidate_graph_reachable':r,'candidate_graph_sha256':sha(json.dumps(g,separators=(',',':')).encode()),'corpus_manifest_sha256':sha((a.corpus/'manifest.json').read_bytes()),'comparison_tables':count,'comparison_rooted_graphs':len(graphs),'repository_commit':manifest['repository_commit'],'matches':matches,'scope':'Exact finite pinned-corpus rooted graph comparison with write/read/direction labels, arbitrary state renaming and global tape reflection. Does not establish semantic inequivalence or universal novelty.'}
 if a.out:a.out.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2))
 if matches:sys.exit(1)
if __name__=='__main__':main()
