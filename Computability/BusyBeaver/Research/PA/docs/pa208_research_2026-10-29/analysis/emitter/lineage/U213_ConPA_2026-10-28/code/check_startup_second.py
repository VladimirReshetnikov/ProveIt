#!/usr/bin/env python3
"""Independent finite blank/startup and source-prefix comparison for U213.

No synthesis, runtime-checker, source-builder, or received-project code imports.
The complete binary tape is a finite support set, with zero exterior.
"""
from pathlib import Path
import argparse,hashlib,json

def require(ok,why):
 if not ok:raise ValueError(why)
def digest(raw):return hashlib.sha256(raw).hexdigest()
def source_graph(rows):
 bounds={}
 for i,(p,o,a)in enumerate(rows):
  for j in range(len(p)+1):
   k=p[:j]
   if k not in bounds:bounds[k]=[i,i+1]
   else:bounds[k][1]=i+1
 graph=[]
 for i,(p,o,a)in enumerate(rows):
  if o=='CI':dest=[i+1]
  elif o=='CH':dest=[]
  else:
   b='1'if o=='CC'else'0';n=a if o!='CD'else 1
   places=[j for j,x in enumerate(p)if x==b];require(len(places)>=n,'Source escape')
   branch=bounds[p[:places[-n]]][0 if o=='CC'else 1]%len(rows)
   dest=[branch,i+1]if o=='CD'else[branch]
  graph.append((o,a,dest))
 return graph
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--table',type=Path,required=True);p.add_argument('--source',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 raw=a.table.read_bytes();table={};starts=[]
 for line in raw.decode('ascii').splitlines():
  if line.startswith('#! start '):starts.append(int(line.split()[-1]))
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));require(b in(0,1)and w in(0,1)and d in('L','R'),'Bad row');require((q,b)not in table,'Duplicate row');table[q,b]=(w,1 if d=='R'else-1,z)
 require(starts==[0],'Start label');states={q for q,b in table};require(len(states)==213 and len(table)==426,'State count');require({z for w,d,z in table.values()}-states=={254},'External target')
 source_raw=a.source.read_bytes();require(digest(source_raw)=='7b6539dc67b66ff73f22554018d7af5985d85574460a73fea5f025103c523d00','Source hash')
 rows=json.loads(source_raw);pcword='001100110101010';require(rows[136][0]==pcword,'Matched source address')
 logical=[1,0,13,0,0,1,0,0,1];physical=[None]*9
 for i,j in enumerate((6,2,0,4,3,7,8,5,1)):physical[j]=logical[i]
 head=-2;expected={head-1,head+56}|{head+i for i,b in enumerate(pcword)if b=='1'};place=head+57
 for v in physical+[1]*43:
  require(place not in expected,'Expected register separator conflict');expected.update(range(place+1,place+v+2));place+=v+2
 q=h=0;ones=set();seen=set();trace_hash=hashlib.sha256()
 for i in range(48140):
  b=int(h in ones);require((q,b)in table,'Premature halt');w,d,z=table[q,b];seen.add((q,b));trace_hash.update((f'{i} {q} {h} {b} {w} {d} {z}\n').encode('ascii'))
  if w:ones.add(h)
  else:ones.discard(h)
  q=z;h+=d
 require((q,h,ones)==(84,head,expected),'Complete blank frame differs')
 graph=source_graph(rows);ordinal=106;registers=[1,0,4,0,0,1,0,0,1];source_trace=[]
 for i in range(141):
  o,r,dest=graph[ordinal];before=registers.copy();old=ordinal
  if o=='CI':registers[r]+=1;ordinal=dest[0]
  elif o=='CD':nonzero=registers[r]>0;registers[r]-=int(nonzero);ordinal=dest[int(nonzero)]
  elif o in('CB','CC'):ordinal=dest[0]
  else:raise ValueError('Unexpected source halt')
  source_trace.append([old,before,ordinal,registers.copy()])
 require(ordinal==136 and registers==logical,'Source prefix does not match blank frame')
 result={'status':'INDEPENDENT_U213_BLANK_AND_SOURCE_PREFIX_PASS','native_table_sha256':digest(raw),'source_sha256':digest(source_raw),'states':len(states),'rows':len(table),'blank_steps':48140,'native_state':q,'head':h,'header_distance':56,'gap':0,'source_ordinal':ordinal,'source_address':pcword,'logical_registers':logical,'spares':[1]*43,'one_cells':sorted(ones),'whole_tape_support_size':len(ones),'blank_trace_text_sha256':trace_hash.hexdigest(),'used_rows':sorted(seen),'source_seed_ordinal':106,'source_seed_registers':[1,0,4,0,0,1,0,0,1],'source_prefix_steps':141,'source_trace_sha256':digest((json.dumps(source_trace,separators=(',',':'))+'\n').encode('ascii')),'scope':'Independent finite exact binary and source replay only; unbounded simulation and safe suffix are separate mathematical obligations.'}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in('used_rows','one_cells','spares')},indent=2))
if __name__=='__main__':main()
