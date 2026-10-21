from pathlib import Path
import sys,json,gzip,hashlib,argparse,io
P=Path(__file__).parent;sys.path.insert(0,str(P));import tm as b,source_language as s
ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('source',type=Path);ap.add_argument('output',type=Path);a=ap.parse_args();a.output.mkdir(exist_ok=True)
sha=lambda raw:hashlib.sha256(raw).hexdigest()
T=b.read_table(a.table.read_bytes());source=json.loads(a.source.read_text());graphs=s.graph_arithmetic(source)[0];assert graphs==s.graph_intervals(source)
# Fresh source execution from the precise abstract AX seed.
pc=25;regs=[1,0,2,0,0,0,0,0,0];source_trace=[]
for tick in range(177):
 before=regs.copy();oldpc=pc;effect,targets=graphs[pc]
 if effect[0]=='increment':regs[effect[1]]+=1;pc=targets[0]
 elif effect[0]=='decrement':r=effect[1];yes=regs[r]>0;regs[r]-=int(yes);pc=targets[int(yes)]
 else:assert effect[0]=='identity';pc=targets[0]
 source_trace.append({'step':tick,'ordinal':oldpc,'site':source[oldpc],'before':before,'next_ordinal':pc,'after':regs.copy()})
assert pc==58 and regs==[1,0,0,0,0,0,0,18,0]
address=source[pc][0];head=-2;physical=[None]*9
for i,j in enumerate((6,2,0,4,3,7,8,5,1)):physical[j]=regs[i]
expected={-3,62}|{head+i for i,bit in enumerate(address)if bit=='1'};pos=63
for value in physical+[0]*63:expected.update(range(pos+1,pos+value+2));pos+=value+2
assert len(expected)==100
# Locate that exact entire finite tape, rather than accepting a partial frame.
q=0;head=0;ones=set();trace=bytearray()
for tick in range(2000000):
 if q==84 and head==-2 and ones==expected:break
 read=int(head in ones);w,d,z=T[q,read];trace.extend((json.dumps([tick,q,head,read,w,d,z],separators=(',',':'))+'\n').encode())
 if w:ones.add(head)
 else:ones.discard(head)
 q=z;head+=d
 if q==254:raise AssertionError(('premature halt',tick+1,head))
else:raise AssertionError(('no whole-frame match',q,head,len(ones)))
steps=tick;print('FOUND',steps,'state',q,'head',head,'ones',len(ones),flush=True)
# Independently replay the saved delta against the literal table.
buf=io.BytesIO()
with gzip.GzipFile(fileobj=buf,mode='wb',filename='',mtime=0)as f:f.write(trace)
(a.output/'blank-delta.jsonl.gz').write_bytes(buf.getvalue());restored=gzip.decompress(buf.getvalue());assert restored==trace
qq=0;hh=0;oo=set()
for n,line in enumerate(restored.splitlines()):
 tick,oldq,oldh,r,w,d,z=json.loads(line);assert(tick,oldq,oldh,r)==(n,qq,hh,int(hh in oo));assert T[qq,r]==(w,d,z)
 if w:oo.add(hh)
 else:oo.discard(hh)
 qq=z;hh+=d
assert n+1==steps and(qq,hh,oo)==(84,-2,expected)
source_raw=(json.dumps(source_trace,separators=(',',':'))+'\n').encode();(a.output/'AX-prefix.json').write_bytes(source_raw)
report={'status':'EXACT_BLANK_FRAME_DELTA_AND_SOURCE_AX_PREFIX_PASS','binary_steps':steps,'dispatcher':q,'head':head,'header':62,'gap':0,'address':address,'source_ordinal':pc,'logical_registers':regs,'spares':[0]*63,'one_cells':sorted(ones),'source_AX_steps':177,'source_AX_entry':25,'source_AX_seed':[1,0,2,0,0,0,0,0,0],'table_sha256':sha(a.table.read_bytes()),'source_sha256':sha(a.source.read_bytes()),'delta_sha256':sha(trace),'AX_prefix_sha256':sha(source_raw),'delta_trace_replayed':True,'source_CFG_resolvers_agree':True}
(a.output/'bootstrap.json').write_text(json.dumps(report,indent=2)+'\n');print({k:v for k,v in report.items()if k not in('one_cells','spares')})
