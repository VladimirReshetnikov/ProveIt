from pathlib import Path
import subprocess,json,itertools,heapq,time,hashlib,sys
P=Path(__file__).resolve().parent
def read(p):
 rows={}
 for ln in Path(p).read_text().splitlines():
  if not ln or ln.startswith('#'):continue
  q,b,w,d,n=ln.split();rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
 return rows
def text(rows):return ''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {n}\n'for(q,b),(w,d,n)in sorted(rows.items()))
def key(rows):return hashlib.sha256(text(rows).encode()).hexdigest()
initial=read(sys.argv[1]);prefix=P/sys.argv[2];limit=int(sys.argv[3])if len(sys.argv)>3 else 10000
queue=[(len(initial)//2,0,initial,[])];seen={key(initial)};i=0;count=0;best=len(initial)//2;start=time.monotonic();hist={};examples={}
while queue and count<limit:
 n,id,rows,path=heapq.heappop(queue);count+=1;hist[n]=hist.get(n,0)+1
 if n<best:best=n;print('BEST',n,'expanded',count,'seen',len(seen),'elapsed',time.monotonic()-start,flush=True);(prefix.with_suffix('.best.tm')).write_text(text(rows));prefix.with_suffix('.best.path.json').write_text(json.dumps(path,indent=2))
 if n<=193:break
 tmp=prefix.with_suffix('.input.tm');tmp.write_text(text(rows))
 proc=subprocess.run([str(P/'action_merge_all'),str(tmp),'5','300'],capture_output=True,text=True);assert proc.returncode==0,proc.stderr
 for line in proc.stdout.splitlines():
  op=json.loads(line);a,b=op['remove'],op['keep']
  for acts in itertools.product(*op['choices']):
   child={}
   for(q,bit),old in rows.items():
    if q==a:continue
    w,d,target=acts[bit]if q==b else old
    child[q,bit]=(w,d,b if target==a else target)
   h=key(child)
   if h in seen:continue
   seen.add(h);i+=1;step={'remove':a,'keep':b,'actions':acts}
   heapq.heappush(queue,(len(child)//2,i,child,path+[step]))
 if count%100==0:print('EXPANDED',count,'queue',len(queue),'best',best,'time',time.monotonic()-start,flush=True)
receipt={'initial_states':len(initial)//2,'expanded':count,'seen':len(seen),'queue_remaining':len(queue),'best':best,'elapsed':time.monotonic()-start,'histogram':hist,'context_radius':5,'max_local_steps':300,'max_nodes':limit}
prefix.with_suffix('.receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt),flush=True)
