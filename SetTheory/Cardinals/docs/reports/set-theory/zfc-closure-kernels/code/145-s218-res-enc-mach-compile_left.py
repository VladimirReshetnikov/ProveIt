from pathlib import Path
import json,time,sys
sys.path.insert(0,str(Path(__file__).parent))
import compile_eq as c
# Return protocol for sources having no right-child decrement: restore the
# K220 zero-decrement and increment-return rows; the special state 302 is absent.
c.T[113,0]=(0,-1,40)
c.T[198,0]=(1,-1,198)
c.T[103,1]=(0,-1,162)
for bit in (0,1):del c.T[302,bit]
source=Path(c.__file__).read_text()
body=source[source.index('def compile(h):'):source.index("if __name__=='__main__':")]
body=body.replace("'CB':lambda a:(0,-1,302)","'CB':lambda a:(0,-1,40)")
exec(body,c.__dict__)
out=Path(__file__).parent/'output/equality_left';out.mkdir(parents=True,exist_ok=True)
results=[]
baseG={q:set(ns)for q,ns in c.G.items()}
for item in json.loads((Path(__file__).parent/'left_hits.json').read_text()):
 i=item['hit'];h=c.tup(item['tree']);name=f'left{i:02d}';start=time.monotonic()
 try:
  c.G={q:set(ns)for q,ns in baseG.items()};clones=[]
  for attempt in range(30):
   try:tree,tt=c.compile(h);break
   except ValueError as e:
    details=e.args[0]
    if not isinstance(details,tuple)or details[0]!='shared leaf context':raise
    q=details[1];pc=details[4][0];n=c.repl(c.TREE,c.OLD,h)
    for ch in pc[:-1]:n=n[int(ch)]
    c.G[q].remove(n);clones.append((q,pc[:-1]))
  else:raise ValueError('too many clone attempts')
  d=out/name;d.mkdir(parents=True,exist_ok=True)
  (d/'candidate.tm').write_bytes(c.b.table_bytes(tt));(d/'sites.json').write_bytes(c.s.compact(c.s.sites(tree)))
  r={'variant':name,'states':len(tt)//2,'metrics':c.s.metrics(tree),'seconds':time.monotonic()-start,'clones':clones}
 except Exception as e:r={'variant':name,'error':repr(e),'seconds':time.monotonic()-start,'clones':clones}
 results.append(r);print(json.dumps(r),flush=True);(out/'summary.json').write_text(json.dumps(results,indent=2))
