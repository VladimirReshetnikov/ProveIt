"""Exhaust a precisely bounded family of one/two SLP rotations; no random run claim."""
import search_grammar as s
import collections,json,time,itertools
T=time.monotonic();roots=set(json.load(open(s.OUT/'true_framework_roots.json')));groups=collections.defaultdict(list)
for q,b,bits,t in s.CON:groups[q,b].append((bits,t))

def rotations(R):
 for w,(a,b)in list(R.items()):
  for side in [0,1]:
   c=(a,b)[side]
   if c not in R:continue
   x,y=R[c]
   if side==0:new=y+b;ab=(x,new);newrule=(y,b)
   else:new=a+x;ab=(new,y);newrule=(a,x)
   pairs=[ab]+([]if new in R else[newrule])
   if any(len(c)==1 and not(s.ALLOWED[c]&(1<<i))for pair in pairs for i,c in enumerate(pair)):continue
   rr=dict(R);rr[w]=ab
   if new not in rr:rr[new]=newrule
   yield rr

def matches(R,w,cs):
 for bits,target in cs:
  z=w
  for b in bits:
   if z not in R:return False
   z=R[z][int(b)]
  if z!=target:return False
 return True

route_assignments=0

def assess(R):
 global route_assignments
 options=[]
 for qb,cs in groups.items():
  choices=[w for w in R if matches(R,w,cs)]
  if not choices:return None
  options.append(choices)
 possibilities=[];tested=set()
 for routes in itertools.product(*options):
  route_assignments+=1
  seen=set()
  def v(w):
   if len(w)==1 or w in seen:return
   seen.add(w)
   for c in R[w]:v(c)
  for w in roots|set(routes):v(w)
  key=frozenset(seen)
  if key in tested:continue
  tested.add(key)
  if len(seen)>128:continue
  rr={w:R[w]for w in seen};p=s.props(rr)
  possibilities.append((len(rr),p[1],p[2],rr,routes))
 return min(possibilities,key=lambda x:(x[1],x[0],x[2]))if possibilities else None

count=0;valid=0;minzero=999;mincount=999;done=set();level1=list(rotations(s.R));best=None
for R in itertools.chain(level1,(rr for r in level1 for rr in rotations(r))):
 count+=1
 key=tuple(sorted(R.items()))
 if key in done:continue
 done.add(key)
 a=assess(R)
 if a is None:continue
 valid+=1;minzero=min(minzero,a[1]);mincount=min(mincount,a[0])
 if a[1]<=5:
  best=a;print('ZERO5',a[:3],flush=True);break
report={'family':'At most two elementary binary-tree rotations of one shared grammar rule, introducing at most one helper per rotation; inherited rules otherwise unchanged. Bootstrap locks and bootstrap-only root obligations released. All combinations of existing compatible active route words are enumerated. Router-only synthesis not included.','raw_proposals':count,'route_assignments_checked':route_assignments,'distinct_rulemaps':len(done),'valid_with_at_most128_rules':valid,'minimum_zero_run':minzero,'minimum_rules':mincount,'found_zero5':best is not None,'seconds':time.monotonic()-T,'complete_enumeration':best is None,'scope':'A finite grammar neighborhood, not a global state-count or grammar lower bound.'}
(s.OUT/'surgical-zero5-results.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
if best:
 n,z,d,rr,routes=best;g=dict(s.G);g['rules_count']=n;g['properties']=list(s.props(rr));g['rules']=[[w,*ab]for w,ab in sorted(rr.items())];g['roots']=sorted(roots);g['routes']=[dict(source=q,read=b,word=w)for(q,b),w in zip(groups,routes)];(s.OUT/'surgical-zero5-candidate.json').write_text(json.dumps(g,indent=2)+'\n')
