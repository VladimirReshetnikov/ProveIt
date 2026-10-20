from collections import deque
def blank_domain(table,start,radius):
 width=2*radius+1;mask=(1<<width)-1
 states={q for q,b in table}|{254};domain={q:set() for q in states}
 domain[start].add(0);todo=deque([(start,0)])
 def post(q,word):
  w,d,z=table[q,(word>>radius)&1]
  written=(word&~(1<<radius))|(w<<radius)
  low=written>>1 if d==1 else (written<<1)&mask
  return z,(low,low|(1<<(width-1) if d==1 else 1))
 while todo:
  q,word=todo.popleft()
  if q==254:continue
  z,words=post(q,word)
  for new in words:
   if new not in domain[z]:domain[z].add(new);todo.append((z,new))
 for q in states-{254}:
  for word in domain[q]:
   z,words=post(q,word)
   assert all(new in domain[z] for new in words)
 assert 0 in domain[start]
 return domain
