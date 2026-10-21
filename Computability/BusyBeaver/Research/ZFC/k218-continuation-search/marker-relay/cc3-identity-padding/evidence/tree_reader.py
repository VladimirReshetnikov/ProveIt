from functools import cache
leaf=lambda t:isinstance(t[0],str)
@cache
def flat(t):return (t,) if leaf(t) else flat(t[0])+flat(t[1])
def serial(ts):
 ans=ts[-1]
 for t in reversed(ts[:-1]):ans=(t,ans)
 return ans
@cache
def boundary(t):
 if leaf(t):
  op,a=t;return (1,0,False) if op=='CD' else (a,0,False) if op=='CB' else (0,a,False) if op=='CC' else (0,0,op=='CH')
 a,b=boundary(t[0]),boundary(t[1]);return max(a[0]-1,0,b[0]),max(a[1],b[1]-1,0),a[2] or b[2]
def rows(t,p=''):
 if leaf(t):return [[p,*t]]
 return rows(t[0],p+'0')+rows(t[1],p+'1')
def parse(rr):
 lookup={p:(op,a)for p,op,a in rr}
 def go(p):return lookup[p] if p in lookup else (go(p+'0'),go(p+'1'))
 t=go('');assert rows(t)==rr;return t
# Independent recursive subtree exits, using only ordinal spans and ancestor edges.
def cfg(t):
 rr=rows(t);ids={p:i for i,(p,_,_)in enumerate(rr)};spans={}
 def spans_at(p):
  if p in ids:v=(ids[p],ids[p]+1)
  else:
   l,r=spans_at(p+'0'),spans_at(p+'1');assert l[1]==r[0];v=(l[0],r[1])
  spans[p]=v;return v
 spans_at('')
 def dest(p,bit,k):
  ancestors=[p[:i] for i,b in enumerate(p) if b==bit]
  if len(ancestors)<k:return 0
  lo,hi=spans[ancestors[-k]];return lo if bit=='1' else hi%len(rr)
 gg=[]
 for k,(p,op,a)in enumerate(rr):
  aft=(k+1)%len(rr)
  gg.append([['increment',a],[aft]] if op=='CI' else [['decrement',a],[dest(p,'0',1),aft]] if op=='CD' else [['identity'],[dest(p,'0',a)]] if op=='CB' else [['identity'],[dest(p,'1',a)]] if op=='CC' else [['halt'],[]])
 return gg
