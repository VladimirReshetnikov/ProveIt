import search_grammar as s
import functools

def details(R):
 bad=[]
 @functools.lru_cache(None)
 def a(i):
  z=s.AST[i]
  if z[0]=='L':return 0,0,0
  if z[0]=='W':return w(z[1])
  ans=join(a(int(z[1])),a(int(z[2])))
  if ans[0]>5:bad.append(('ast',i,ans))
  return ans
 @functools.lru_cache(None)
 def w(t):
  if len(t)==1:return a(s.ATOM[t])
  x,y=R.get(t,s.OLD.get(t));ans=join(w(x),w(y))
  if ans[0]>5:bad.append(('word',t,ans))
  return ans
 def join(x,y):return 1+x[0],max(1+x[0],x[1],y[1]),1+max(x[2],y[2])
 print(a(s.root));return bad
if __name__=='__main__':
 print('BASE',details(s.R))
 R=dict(s.R);R['eijkKCqkjGeU']=('eijkKCqkjG','eU');R['eU']=('e','U');del R['eijkKCqkjGe']
 print('SURGICAL',details(R))
