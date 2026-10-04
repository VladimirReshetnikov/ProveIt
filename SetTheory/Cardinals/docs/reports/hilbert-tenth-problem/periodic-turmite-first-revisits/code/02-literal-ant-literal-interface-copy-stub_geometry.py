"""Own exact closed integer-strip geometry; no generator imports."""
D=((0,-1),(1,0),(0,1),(-1,0))
def rotate(p,k):
 x,y=p
 for _ in range(k%4):x,y=-y,x
 return x,y
def corridor(state,incoming):
 x,y,h=state;d=D[h];v=rotate((0,-1),(h-1)%4)
 start=(x-d[0],y-d[1])if incoming else(x,y)
 direction=(-d[0],-d[1])if incoming else d;ans=[]
 for i in range(2):
  low=min(start[i],start[i]+v[i]);high=max(start[i],start[i]+v[i])
  if direction[i]<0:low=float('-inf')
  if direction[i]>0:high=float('inf')
  ans.append((low,high))
 return ans
def intersects(a,b):return all(max(x[0],y[0])<=min(x[1],y[1])for x,y in zip(a,b))
