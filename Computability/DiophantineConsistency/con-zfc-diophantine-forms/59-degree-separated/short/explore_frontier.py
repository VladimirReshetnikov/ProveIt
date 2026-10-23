import itertools

def parts(seq):
 if not seq: yield [];return
 first,*rest=seq
 for p in parts(rest):
  yield [[first]]+p
  for j in range(len(p)): yield p[:j]+[[first]+p[j]]+p[j+1:]
rows=[]
for t,g0,ga in itertools.product((0,1),repeat=3):
 # source61 ordinary, firstgap andauxgap eachaddone, T2 savesone
 deg={'N0':12 if g0 else 22,'N1':18,'Na':(23 if t else 22) if ga else(30 if t else 28),'Nk':7,'Nt':2}
 prefix=61-t+g0+ga
 for p in parts(list(deg)):
  # m unit groups plus separate zero strongresidual
  m=len(p);ops=prefix+(5-m)+(m+1)*2+m
  degree=2*max(22,*[sum(deg[x] for x in b) for b in p])
  rows.append((ops,degree,t,g0,ga,'sos',p))
 # include ordinary strong unit and plain product, or sumsq groups
 deg['Ns']=22
 prefix+=2
 rows.append((prefix+6,sum(deg.values()),t,g0,ga,'product',[list(deg)]))
 for p in parts(list(deg)):
  m=len(p);ops=prefix+6-m+3*m-1
  degree=2*max(sum(deg[x] for x in b) for b in p)
  rows.append((ops,degree,t,g0,ga,'unit_sos',p))
for row in sorted(rows):
 if not any(x[0]<=row[0] and x[1]<=row[1] and x[:2]!=row[:2] for x in rows): print(row)
