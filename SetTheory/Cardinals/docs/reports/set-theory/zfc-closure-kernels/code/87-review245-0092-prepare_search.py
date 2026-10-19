import search_grammar as s
allwords=set(s.R)|set(s.OLD)|set(s.ATOM)|s.ROOTS
for R in [s.R,s.OLD]:allwords.update(x for cs in R.values()for x in cs)
allwords.update(z[1]for z in s.AST if z[0]=='W')
words=sorted(allwords,key=lambda w:(len(w),w));ids={w:i for i,w in enumerate(words)}
f=open(s.OUT/'search-input.txt','w');p=lambda *x:print(*x,file=f)
p(len(words))
for w in words:p(w,s.ALLOWED.get(w,3),s.ATOM.get(w,-1))
p(len(s.OLD))
for w,ab in s.OLD.items():p(ids[w],*(ids[x]for x in ab))
p(len(s.R))
for w,ab in s.R.items():p(ids[w],*(ids[x]for x in ab))
p(len(s.ROOTS),*(ids[w]for w in s.ROOTS))
p(len(s.locks))
for w,b,t in s.locks:p(ids[w],b,ids[t])
p(len(s.CON))
for q,b,bits,t in s.CON:p(ids[s.ROUTES[q,b]],bits,ids[t])
p(len(s.AST),s.root)
for z in s.AST:
 if z[0]=='L':p('L',0,0)
 elif z[0]=='W':p('W',ids[z[1]],0)
 else:p(*z)
f.close()
