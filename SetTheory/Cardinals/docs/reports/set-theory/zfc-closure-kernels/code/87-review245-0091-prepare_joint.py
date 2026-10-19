import search_grammar as s
import collections
text=(s.OUT/'search-input.txt').read_text().splitlines();i=0;n=int(text[i]);i+=n+1;words=[l.split()[0]for l in text[1:n+1]];ids={w:i for i,w in enumerate(words)}
n=int(text[i]);i+=n+1;n=int(text[i]);i+=n+1
prefix=text[:i];oldroots=text[i];i+=1;n=int(text[i]);locks=text[i:i+n+1];i+=n+1;n=int(text[i]);i+=n+1;ast=text[i:]
groups=collections.defaultdict(list)
for q,b,bits,t in s.CON:groups[q,b].append((bits,t))
f=open(s.OUT/'joint-input.txt','w');p=lambda *x:print(*x,file=f)
for l in prefix:p(l)
p(len(s.G['roots']),*(ids[w]for w in s.G['roots']))
for l in locks:p(l)
p(len(groups))
for qb,cs in groups.items():
 p(ids[s.ROUTES[qb]],len(cs))
 for bits,t in cs:p(bits,ids[t])
for l in ast:p(l)
