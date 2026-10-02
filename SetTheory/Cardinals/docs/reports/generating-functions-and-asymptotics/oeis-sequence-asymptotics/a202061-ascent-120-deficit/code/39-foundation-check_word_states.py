from collections import Counter

def asc(w):return sum(a<b for a,b in zip(w,w[1:]))
def avoid(w):return not any(w[k]<w[i]<w[j] for i in range(len(w)) for j in range(i+1,len(w)) for k in range(j+1,len(w)))
def state(w):
 cutoff=max([0]+[w[i] for i in range(len(w)) for j in range(i+1,len(w)) if w[i]<w[j]])
 S=tuple(sorted(set(v-cutoff for v in w if v>=cutoff)))
 a=asc(w)-cutoff;l=w[-1]-cutoff
 assert S[0]==0 and a+1-max(S)>=1
 assert l==0 or (len(S)>1 and l==S[1])
 return a,l,S

def successors(st):
 a,l,S=st;out=Counter()
 for i in range(a+2):
  p=max([0]+[v for v in S if v<i])
  out[a+(l<i)-p,i-p,tuple(sorted(set(v-p for v in S if v>=p)|{i-p}))]+=1
 return out
words=[(0,)]
for n in range(1,10):
 nxt=[]
 for w in words:
  children=[w+(z,) for z in range(asc(w)+2) if avoid(w+(z,))]
  assert Counter(map(state,children))==successors(state(w)),w
  nxt.extend(children)
 print('length',n,'prefixes',len(words),'all literal-word state transitions PASS',flush=True)
 words=nxt
print('PASS direct length-10 count',len(words))
