"""Exact finest closed-atom vocabulary derived from the archived source AST."""
from functools import cache
from pathlib import Path
import heapq,json,string

class Domain:
 def __init__(self,package):
  self.package=Path(package)
  self.source=json.loads((self.package/'inputs/closed-sequence-grammar-next22.json').read_text())
  self.symbols=json.loads((self.package/'inputs/semantic-symbols.json').read_text())
  self.ast=self.source['ast_dag']
  self.atoms={c:self.finest(self.source['atoms'][name]['ast'])for c,name in self.symbols.items()}
  token_ids=sorted({i for w in self.atoms.values()for i in w})
  assert len(token_ids)==30 and len(self.atoms)==44
  self.token_encoding={i:string.ascii_letters[j]for j,i in enumerate(token_ids)}
  self.token_ast={c:i for i,c in self.token_encoding.items()}
  self.expansions={c:''.join(self.token_encoding[i]for i in w)for c,w in self.atoms.items()}
  self.fine_symbols={self.expansions[c]:name for c,name in self.symbols.items()}
  assert len(self.fine_symbols)==44
  self.disjoint_pairs={tuple(sorted((a,b)))for a in self.token_ast for b in self.token_ast if a!=b and not self.footprint(self.token_ast[a])[0]&self.footprint(self.token_ast[b])[0] and not self.footprint(self.token_ast[a])[1] and not self.footprint(self.token_ast[b])[1]}
 @cache
 def bounds(self,i):
  r=self.ast[i]
  if r[0]=='L':
   op,*a=r[1];return(1 if op=='dec'else a[0]if op=='brk'else 0,a[0]if op=='cont'else 0)
  a,b=self.bounds(r[1]),self.bounds(r[2]);return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)
 @cache
 def finest(self,i):
  r=self.ast[i]
  return self.finest(r[1])+self.finest(r[2])if r[0]=='N'and self.bounds(r[1])==self.bounds(r[2])==(0,0)else(i,)
 @cache
 def footprint(self,i):
  r=self.ast[i]
  if r[0]=='L':
   op,*a=r[1];return(1<<a[0]if op in('inc','dec')else 0,op=='halt')
  a,b=self.footprint(r[1]),self.footprint(r[2]);return a[0]|b[0],a[1]or b[1]
 def expand(self,w):return ''.join(self.expansions[c]for c in w)

def trace_normal(w,independence):
 """Lexicographically least linearization of the letter dependence DAG."""
 edges=[[]for _ in w];degree=[0]*len(w);last={}
 for i,c in enumerate(w):
  for d,j in last.items():
   if tuple(sorted((c,d)))not in independence:edges[j].append(i);degree[i]+=1
  last[c]=i
 ready=[(c,i)for i,c in enumerate(w)if degree[i]==0];heapq.heapify(ready);out=[]
 while ready:
  c,i=heapq.heappop(ready);out.append(c)
  for j in edges[i]:
   degree[j]-=1
   if degree[j]==0:heapq.heappush(ready,(w[j],j))
 assert len(out)==len(w)
 return ''.join(out)
