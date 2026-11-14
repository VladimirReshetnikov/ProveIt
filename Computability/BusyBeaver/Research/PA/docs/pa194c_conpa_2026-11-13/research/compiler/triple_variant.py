from pathlib import Path
import sys,itertools
P=Path(__file__).resolve().parents[2] / 'reference' / 'pa194';W=Path(__file__).resolve().parent
sys.path.insert(0,str(P/'construction'));import compiler as c
original=c.read_grammar(P/'construction/source/pa194.grammar.json');inc=('leaf','inc',1);dec=('leaf','dec',1)
def length(t):return length(t[0])+length(t[1]) if c.isnode(t) else 1
def word(t):return word(t[0])+word(t[1]) if c.isnode(t) else [t]
def join(a,b):return b if a is None else a if b is None else (a,b)
def sl(t,lo,hi):
 if lo==hi:return None
 if lo==0 and hi==length(t):return t
 n=length(t[0]);return join(sl(t[0],lo,min(hi,n)) if lo<n else None,sl(t[1],max(lo-n,0),hi-n) if hi>n else None)
def repl(t,lo,hi,new):
 if lo==0 and hi==length(t):return new
 n=length(t[0])
 if hi<=n:return (repl(t[0],lo,hi,new),t[1])
 if lo>=n:return (t[0],repl(t[1],lo-n,hi-n,new))
 return join(sl(t,0,lo),join(new,sl(t,hi,length(t))))
a=word(original);runs=[i for i in range(len(a)-2) if a[i:i+3]==[inc]*3]
assert not any(a[i:i+4]==[inc]*4 for i in range(len(a)-3))
print('triples:',runs)
mac=dict(c.MACROS);mac[dec]=41
records=[]
for mask in range(1<<len(runs)):
 t=original
 for j in reversed(range(len(runs))):
  if mask>>j&1:t=repl(t,runs[j],runs[j]+3,('node61',dec))
 ns=[];memo={}
 def go(t):
  if t in memo:return memo[t]
  if t in mac:v=(0,mac[t],-1,-1)
  elif t==c.BREAK:v=(0,-1,-1,-1)
  else:v=(1,go(t[0]),go(t[1]),0)
  q=len(ns);ns.append(v);memo[t]=q;return q
 rt=go(t);records += [f'{mask} {len(ns)} {rt}']+[' '.join(map(str,v)) for v in ns]
base=(W/'start194.txt').read_text().splitlines()[:135]
(W/'triple_inputs.txt').write_text('\n'.join(base+[str(1<<len(runs))]+records)+'\n')
l=(P/'search/inputs/leaf_attrs.txt').read_text().splitlines();l[0]='14';l.append('41 0 0 0 0 0');(W/'triple_attrs.txt').write_text('\n'.join(l)+'\n')
s=(W/'search_identity.cpp').read_text().replace('case -1:return','case 41:return "[\\\"leaf\\\",\\\"dec\\\",1]";case -1:return')
(W/'search_triple.cpp').write_text(s)
