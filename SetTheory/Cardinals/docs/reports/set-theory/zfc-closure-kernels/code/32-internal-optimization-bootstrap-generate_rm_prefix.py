from pathlib import Path
import json
paths=json.loads(Path('paths.json').read_text());trie={}
for p,op in paths:
 n=trie
 for b in p:n=n.setdefault(b,{})
 n['op']=op

def inc(p):
 if '0'not in p:return '0'*len(p)
 j=p.rindex('0');return p[:j]+'1'+'0'*(len(p)-j-1)
def strip(p,b,k):
 while k>0 and p:
  if p[-1]==b:k-=1
  p=p[:-1]
 return p
R=[2,0,0,0,0,0,0,0,0];P='';phys=[2,4,3,7,6,8,0,1,5];entries=[];maxreg=0
with Path('rm_prefix100k.txt').open('w')as f:
 for step in range(100001):
  ps=P.rstrip('0');pr=[R[j]for j in phys]
  f.write(f'{step} {ps or "-"} '+','.join(map(str,pr))+'\n')
  n=trie;Q=''
  while 'op'not in n:
   bit=P[len(Q)]if len(Q)<len(P)else'0';Q+=bit;n=n[bit]
  k,*a=n['op'].split();r=int(a[0])if a else None
  if k=='CI':R[r]+=1;P=inc(Q)
  elif k=='CD':
   if R[r]:R[r]-=1;P=inc(Q)
   else:P=inc(strip(Q,'0',1))
  elif k=='CB':P=inc(strip(Q,'0',r))
  elif k=='CC':P=strip(Q,'1',r)
  else:raise RuntimeError(f'halt at{step}')
  maxreg=max(maxreg,max(R))
print('RM prefix100001configurations;maxregister',maxreg,'last',P,R)
