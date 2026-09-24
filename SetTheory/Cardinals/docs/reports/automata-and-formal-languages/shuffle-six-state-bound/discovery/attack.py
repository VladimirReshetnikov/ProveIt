import sys, re, json, time, random
from native_z3 import solve

def fmt_or(a):
 return '(or '+ ' '.join(a) + ')' if a else 'false'

def predecessor(S,m,n,strict=True, timeout=30000, extra='', full_support=False):
 code=['(set-option :timeout %d)'%timeout,'(set-option :produce-models true)']
 for i in range(m): code+=['(declare-const f%d Int)'%i,'(assert (and (<= 0 f%d) (< f%d %d)))'%(i,i,m)]
 for j in range(n): code+=['(declare-const g%d Int)'%j,'(assert (and (<= 0 g%d) (< g%d %d)))'%(j,j,n)]
 for i in range(m):
  for j in range(n):
   code+=['(declare-const p%d_%d Bool)'%(i,j)]
   a=fmt_or(['(= f%d %d)'%(i,r) for r in range(m) if (r,j) in S])
   b=fmt_or(['(= g%d %d)'%(j,c) for c in range(n) if (i,c) in S])
   code+=['(assert (=> p%d_%d (and %s %s)))'%(i,j,a,b)]
 for r,c in sorted(S):
  a=['(and p%d_%d (= f%d %d))'%(i,c,i,r) for i in range(m)]
  a+=['(and p%d_%d (= g%d %d))'%(r,j,j,c) for j in range(n)]
  code+=['(assert %s)'%fmt_or(a)]
 code+=['(assert %s)'%fmt_or(['p0_%d'%j for j in range(n)]),'(assert %s)'%fmt_or(['p%d_0'%i for i in range(m)])]
 if full_support:
  for i in range(m): code+=['(assert %s)'%fmt_or(['p%d_%d'%(i,j) for j in range(n)])]
  for j in range(n): code+=['(assert %s)'%fmt_or(['p%d_%d'%(i,j) for i in range(m)])]
 if strict:
  code+=['(assert (< (+ %s) %d))'%(' '.join('(ite p%d_%d 1 0)'%(i,j) for i in range(m) for j in range(n)),len(S))]
 if extra: code+=[extra]
 code+=['(check-sat)']
 variables=['f%d'%i for i in range(m)]+['g%d'%j for j in range(n)]+['p%d_%d'%(i,j) for i in range(m) for j in range(n)]
 text='\n'.join(code)
 output=solve(text, '(get-value (%s))'%' '.join(variables))
 status=output.split()[0]
 if status!='sat': return {'status':status}
 pairs=dict(re.findall(r'\((\w+)\s+(\w+)\)',output))
 f=[int(pairs['f%d'%i]) for i in range(m)];g=[int(pairs['g%d'%j]) for j in range(n)]
 P={(i,j) for i in range(m) for j in range(n) if pairs['p%d_%d'%(i,j)]=='true'}
 image={(f[i],j) for i,j in P}|{(i,g[j]) for i,j in P}
 assert image==S
 assert any(i==0 for i,j in P) and any(j==0 for i,j in P)
 assert not strict or len(P)<len(S)
 return {'status':'sat','f':f,'g':g,'P':sorted(P)}

if __name__=='__main__':
 for n in [6,7,8,9,10]:
  S={(i,(i+d)%n) for i in range(n) for d in [0,1,3]}
  start=time.time(); r=predecessor(S,n,n)
  print(n,len(S),r,'time',time.time()-start,flush=True)
