"""Corroborate a hypothetical parser, not the rejected scratch-biased table."""
from math import isqrt
from functools import cache
import json
from pathlib import Path
P=lambda a,b:(a+b)*(a+b+1)//2+b
def un(n):
 s=(isqrt(8*n+1)-1)//2;y=n-s*(s+1)//2;return s-y,y
f=lambda n:un(n)[1]
@cache
def word(n):
 a,y=un(n)
 if a==0:return ('S',)+(word(y-1)if y else())
 r=f(y)if a==1 else f(f(y))
 return ('M'if a==1 else'A',)+(word(r)if r else())
wt={'S':-1,'M':0,'A':10}
@cache
def summary(n):
 w=word(n);b=m=0
 for c in w:b+=wt[c];m=min(m,b)
 return b,-m,int(w[-1]!='S')
# recurrence uses current incoming bias in increment BEFORE execution of word n.
n=1;incoming=1;balance=0;minimum=0;records=[]
while n<15:
 w=word(n);b,d,outgoing=summary(n)
 minimum=min(minimum,balance-d);balance+=b
 records.append({'n':n,'incoming':incoming,'word':w,'balance':balance,'minimum':minimum,'outgoing':outgoing,'next':n+1+incoming})
 n,incoming=n+1+incoming,outgoing
print(records,'next',n,incoming)
next_candidate=n
N=500000
Q=0;worst=0;bad=[];qmax=[]
for n in range(N):
 b,d,B=summary(n);q=2**d;Q+=q
 if q>n+2 or Q>4*(n+1):bad.append((n,d,Q,q))
 if d>worst:worst=d;qmax.append([n,d])
print('QBOUND',bad[:5],'worst',qmax,'sum',Q)
res={'status':'hypothetical intended parser only; archived scratch-biased table halts',
     'small_hypothetical_schedule':records,'next':next_candidate,'checks':N,'q_bound_pass':not bad,'new_max_debts':qmax,'Q':Q}
Path(__file__).with_name('biased_credit_result.json').write_text(json.dumps(res,indent=2)+'\n')
