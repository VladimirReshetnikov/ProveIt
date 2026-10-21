"""Owned finite corroboration of the new all-natural credit proof.
No project module or received program is imported; input is only a numerical bound.
"""
import json
from math import isqrt
from pathlib import Path

def unpair(n):
    s = (isqrt(8*n+1)-1)//2
    y = n-s*(s+1)//2
    return s-y,y

def right(n):
    return unpair(n)[1]

def initial(n):
    tag,tail = unpair(n)
    if tag == 0:
        return 'S',-1,tail
    if tag == 1:
        return 'MP',0,right(tail)
    return 'AX',10,right(right(tail))

limit = 500000
balances = []
minima = []
lengths = []
words = []
B = 0
min_global = 0
for n in range(limit):
    kind,w,tail = initial(n)
    if tail:
        assert tail-1 < n
        b = w + balances[tail-1]
        m = min(0,w+minima[tail-1])
        length = 1+lengths[tail-1]
    else:
        b,m,length = w,min(0,w),1
    balances.append(b)
    minima.append(m)
    lengths.append(length)
    assert length <= n+1
    min_global = min(min_global,B+m)
    B += b
    assert B+n+1 >= 0
    if n < 1000:
        word = [kind] + (words[tail-1] if tail else [])
        words.append(word)
        count = 0
        lowest = 0
        for k in word:
            count += {'S':-1,'MP':0,'AX':10}[k]
            lowest = min(lowest,count)
        assert (count,lowest,len(word)) == (b,m,length)

whole = 0
for s in range(2,isqrt(2*limit)+1):
    lo,hi = s*(s+1)//2,(s+1)*(s+2)//2
    if hi > limit:
        break
    b,m = 0,0
    for n in range(lo,hi):
        m = min(m,b+minima[n])
        b += balances[n]
    assert m == 0
    assert b >= 7*s-9
    whole += 1

def finite_credit(N):
    s = (isqrt(8*N+1)-1)//2
    E = max(3,(s+1)*(s+2)//2)
    b,m = 0,0
    for n in range(N,E):
        m = min(m,b+minima[n])
        b += balances[n]
    return {'cutoff':N,'horizon':E,'required_credit':-m,'final_balance':b}

report = {
    'status':'PASS',
    'scope':'Finite independent recurrence corroboration only; the separate written induction proves all naturals.',
    'candidate_count':limit,
    'explicit_word_comparisons':len(words),
    'whole_diagonals_checked':whole,
    'minimum_global_command_prefix_balance':min_global,
    'first_candidate_words':[{'n':n,'word':words[n],'balance':balances[n],'minimum':minima[n]} for n in range(10)],
    'small_credits':[finite_credit(n) for n in range(30)],
    'startup':{'next_candidate':1,'theorem_prefix_length':10,'required_credit':finite_credit(1)['required_credit'],'minimum_remaining_protected_heads':10-finite_credit(1)['required_credit']}
}
Path(__file__).with_name('TRANSFER_CREDIT_CHECK.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('first_candidate_words','small_credits')},indent=2))
