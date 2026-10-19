"""Structured source PC operations and the fixed logical register permutation.

The functions are extracted unchanged from ProveIt's independent runtime helper.
Their mathematical meaning is defined in report/k228-transfer.tex.
"""
PHY=(6,2,0,4,3,7,8,5,1)

def inc(pc):
    n=len(pc);v=(int(pc,2) if pc else 0)+1
    return (format(v%2**n,'0'+str(n)+'b') if n else ''),int(v==2**n)

def strip(pc,bit,count):
    assert isinstance(count,int) and count>=0
    if count==0:return pc
    for i in range(len(pc)-1,-1,-1):
        if pc[i]==bit:
            count-=1
            if count==0:return pc[:i]
    return ''
