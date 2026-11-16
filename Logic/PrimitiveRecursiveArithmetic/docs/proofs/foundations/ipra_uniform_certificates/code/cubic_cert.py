"""Exact rational reference evaluator for y^3+y=x, x in [0,1].
This is executable evidence only, not an object-theory proof.
"""
from fractions import Fraction as Q

def clip(x): return min(Q(1), max(Q(0), x))
def p(x,y): return y*y*y+y-x

def bracket(x,n):
    x=clip(x)
    lo,hi=Q(0),Q(1)
    for _ in range(n):
        mid=(lo+hi)/2
        if p(x,mid)<=0: lo=mid
        else: hi=mid
        assert p(x,lo)<=0<=p(x,hi)
    assert hi-lo==Q(1,2**n)
    return lo,hi

def output_from_name(name,k):
    """name(j) approximates x to 2^-j, and target x in [0,1]."""
    j=k+3
    lo,hi=bracket(name(j),j)
    return (lo+hi)/2

def run():
    for den in (1,2,3,5,8,17):
        for num in range(den+1):
            x=Q(num,den)
            for k in range(9):
                a,b=bracket(x,k+3)
                y=(a+b)/2
                assert abs(p(x,y))<=Q(2,2**(k+3)) # derivative <= 4, midpoint error <= 2^-(k+4)
                # Approximate x with any legal error, check bracket root enclosure and total bound.
                for direction in (-1,0,1):
                    r=x+direction*Q(1,2**(k+3))
                    z=output_from_name(lambda j, r=r, x=x: x+direction*Q(1,2**j),k)
                    l,u=bracket(x,k+8)
                    assert z-u<Q(1,2**k) and l-z<Q(1,2**k)
    print('PASS: exact rational cubic certificates (all tests)')
if __name__=='__main__': run()
