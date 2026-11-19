"""Regenerate the printed distance, rationalized angle, and contact tables."""
import csv
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path
from math import isqrt
from geometry import POINTS
getcontext().prec=80
data=Path(__file__).resolve().parents[1]/'data'
rows=list(csv.DictReader((data/'refined_distances.csv').open()))
def numbers(row):
    lo,hi=map(Decimal,(row['lower'],row['upper']))
    assert f'{lo:.15f}'==f'{hi:.15f}'
    w=row['word']
    w=r'\textendash' if w=='direct' else w
    return f"{row['from'][1:]},{row['to'][1:]} & {lo:.15f} & "+r'\textsf{'+w+'}'
with (data/'lengths.tex').open('w') as out:
    for i in range(23):
        right=numbers(rows[i+23]) if i+23 <len(rows) else ' & & '
        print(numbers(rows[i])+' & '+right+r' \\',file=out)
def tex(q):
    q=Fraction(q)
    return str(q.numerator) if q.denominator==1 else f'{q.numerator}/{q.denominator}'
def surd(n):
    divisor=next(i for i in range(isqrt(n),0,-1) if n%(i*i)==0)
    return divisor,n//(divisor*divisor)
with (data/'constants.tex').open('w') as out:
    for i,(h,s,*_) in enumerate(POINTS.values(),1):
        d=1+h*h
        den=h.denominator
        k,rad=surd(3*den*den-h.numerator*h.numerator)
        factor=Fraction(k,den)
        def times_root(q):
            n=q.numerator
            front= ('-' if n<0 else '') + (str(abs(n)) if abs(n)!=1 else '')
            return front+rf'\sqrt{{{rad}}}'+('/'+str(q.denominator) if q.denominator!=1 else '')
        tan=times_root(h*factor/(1-h*h)) if h!=1 else r'\infty'
        m=times_root(2*h*factor*(2-s*(3+h*h))/d)
        n=(8*h*h+s*(9+3*h*h+2*h**4))/d
        print(f'{i} & ${tex(d)}$ & ${tan}$ & ${m}$ & ${tex(n)}$'+r' \\',file=out)
