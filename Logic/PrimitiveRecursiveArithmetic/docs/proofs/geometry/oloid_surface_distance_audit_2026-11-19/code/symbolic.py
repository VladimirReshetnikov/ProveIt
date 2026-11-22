"""Evaluate the compact h-formulas and the elementary P6--P9 route gap."""
from fractions import Fraction as Q
import csv
from pathlib import Path
import precise_distances as p

def coordinates(name):
    h,s,*_ = p.POINTS[name]
    d = 1+h*h
    z = p.interval(3-h*h).sqrt()
    x = 1-h*h
    if x > 0:
        alpha = p.atan(h*z/x)
    elif x < 0:
        alpha = p.PI-p.atan(h*z/(-x))
    else:
        alpha = p.PI/2
    u = 2*alpha + 2*h*z*(2-s*(3+h*h))/d
    v = p.log_positive(p.interval(d)) + p.interval((8*h*h+s*(9+3*h*h+2*h**4))/d)
    return (p.R3*u/9,p.R3*v/9)

def length(a,b):
    return sum((x-y).square() for x,y in zip(a,b)).sqrt()

def main():
    group = {'direct': (1,0), 'L': (-1,0), 'R': (-1,1),
             'LR': (1,-1), 'RL': (1,1)}
    count = 0
    rows = Path(__file__).resolve().parents[1]/'data'/'refined_distances.csv'
    for row in csv.DictReader(rows.open()):
        word = row['word']
        if word not in group:
            continue
        a = coordinates(row['from'])
        x,y = coordinates(row['to'])
        sign,k = group[word]
        result = length(a,(sign*x+2*k*p.W,y))
        p.require(Q(row['lower']) <= Q(result.lo,p.BASE) <= Q(result.hi,p.BASE)
                  <= Q(row['upper']), 'symbolic result outside reported interval')
        count += 1
    p.require(count==25,'incorrect number of elementary rows')
    a,b = coordinates('P6'),coordinates('P9')
    corner = (p.ZERO,p.R3)
    alternate = length(a,corner)+length(corner,b)
    gap = alternate - length(a,(-b[0],b[1]))
    print(count, 'elementary expressions verified.')
    print('B minimum:', *p.outward(alternate,45))
    print('B minus L:', *p.outward(gap,45))

if __name__=='__main__':
    main()
