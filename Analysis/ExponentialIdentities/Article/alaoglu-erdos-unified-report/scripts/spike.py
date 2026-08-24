from mpmath import mp, mpf, log, sqrt
mp.dps = 50
exec(open('greedy.py').read().split('a = log(2)')[0])
a=log(2); b=log(3); target=log(6)/2
def gE(E):
    q,Si,Sj = stats(E)
    F = mpf(2)/3*sqrt(2*a*b*q) - (Si*a+Sj*b)/q
    return (target-F)*E, F
# scan for extremes of gap*E
import sys
best=None; worst=None
vals=[]
for E in list(range(300,3000,7))+list(range(15000,16200,13))+list(range(24000,25600,13))+[320,640,1280,2560,5120,10240]:
    g,F = gE(E)
    vals.append((float(g),E))
vals.sort()
print("min gap*E:", vals[:6])
print("max gap*E:", vals[-6:])
