"""Generate rational candidate boxes. mpmath is used ONLY to propose boxes.
Run verify_global.py to turn these untrusted proposals into certificates.
"""
from pathlib import Path
from fractions import Fraction as F
import json
import mpmath as mp

ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=65
D=10**44
logs={n:mp.log(n) for n in (2,3,4,5)}
def rational(x):return str(x.numerator)+'/'+str(x.denominator)
def approximate_root(b):
    if b==1:return mp.mpf(1)
    b=mp.mpf(b.numerator)/b.denominator
    U=1+mp.exp(-b*logs[2]);V=U+mp.exp(-b*logs[3]);W=V+mp.exp(-b*logs[4])
    l25=logs[5]-logs[2];l827=3*(logs[3]-logs[2])
    def f(a):return U*V*mp.exp(-a*logs[3])-W*mp.exp(-a*l25)/2-U**3*mp.exp(-a*l827)/2
    def df(a):return -logs[3]*U*V*mp.exp(-a*logs[3])+l25*W*mp.exp(-a*l25)/2+l827*U**3*mp.exp(-a*l827)/2
    guess=1+(1-b)*(mp.mpf('.570')+mp.mpf('.123')*(1-b))
    return mp.findroot(f,guess,df=df,solver='newton',tol=mp.mpf('1e-60'),maxsteps=30)

def main():
    cells=[];positions=set()
    for kind,n,start,length in [('increasing',2048,F(0),F(9,10)),('concave',256,F(9,10),F(1,10))]:
        for j in range(n):
            lo=start+length*j/n;hi=start+length*(j+1)/n;mid=(lo+hi)/2
            cells.append({'kind':kind,'lo':rational(lo),'hi':rational(hi),'mid':rational(mid)})
            positions.update((lo,hi,mid))
    roots={}
    for j,b in enumerate(sorted(positions)):
        v=approximate_root(b);k=int(mp.floor(v*D))
        roots[rational(b)]={'lo':rational(F(k-4,D)),'hi':rational(F(k+5,D))}
        if j%512==0:print('proposed root',j,'of',len(positions),flush=True)
    doc={'description':'Untrusted rational graph-cover proposals; independently verify all signs.',
         'cells':cells,'roots':roots,'precision_digits_for_proposals':65}
    out=ROOT/'certificates'/'global_mesh.json';out.write_text(json.dumps(doc,indent=2)+'\n')
    print('wrote',out,'with',len(cells),'cells and',len(roots),'root boxes',flush=True)
if __name__=='__main__':main()
