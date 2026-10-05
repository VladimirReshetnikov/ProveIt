"""Fresh finite Fourier evidence for the new sine-coordinate lift."""
from fractions import Fraction as F
from pathlib import Path
import argparse,hashlib,json

def require(c,m):
    if not c:raise ValueError(m)
def coefficients(M):
    n=len(M);C=[[0]*n for _ in range(n)]
    for k in reversed(range(n)):
        for m in range(n):
            C[k][m]=M[k][m]+(C[k+1][n-1-m] if k+1<n else 0)
    return C
def mask(C,q):
    n=len(C);b=n+1;a={0:F(1)}
    for k,row in enumerate(C,1):
        for m,v in enumerate(row,1):
            if v:
                j=b*k-m;require(j not in a and -j not in a,'collision')
                a[j]=a[-j]=F(v,q)
    return a
def fourier_image(a,b,v):
    out={}
    for n,c in v.items():
        for j,d in a.items():
            if (n+j)%b==0:
                k=(n+j)//b;out[k]=out.get(k,F(0))+c*d
    return {k:v for k,v in out.items() if v}
def sine(v):
    return {sgn*(m+1):sgn*F(c) for m,c in enumerate(v) if c for sgn in [-1,1]}
def mv(M,v):return [sum(x*y for x,y in zip(row,v)) for row in M]
def run():
    cases=[];basis=0;products=0
    for n in range(1,8):
        matrices=[[[0]*n for _ in range(n)],
                  [[int(k==m) for m in range(n)] for k in range(n)],
                  [[(2*k+3*m+n)%9-4 for m in range(n)] for k in range(n)],
                  [[int(k==n-1 and m==0) for m in range(n)] for k in range(n)]]
        cs=[coefficients(M) for M in matrices]
        sums=[sum(abs(x) for row in C for x in row) for C in cs]
        q=2*max(sums)+1;b=n+1;degree=n*b-1
        aa=[mask(C,q) for C in cs]
        for M,C,a in zip(matrices,cs,aa):
            require(all(j==0 or j%b for j in a),'Markov normalization')
            require(max(map(abs,a))<=degree and degree//(b-1)==n,'degree/core')
            require(1-sum(abs(c) for j,c in a.items() if j)>=F(1,q),'positive margin')
            require(sum(abs(x) for row in C for x in row)<=n*sum(abs(x) for row in M for x in row),'triangular size bound')
            for m in range(n):
                v=[int(k==m) for k in range(n)]
                require(fourier_image(a,b,sine(v))==sine([x/q for x in mv(M,[F(x) for x in v])]),'sine image')
                basis+=1
            cases.append({'dimension':n,'matrix':M,'lift_coefficients':C,'q':q,'dilation':b,'degree_bound':degree,'fourier_mask':[[j,str(c)] for j,c in sorted(a.items())]})
        for i,M in enumerate(matrices):
            for j,N in enumerate(matrices):
                for m in range(n):
                    v=[F(int(k==m)) for k in range(n)]
                    image=fourier_image(aa[j],b,fourier_image(aa[i],b,sine(v)))
                    require(image==sine([x/(q*q) for x in mv(N,mv(M,v))]),'word order and scale')
                    products+=1
        # Wholly zero families use q=1, separate from zero family members above.
        require(mask(coefficients(matrices[0]),1)=={0:F(1)},'zero family')
    # Two homogeneous counter branch matrices with the improved exact scale q=5.
    special=[]
    for M in [[[1,0],[0,1]],[[1,-1],[0,1]]]:
        C=coefficients(M);a=mask(C,5)
        for m in range(2):
            v=[F(int(k==m)) for k in range(2)]
            require(fourier_image(a,3,sine(v))==sine([x/5 for x in mv(M,v)]),'counter matrix')
        special.append({'matrix':M,'C':C,'q':5,'b':3,'mask':[[j,str(c)] for j,c in sorted(a.items())]})
    # Independent one-variable coefficients for q+2 sum C cos(j theta), t=cos theta.
    # Identity uses C at j=2,4; decrement adds coefficient -1 at j=1.
    identity=[3,0,-8,0,16]
    decrement=[3,-2,-8,0,16]
    square=[1,0,-8,0,16]  # (4t^2-1)^2
    require(identity==[square[i]+(2 if i==0 else 0) for i in range(5)],'identity positivity decomposition')
    require(decrement==[square[i]+(2 if i==0 else -2 if i==1 else 0) for i in range(5)],'decrement positivity decomposition')
    t=F(3,5)
    q4_value=sum(c*t**i for i,c in enumerate(decrement))-1
    require(q4_value==F(-4,625),'q4 strict counterexample')
    return {'schema':'markov-sine-lift-finite-evidence-v1','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'cases':cases,'basis_images':basis,'two_step_images':products,'all_zero_dimensions':list(range(1,8)),'counter_example':special,'q5_chebyshev_coefficients':{'identity':identity,'decrement':decrement},'q4_decrement_at_three_fifths':str(q4_value),'scope':'Fresh finite Fourier checks only; all-size/sharpness/positivity proofs are in the note. No saved source/helper execution or universal compiler claim.'}

if __name__=='__main__':
    ap=argparse.ArgumentParser();g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);args=ap.parse_args()
    result=run();raw=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
    if args.output:
        with args.output.open('xb') as f:f.write(raw)
    else:require(args.expect.read_bytes()==raw,'exact receipt')
    print('PASS',len(result['cases']),'masks',result['basis_images'],'basis images',result['two_step_images'],'two-step images; exact q5 counter masks')
