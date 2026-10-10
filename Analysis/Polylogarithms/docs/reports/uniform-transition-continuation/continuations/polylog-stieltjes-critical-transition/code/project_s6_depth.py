"""Project the frozen S6 formal lift without increasing its depth.

This does not prove or disprove the conjectural numerical identity.
The frozen target is transcribed from the existing ProveIt report
fractional-cayley-scaling/continuations/golden-cayley-double-turning,
sections/05_cayley.tex, equation cay:eq:target, at commit
570b0567f311cf1890865065896be2665f469e4f. No upstream module is required.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse,json,time
import depth_projector as P

def s6_target():
    """The inherited raw five-letter shuffle lift (before K-odd projection).

    Raw alphabet: Z=-1, C=0, A=1, B=2, ABAR=3.
    H((F-KF)/2)/i is 485683200 times the frozen real S6 residual.
    """
    z,a,c,b,abar=-1,1,0,2,3
    out={}
    P.add(out,{(z,)*5+(a,a):1},-179712000)
    P.add(out,{(z,)*5+(a,abar):1},485683200)
    P.add(out,{(z,)*3+(a,)+(z,)*2+(a,):1},-36864000)
    P.add(out,{(z,a)+(z,)*4+(a,):1},401080320)
    P.add(out,{(z,)*6+(a,):1},Q(-47600087040,61))
    P.add(out,P.shuffle((z,a),(z,)*4+(c,)),11750400)
    P.add(out,P.shuffle((z,)*3+(a,),(z,)*2+(c,)),109347840)
    P.add(out,P.shuffle((z,)*5+(a,),(b,)),-971366400)
    return out

def change_basis(w):
    table={-1:{P.Z:1},0:{P.X:1,P.B:1},1:{P.Y:Q(1,2),P.H:Q(1,2),P.B:Q(1,2)},2:{P.B:1},3:{P.Y:Q(-1,2),P.H:Q(1,2),P.B:Q(1,2)}}
    out={():1}
    for a in w:
        q={}
        for u,c in out.items():
            for b,d in table[a].items():q[u+(b,)]=c*d
        out=q
    return out
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'verification'/'s6_oriented_normal_form.json')
    args=parser.parse_args()
    start=time.monotonic();raw=s6_target();adapt=P.apply(change_basis,raw)
    odd={w:c for w,c in adapt.items() if P.parity(w)}
    normal=P.apply(P.projection,odd)
    assert normal and all(P.depth(w)<=2 for w in normal)
    data={'schema':'proveit.oriented-cayley-s6.v1','alphabet':{'Z':P.Z,'Y':P.Y,'H':P.H,'B':P.B,'X':P.X},
          'formal_target':'The fixed shuffle-product lift of 485683200 times the frozen S6 residual from golden-cayley-double-turning, eq. cay:eq:target.',
          'input_odd_support':len(odd),'normal_form_support':len(normal),'max_depth':max(map(P.depth,normal)),
          'projection':[{'word':list(w),'coefficient':str(c)} for w,c in sorted(normal.items())],
          'result':'NONZERO FORMAL NORMAL FORM; no assertion about the numerical residual',
          'elapsed_seconds':round(time.monotonic()-start,3)}
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k!='projection'},indent=2))
    print('first entries',data['projection'][:5])
