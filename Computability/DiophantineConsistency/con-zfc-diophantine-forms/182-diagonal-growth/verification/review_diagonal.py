#!/usr/bin/env python3
"""Independent reconstruction of the five-row diagonal edit and its majorant.

No producer module is imported. Exact integers, positive expression degrees,
all residual coefficients and the entire collected quartic are checked.
"""
from pathlib import Path
from collections import defaultdict
from hashlib import sha256
import json

ROOT = Path(__file__).resolve().parents[1] / 'direct'
PARENT_SHA = '8d919a1e5d6a802765b6d010c0140fb1d83c3d36d211b209b7a8d2fb3f3fb6f6'
C = 464
D = 3*C*C

def require(x, message):
    if not x:
        raise ValueError(message)

def plus(*polys):
    p = defaultdict(int)
    for q in polys:
        for mon, coef in q.items():
            p[mon] += coef
    return {m:c for m,c in p.items() if c}

def times(p, q):
    r = defaultdict(int)
    for m,c in p.items():
        for n,d in q.items():
            r[tuple(sorted(m+n))] += c*d
    return {m:c for m,c in r.items() if c}

def scale(p, c): return {m:v*c for m,v in p.items() if v*c}
def var(i): return {(i,):1}
def con(i): return {():i} if i else {}
def square(p): return times(p,p)
def decode(row): return {tuple(m):c for c,m in row['terms']}

class Positive:
    """A positive-coefficient expression evaluated at the diagonal a=b=c=d=C."""
    def __init__(self, value, degree=0):
        self.value=value
        self.degree=degree
    def __add__(self, other):
        if type(other) is int: other=Positive(other)
        return Positive(self.value+other.value, max(self.degree,other.degree))
    __radd__=__add__
    def __mul__(self, other):
        if type(other) is int: other=Positive(other)
        return Positive(self.value*other.value, self.degree+other.degree)
    __rmul__=__mul__
    def __pow__(self, n):
        require(type(n)is int and n>=0, 'positive literal power')
        return Positive(self.value**n, self.degree*n)

def independent_labels(diagonal):
    # These constructors are independently transcribed from the mathematical
    # C222 square-shell definition, not executed through shell_source.py.
    I=lambda x,y:2*((x+y)**2+x)
    M=lambda x,y:I(x,y)+1
    A=lambda x,y:2*((x+y)**2+3*x+4*y+3)
    E=lambda x,y:A(x,y)+1
    N=lambda x:I(x,1)
    Ex=lambda x,h:N(A(x,N(h)))
    def req(y,k,h):
        return A(y,I(h,N(A(y,I(h,N(M(y,k)))))))
    def clos(x,y,k,h):
        subset=A(k,I(M(k,x),M(k,y)))
        return A(y,I(M(y,k),N(A(x,I(h,N(A(x,I(subset,req(y,k,h)))))))))
    def bundle(x,y,k):
        rv=I(M(x,y),A(k,M(x,y)))
        negative=A(k,I(clos(x,y,k,k),N(req(y,k,k))))
        return N(I(rv,negative))
    a,b,c,d=[Positive(diagonal,1) for _ in range(4)]
    codes=[Ex(a,E(a,b)), I(A(a,I(b,c)),I(A(a,b),A(a,c))),
      I(E(a,b),I(M(c,a),M(c,b))), I(A(a,A(b,c)),A(b,A(a,c))),
      I(E(c,a),I(M(c,b),M(a,b))), I(Ex(a,A(a,b)),b),
      I(E(c,a),I(E(c,b),A(M(a,b),E(a,b)))),
      I(I(I(c,d),a),I(I(a,c),I(b,c))), bundle(a,b,c)]
    return codes, sum(codes)+a+b+I(a,b)+A(a,b)+1

def main():
    parent_raw=(ROOT/'principal/equation.json').read_bytes()
    require(sha256(parent_raw).hexdigest()==PARENT_SHA, 'parent identity')
    parent=json.loads(parent_raw)
    new_raw=(ROOT/'diagonal214/equation.json').read_bytes()
    new=json.loads(new_raw)
    before=list(map(decode,parent['residuals']))
    after=list(map(decode,new['residuals']))
    require(len(parent['variables'])==215 and len(new['variables'])==214,'dimensions')
    require(len(before)==154 and len(after)==153,'row counts')
    require(new['variables']==parent['variables'][:214], 'all retained variable metadata')
    require(new['domain']=='unrestricted integers', 'domain')
    require(before[96]=={():1,(0,0):1,(0,132):-2,(139,):1}, 'old base row')
    require(before[97]=={(0,182):-1,(2,):1,(139,140):1,(181,):-1}, 'old output row')
    require(before[130]=={():-128,(0,):1,(185,185):-4}, 'old horizon')
    require(before[152]=={(0,0):-1,(214,):1}, 'old square wire')
    require(before[153]=={(93,):1,(214,214):-1}, 'old quartic index')
    expected=before[:153]
    expected[96]={():1,(93,93):1,(93,132):-2,(139,):1}
    expected[97]={(2,):1,(93,182):-1,(139,140):1,(181,):-1}
    expected[128]=plus(before[128],{(0,0):1,(93,93):-1})
    expected[130]={():-C,(0,):1,(185,185):-1}
    expected[152]={(93,):1,(0,0):-C}
    require(after==expected, 'every changed and unchanged residual')
    require([j for j in range(153) if before[j]!=after[j]]==[96,97,128,130,152],
            'exact change inventory')
    require([j for j,p in enumerate(before) if any(214 in m for m in p)]==[152,153],
            'deleted coordinate private')
    require([j for j,p in enumerate(before) if any(185 in m for m in p)]==[130],
            'horizon root private')
    # Independently rebuild the entire square frame, including BOTH K uses.
    t,F,K,A=var(0),var(2),var(93),var(132)
    atoms=[t,plus(t,con(1)),plus(F,t),var(1),K,var(3),F,var(4),
           plus(var(8),con(-1))]
    atoms.extend(var(i) for i in range(9,16))
    atoms.extend([scale(var(16),2),var(17),K,plus(var(95),con(-1)),
                  var(95),var(184)])
    atoms.extend(var(i)for i in [96,97,101,104,107,110,113,114,117,120,121,125,128])
    frame=plus(var(131),con(-2),*(scale(square(a),-1)for a in atoms))
    require(frame==after[128], 'full actual frame reconstruction')
    require(len(atoms)==35,'all frame atoms')
    # The index pair and its orientation/cap terms remain intact.
    require(after[126]=={():1,(132,182):-1,(181,):-1,(183,):1},'pair product row')
    require(after[127]=={():-1,(181,):2,(181,181):-1,(181,183):2,(182,182):1},
            'pair norm row')
    require(after[141].get((93,93))==1 and after[141].get((93,182))==-2,
            'index orientation')
    require(after[144].get((182,182))==-1,'index cap')
    expanded=plus(*(square(p)for p in after))
    frozen=json.loads((ROOT/'diagonal214/expanded_polynomial.json').read_bytes())
    require(expanded=={tuple(m):c for c,m in frozen['terms']},'entire quartic expansion')
    require({v for p in after for m in p for v in m}==set(range(214)),'all coordinates live')
    metrics={'variables':214,'residuals':153,'degree':max(map(len,expanded)),
             'monomials':len(expanded),'height':max(map(abs,expanded.values())),
             'residual_monomials':sum(map(len,after)),
             'residual_height':max(abs(c)for p in after for c in p.values()),
             'domain':'unrestricted integers'}
    require(metrics==json.loads((ROOT/'diagonal214/metrics.json').read_bytes()),'every metric')
    # Every term of J has nonnegative coefficients and degree at most524288.
    codes,J=independent_labels(C)
    bound=pow(C,D)
    require(J.degree==524288,'actual label-sum degree')
    require(J.degree<D,'degree below majorant exponent')
    require(J.value<bound,'exact diagonal inequality')
    require(J.value.bit_length()==5692913 and bound.bit_length()==5721264,'independent bit lengths')
    receipt={'status':'PASS','equation_sha256':sha256(new_raw).hexdigest(),
      'parent_sha256':PARENT_SHA,'metrics':metrics,'changed_rows':[96,97,128,130,152],
      'deleted_coordinate_private':True,'frame_atoms_reconstructed':len(atoms),
      'growth_pair_and_orientation_retained':True,'C':C,'majorant_exponent':D,
      'label_degree':J.degree,'axiom_degrees':[p.degree for p in codes],
      'J_at_C_bits':J.value.bit_length(),'C_to_D_bits':bound.bit_length(),
      'J_at_C_sha256':sha256(J.value.to_bytes((J.value.bit_length()+7)//8,'big')).hexdigest(),
      'scope':'Independent exact finite algebra and positive-expression audit; unbounded argument is in DIAGONAL_REVIEW.md. No inherited formal-kernel rebuild.'}
    print(json.dumps(receipt,indent=2,sort_keys=True))
if __name__=='__main__': main()
