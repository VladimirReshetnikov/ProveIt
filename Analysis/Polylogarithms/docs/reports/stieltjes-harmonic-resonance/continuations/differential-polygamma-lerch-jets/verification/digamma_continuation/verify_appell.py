"""Exact checks for the printed Appell formulas and weight-six certificate."""
from pathlib import Path
from functools import lru_cache
import json
import sympy as sp
from compute_appell import compute, nice, even_reduce, h, A, v, z

BASE=Path(__file__).parent
def d(word,j):return sp.Symbol('d_'+'_'.join(map(str,word))+'__'+str(j))
def D(word,i,j):return d(word,i)-d(word,j)
def dz(k):return d((k,),1)
def print_D6():
    return 120*z[2]*D((2,1),1,2)-60*D((2,2,1),2,3)+120*D((3,1,1),1,2)-180*D((4,1),1,2)-30*D((2,3),1,2)+138*dz(5)-60*z[2]*dz(3)+30*z[3]*dz(2)
def print_D7():
    return (840*z[2]*D((2,1,1),1,2)-840*z[2]*D((3,1),1,2)+210*z[2]*d((2,2),1)
      -420*D((2,2,1,1),2,3)+630*D((2,3,1),2,3)+840*D((3,1,1,1),1,2)
      +420*D((3,1,2),1,2)+210*(2*D((3,2,1),1,3)+D((3,2,1),2,3))+210*d((2,2,2),1)
      +798*d((3,3),1)-1260*D((4,1,1),1,2)+168*D((2,4),1,2)+1596*D((5,1),1,2)
      +sp.Rational(651,2)*z[4]*dz(2)+336*z[2]*dz(4)-378*z[3]*dz(3)-504*dz(6))

def main():
    checks=[]
    replacements={
      d((2,2),2):z[2]*dz(2)-dz(4)-d((2,2),1),
      d((3,3),2):z[3]*dz(3)-dz(6)-d((3,3),1),
      d((3,2),1):z[2]*dz(3)-dz(5)-d((2,3),2),
      d((3,2),2):z[3]*dz(2)-dz(5)-d((2,3),1),
      d((4,2),1):z[2]*dz(4)-dz(6)-d((2,4),2),
      d((4,2),2):z[4]*dz(2)-dz(6)-d((2,4),1),
      d((2,2,2),3):sp.Rational(3,4)*z[4]*dz(2)-z[2]*dz(4)+dz(6)-d((2,2,2),1)-d((2,2,2),2),
    }
    for m,printed in [(6,print_D6()),(7,print_D7())]:
        data=compute(m)
        raw=sp.expand(sum(nice(c)*d(w,pos+1) for (w,pos),c in data['Dwords'].items()))
        diff=even_reduce(raw.subs(replacements,simultaneous=True)-printed)
        assert diff==0,(m,diff)
        checks.append(f'Exact differentiated-stuffle reduction D{m}')
        assert even_reduce(raw.subs(replacements,simultaneous=True)-(printed+dz(m-1)))!=0
        checks.append(f'Changed D{m} ordinary derivative coefficient rejected')
        # The actual rational finite-index shift is checked independently of tail asymptotics.
        for n in [1,2,5,11]:
            hn={h[r-1]:sum(sp.Rational(1,k**r) for k in range(1,n+1)) for r in range(1,m)}
            hp={h[r-1]:sum(sp.Rational(1,k**r) for k in range(1,n)) for r in range(1,m)}
            exact=even_reduce(data['defect'].subs(hn)-data['defect'].subs(hp))
            alt=even_reduce(data['dt'].subs({v:sp.Rational(1,n),h[0]:hp[h[0]],**{A[r-1]:z[r]-hn[h[r-1]] for r in range(2,m)}},simultaneous=True))
            assert sp.expand(exact-alt)==0
            checks.append(f'Exact original-index/tail-index difference at m={m}, n={n}')
    record=json.loads((BASE/'mzv6_relations.json').read_text())
    mat=sp.Matrix([[sp.Rational(x) for x in row] for row in record['matrix']])
    inverse=sp.Matrix([[sp.Rational(x) for x in row] for row in record['selected_inverse']])
    selected=record['selected_rows']
    assert inverse*mat[selected,:]==sp.eye(16)
    checks.append('Independent rational replay of 16 by 16 weight-six left inverse')
    rhs=sp.Matrix([sp.sympify(x) for x in record['rhs']])
    sol=sp.Matrix([sp.sympify(record['solutions'][str(tuple(w))]) for w in record['words']])
    assert all(sp.expand(x)==0 for x in inverse*rhs[selected,:]-sol)
    assert all(sp.expand(x)==0 for x in mat*sol-rhs)
    checks.append('All 49 shuffle/stuffle/duality equations satisfied by certified solution')
    out={'passed':True,'exact_checks':len(checks),'checks':checks,'scope':'Finite algebra only; analytic justifications are proved in the article.'}
    (BASE/'exact_appell.json').write_text(json.dumps(out,indent=2))
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
