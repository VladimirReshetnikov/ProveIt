"""Exact algebraic checks and generated identity tables. Run from bundle root."""
from __future__ import annotations
import json, sys
from pathlib import Path
from math import comb
import sympy as s
from gap_reduce import correction, parity_component, u_matrix, t_matrix
ROOT=Path(__file__).resolve().parents[1]
pi=s.pi; I=s.I; Z=s.zeta
L2,L3=s.symbols('ell_2 ell_3', real=True)
B={n:s.Symbol('B'+str(n),real=True) for n in range(2,17,2)}
C={n:s.Symbol('C'+str(n),real=True) for n in range(2,17,2)}

def singles(n:int, root:str='i'):
    if root=='i': x=s.Rational(1,4); ell=L2; even=B
    elif root=='rho': x=s.Rational(1,3); ell=L3; even=C
    else: raise ValueError(root)
    if n==1: return -ell/2+I*pi*(s.Rational(1,2)-x)
    re=(-s.Rational(1,2)**n*(1-s.Rational(1,2)**(n-1))*Z(n) if root=='i'
        else (s.Rational(1,3)**(n-1)-1)*Z(n)/2)
    im=(even[n] if n%2==0 else s.simplify(-(2*pi*I)**n*s.bernoulli(n,x)/(2*I*s.factorial(n))))
    return re+I*im

def part(a,b,root='i'):
    return s.simplify(s.expand(parity_component(a,b,lambda n:singles(n,root),Z,s.conjugate,
                                                s.im if (a+b)%2==0 else s.re)))

def write_results():
    results={'partial_fraction_tests':0,'matrix_weights':[],'exact_candidate_checks':[],'new_target_checks':[]}
    x=s.symbols('x')
    # Equality of rational functions, not a finite sample in x.
    for a in range(1,8):
      for b in range(1,8):
        w=a+b
        rhs=sum((-1)**(b-j)*s.binomial(w-j-1,a-1)/x**j for j in range(1,b+1))
        rhs+=sum((-1)**b*s.binomial(w-j-1,b-1)/(x+1)**j for j in range(1,a+1))
        assert s.cancel(rhs-1/(x**b*(x+1)**a))==0
        results['partial_fraction_tests']+=1
    for w in range(2,25):
        U=s.Matrix(u_matrix(w)); T=s.Matrix(t_matrix(w)); n=w-1
        V=s.Matrix([[(-1)**(a-j)*comb(w-j-1,a-j) if j<=a else 0 for j in range(1,w)] for a in range(1,w)])
        assert U*V==s.eye(n) and T*T==s.eye(n)
        rows=[]
        for a in range(1,w//2+1): rows.append(list(U[a-1,:]+U[w-a-1,:]))
        # Projected stuffle is delta_a*(Y_a-Y_{w-a}).
        for a in range(1,(w+1)//2): rows.append(list((-1)**(w-a+1)*(U[a-1,:]-U[w-a-1,:])))
        M=s.Matrix(rows); det=M.det()
        assert abs(det)==2**(w//2)
        results['matrix_weights'].append({'weight':w,'determinant':str(det),'rank':n})
    g={a:part(a,6-a) for a in range(1,6)}
    G=B[2]; b4=B[4]; b6=B[6]
    expected={
      5:(-64*pi**3*Z(3)-527*pi*Z(5)+4096*b6)/2048,
      4:(96*pi**3*Z(3)-32*pi**2*b4+1581*pi*Z(5)-8448*b6)/1536,
      3:(-3*pi**3*Z(3)+64*pi**2*b4-1581*pi*Z(5)+4608*b6)/1024,
      2:(-14*pi**4*G+135*pi**3*Z(3)-1440*pi**2*b4+23715*pi*Z(5)-69120*b6)/23040,
      1:(-150*pi**5*L2+56*pi**4*G-270*pi**3*Z(3)+1920*pi**2*b4-675*pi*Z(5))/92160}
    for a in range(1,6):
      assert s.simplify(g[a]-expected[a])==0
      results['exact_candidate_checks'].append('gauss:eq:g'+str(a)+str(6-a))
    # The "sporadic" weight-five row is exactly 960 shuffle(1,4)-224 shuffle(2,3).
    U5=s.Matrix(u_matrix(5))
    coeff=960*(U5[0,:]+U5[3,:])-224*(U5[1,:]+U5[2,:])
    assert list(coeff)==[576,288,736,960]
    sp=s.simplify(960*s.im(singles(1)*singles(4))-224*s.im(singles(2)*singles(3)))
    assert s.simplify(sp-(21*B[2]*Z(3)-480*B[4]*L2))==0
    results['exact_candidate_checks'].append('gauss:eq:wt5-sporadic')
    lines=[]
    data={}
    for root in ['i','rho']:
      for w in range(2,9):
        for a in range(1,w):
          expr=part(a,w-a,root)
          component='imag' if w%2==0 else 'real'
          data[f'{root}:F{a},{w-a}:{component}']=s.sstr(expr)
          # Two expanded terms per line keep the TeX fragment within normal margins.
          terms=s.expand(expr).as_ordered_terms()
          head=(r'\Im' if w%2==0 else r'\Re')+' F_{'+str(a)+','+str(w-a)+'}('+('i' if root=='i' else r'\rho')+')'
          chunks=[]
          for start in range(0,len(terms),2):
            text=''
            for idx,term in enumerate(terms[start:start+2],start):
              if term.could_extract_minus_sign(): text+='-'+s.latex(-term)
              else: text+=('+' if idx else '')+s.latex(term)
            chunks.append((head+r' &=' if start==0 else r' &{}')+text)
          lines.append(r'\begin{align*}'+ '\n'+(' '+r'\\'+'\n').join(chunks)+r'.'+'\n'+r'\end{align*}')
    (ROOT/'generated'/'parity_tables.tex').write_text('\n'.join(lines)+'\n')
    (ROOT/'generated'/'parity_tables.json').write_text(json.dumps(data,indent=2)+'\n')
    # Targeted mixed-point real projection, a=4,b=1, using the opposite stuffle.
    for root in ['i','rho']:
      li=lambda n:singles(n,root)
      rest=s.simplify(s.re(li(4)*s.conjugate(li(1)))-Z(5)-s.re(correction(1,4,li,Z)))
      print(root, 'Re D41 = Re F41 +',rest)
      print(root, 'Im D51 =',s.simplify(3*s.im(li(6))-Z(2)*s.im(li(4))-Z(4)*s.im(li(2))-(L2 if root=='i' else L3)/2*s.im(li(5))))
    # Explicit real targets and their existing F41 coordinates, both roots.
    for root in ['i','rho']:
      li=lambda n:singles(n,root)
      hf=part(4,1,root)
      expected_h=(-pi*B[4]/4+pi**2*Z(3)/48+s.Rational(467,1024)*Z(5) if root=='i'
                  else -pi*C[4]/6-s.Rational(13,54)*Z(5)+pi**2*Z(3)/18)
      rest=s.re(li(4)*s.conjugate(li(1)))-Z(5)-s.re(correction(1,4,li,Z))
      expected_d=(3*pi**4*L2/512+pi**2*Z(3)/64-s.Rational(587,1024)*Z(5) if root=='i'
                  else 2*pi**4*L3/243+2*pi**2*Z(3)/27-s.Rational(281,162)*Z(5))
      expected_im=(3*B[6]-pi**2*B[4]/6-pi**4*B[2]/90-5*pi**5*L2/3072 if root=='i'
                   else 3*C[6]-pi**2*C[4]/6-pi**4*C[2]/90-pi**5*L3/729)
      imd=sum(part(6-j,j,root) for j in range(1,6))+s.im(correction(5,1,li,Z))
      assert s.simplify(hf-expected_h)==0
      assert s.simplify(hf+rest-expected_d)==0
      assert s.simplify(imd-expected_im)==0
      results['new_target_checks'].extend([root+':ReF41',root+':ReD41',root+':ImD51'])
    (ROOT/'verification'/'exact_checks.json').write_text(json.dumps(results,indent=2)+'\n')
    print('Exact checks:', results['partial_fraction_tests'],'rational functions;',len(results['matrix_weights']),'weights;',len(results['exact_candidate_checks']),'manuscript identities;',len(results['new_target_checks']),'additional target checks.')

if __name__=='__main__': write_results()
