#!/usr/bin/env python3
"""Exploratory arithmetic DAGs, not replacement universal certificates.

Counts a favorable direct expansion of Vallata--Omodeo Figure 2 and of
the norm-4 bridge in arXiv:2505.16963v1, Definition 10/Theorem 11.
Fixed numerals and supplied aliases are free; multiplication by a numeral
is counted. Square tests, divisibility quotients, and positive inequality
slacks are materialized. Input-domain conversion is deliberately excluded.
Every final residual is checked symbolically against the displayed source.
"""
from collections import Counter
import json
from pathlib import Path
import sympy as s


class DAG:
    def __init__(self):
        self.rows = []
        self.env = {}
        self.cache = {}

    def symbol(self, name):
        self.env[name] = s.Symbol(name)
        return name

    def value(self, x):
        return self.env[x] if isinstance(x, str) else s.Integer(x)

    def op(self, name, op, left, right):
        key = (op, left, right)
        reverse = (op, right, left)
        if key in self.cache:
            return self.cache[key]
        if op in ('+', '*') and reverse in self.cache:
            return self.cache[reverse]
        assert name not in self.env
        a, b = self.value(left), self.value(right)
        self.env[name] = a+b if op == '+' else a-b if op == '-' else a*b
        self.rows.append((name, op, left, right))
        self.cache[key] = name
        return name

    def check(self, left, right, expected):
        assert s.expand(self.value(left)-self.value(right)-expected) == 0

    def receipt(self):
        hist = Counter(row[1] for row in self.rows)
        return {'operations': len(self.rows), 'multiplications': hist['*'],
                'additions': hist['+']+hist['-'], 'schedule': self.rows}


def mr_exponent():
    d = DAG()
    for name in ('x', 'y', 'n', 'i', 'j', 'k', 'ell', 'root1', 'root2', 'quot', 'slack'):
        d.symbol(name)
    op = d.op
    # Rewriting 4*n*(y+1) as 4*(ny+n) shares ny with the inequality.
    ny = op('ny', '*', 'n', 'y')
    np = op('nypn', '+', ny, 'n')
    four = op('four_nypn', '*', 4, np)
    mx = op('M_before_two', '+', four, 'x')
    M = op('M', '+', mx, 2)
    B = op('B', '+', 'n', 1)
    C = op('C', '+', B, 'k')
    A = op('A', '*', M, 'x')
    mm1 = op('Mminus1', '-', M, 1)
    lp = op('ell_Mminus1', '*', 'ell', mm1)
    L = op('L', '+', B, lp)
    a2 = op('A2', '*', A, A)
    disc = op('disc', '-', a2, 1)
    c2 = op('C2', '*', C, C)
    dc = op('discC2', '*', disc, c2)
    D = op('D', '+', dc, 1)
    c2d = op('C2D', '*', c2, D)
    ie = op('iC2D', '*', 'i', c2d)
    E = op('E', '*', 2, ie)
    e2 = op('E2', '*', E, E)
    fe = op('discE2', '*', disc, e2)
    F = op('F', '+', fe, 1)
    fa = op('FminusA', '-', F, A)
    gf = op('G_before_A', '*', fa, F)
    G = op('G', '+', gf, A)
    jc = op('jC', '*', 'j', C)
    twojc = op('twojC', '*', 2, jc)
    H = op('H', '+', B, twojc)
    g2 = op('G2', '*', G, G)
    gd = op('G2minus1', '-', g2, 1)
    h2 = op('H2', '*', H, H)
    gi = op('GdiscH2', '*', gd, h2)
    I = op('I', '+', gi, 1)
    df = op('DF', '*', D, F)
    dfi = op('DFI', '*', df, I)
    root1 = op('root1square', '*', 'root1', 'root1')
    hc = op('HminusC', '-', H, C)
    fq = op('Fquot', '*', F, 'quot')
    m2 = op('M2', '*', M, M)
    md = op('M2minus1', '-', m2, 1)
    l2 = op('L2', '*', L, L)
    ml = op('MdiscL2', '*', md, l2)
    pell2 = op('pell2', '+', ml, 1)
    root2 = op('root2square', '*', 'root2', 'root2')
    ly = op('Ly', '*', L, 'y')
    diff = op('CminusLy', '-', C, ly)
    diff2 = op('CminusLy2', '*', diff, diff)
    xny = op('xny', '*', 'x', ny)
    prod = op('error_product', '*', diff2, xny)
    error4 = op('four_error', '*', 4, prod)
    bound = op('bound_rhs', '+', error4, 'slack')
    x,y,n,i,j,k,ell,rr,ss,qq,slack = [d.value(z) for z in
        ('x','y','n','i','j','k','ell','root1','root2','quot','slack')]
    assert s.expand(d.value(M)-(4*n*(y+1)+x+2)) == 0
    # Use the now-validated register expression thereafter, keeping this
    # check compositional instead of expanding the entire high-degree DAG.
    ms = d.value(M); bs=n+1; cs=k+bs; aa=ms*x; ls=bs+ell*(ms-1)
    ds=(aa**2-1)*cs**2+1; es=2*i*cs**2*ds
    fs=(aa**2-1)*es**2+1; gs=(fs-aa)*fs+aa; hs=bs+2*j*cs
    iss=(gs**2-1)*hs**2+1
    # Avoid full expansion of the large DFI polynomial; source aliases are
    # validated in topological order, then final residuals use those aliases.
    for name, expr in ((M,ms),(B,bs),(C,cs),(A,aa),(L,ls),(D,ds),(E,es),
                       (F,fs),(G,gs),(H,hs),(I,iss)):
        assert s.expand(d.value(name)-expr)==0
    assert d.value(dfi)==d.value(D)*d.value(F)*d.value(I)
    d.check(hc,fq,hs-cs-fs*qq)
    d.check(pell2,root2,(ms**2-1)*ls**2+1-ss**2)
    d.check(l2,bound,ls**2-4*(cs-ls*y)**2*x*y*n-slack)
    assert d.value(root1)==rr**2
    return d.receipt()


def lucas_bridge():
    d = DAG()
    for name in ('X','Y','b','h','k','ell','w','x','y','root1','root2','quot','slack'):
        d.symbol(name)
    op=d.op
    ly=op('ellY','*','ell','Y'); ux=op('XellY','*','X',ly); U=op('U','*',2,ux)
    wy=op('wY','*','w','Y'); V=op('V','*',4,wy)
    vp=op('Vplus1','+',V,1); A=op('A','*',U,vp)
    xx=op('twoX','*',2,'X'); B=op('B','+',xx,1)
    am=op('Aminus2','-',A,2); ah=op('Aminus2h','*',am,'h'); C=op('C','+',B,ah)
    a2=op('A2','*',A,A); disc=op('disc','-',a2,4)
    c2=op('C2','*',C,C); dc=op('discC2','*',disc,c2); D=op('D','+',dc,4)
    cd=op('C2D','*',c2,D); E=op('E','*',cd,'x')
    e2=op('E2','*',E,E); de=op('discE2','*',disc,e2)
    four=op('four_discE2','*',4,de); F=op('F','+',four,1)
    df=op('DF','*',D,F); cdf=op('CDF','*',C,df)
    ade=op('Aminus2_discE2','*',am,de); ade2=op('two_Aminus2_discE2','*',2,ade)
    gg=op('Gminus1','-',cdf,ade2); G=op('G','+',gg,1)
    yy=op('twoy','*',2,'y'); ym=op('twoyminus1','-',yy,1)
    yc=op('twoyminus1C','*',ym,C); hb=op('Hinner','+',B,yc)
    hf=op('Hproduct','*',F,hb); H=op('H','+',C,hf)
    g2=op('G2','*',G,G); gd=op('G2minus1','-',g2,1)
    h2=op('H2','*',H,H); gi=op('GdiscH2','*',gd,h2); I=op('I','+',gi,1)
    dfi=op('DFI','*',df,I); root1=op('root1square','*','root1','root1')
    u2=op('U2','*',U,U); Q=op('Q','*',u2,V); qm=op('Qminus2','-',Q,2)
    kq=op('kQminus2','*','k',qm); xp=op('Xplus1','+','X',1); J=op('J','+',xp,kq)
    q2=op('Q2','*',Q,Q); qd=op('Q2minus4','-',q2,4)
    j2=op('J2','*',J,J); qj=op('QdiscJ2','*',qd,j2); pj=op('pellJ','+',qj,4)
    root2=op('root2square','*','root2','root2')
    aa=op('twoA','*',2,A); mod=op('modulus','-',aa,5)
    bw=op('bw','*','b','w'); bw2=op('bw2','*',bw,bw)
    bw2m=op('bw2minus1','-',bw2,1); rhs=op('two_bw2minus1','*',2,bw2m)
    bwc=op('bwC','*',bw,C); lhs=op('three_bwC','*',3,bwc)
    diff=op('dividend','-',lhs,rhs); mq=op('modulusquot','*',mod,'quot')
    lj=op('ellYJ','*',ly,J); cj=op('CminusellYJ','-',C,lj)
    ce=op('four_difference','*',4,cj); cesq=op('four_difference2','*',ce,ce)
    bound=op('bound_rhs','+',cesq,'slack')
    val=d.value
    # The factored G/H forms are exactly Definition 10, with g=1.
    atom=s.Symbol('atom')
    assert s.expand((atom-2)*(atom**2-4)-(atom+2)*(atom-2)**2)==0
    assert val(G)==1+val(cdf)-val(ade2)
    ca,ba,fa,ya=s.symbols('ca ba fa ya')
    assert s.expand(ca+fa*(ba+(2*ya-1)*ca)
                    -(ca+ba*fa+(2*ya-1)*ca*fa))==0
    assert val(dfi)==val(D)*val(F)*val(I)
    d.check(pj,root2,(val(U)**4*val(V)**2-4)*val(J)**2+4-val('root2')**2)
    d.check(diff,mq,3*val('b')*val('w')*val(C)
            -2*(val('b')**2*val('w')**2-1)-(2*val(A)-5)*val('quot'))
    d.check(j2,bound,val(J)**2-16*(val(C)-val('ell')*val('Y')*val(J))**2-val('slack'))
    return d.receipt()


if __name__ == '__main__':
    result={'status':'EXPLORATORY_ARITHMETIC_PASS',
            'scope':'favorable direct expansions; no replacement theorem or minimality claim',
            'mr_exponent':mr_exponent(), 'lucas_bridge_g1':lucas_bridge()}
    for name in ('mr_exponent','lucas_bridge_g1'):
        row=result[name]
        print(name,row['operations'],row['multiplications'],row['additions'])
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
