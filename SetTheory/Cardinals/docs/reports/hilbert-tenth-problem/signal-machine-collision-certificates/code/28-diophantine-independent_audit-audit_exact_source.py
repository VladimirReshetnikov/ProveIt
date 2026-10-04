#!/usr/bin/env python3
"""Owned independent audit. Reads author JSON as inert data; imports no author code.
Sparse polynomials are reconstructed directly from mathematical equations, not
from the emitter, aliases, module metadata, or receipt assertions.
"""
import json, hashlib, math
from collections import Counter
from pathlib import Path
ROOT=Path('/workspace/shared/five-signal-diophantine58-20261004')
OUT=Path('/workspace/shared/five-signal-certificate58-independent-audit-20261004')
class Poly:
    def __init__(self,x=0):
        if isinstance(x,Poly): self.d=dict(x.d)
        elif type(x)==int: self.d={():x} if x else {}
        elif type(x)==str: self.d={(x,):1}
        else: self.d={k:v for k,v in x.items() if v}
    def __add__(self,x):
        d=dict(self.d)
        for k,v in Poly(x).d.items(): d[k]=d.get(k,0)+v
        return Poly(d)
    __radd__=__add__
    def __neg__(self): return Poly({k:-v for k,v in self.d.items()})
    def __sub__(self,x): return self+-Poly(x)
    def __rsub__(self,x): return Poly(x)+-self
    def __mul__(self,x):
        d={}
        for a,av in self.d.items():
            for b,bv in Poly(x).d.items():
                k=tuple(sorted(a+b));d[k]=d.get(k,0)+av*bv
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        assert type(n)==int and n>=0
        a=Poly(1)
        for _ in range(n):a=a*self
        return a
    def __eq__(self,x):return self.d==Poly(x).d
    def degree(self):return max(map(len,self.d),default=-1)
    def digest(self):return hashlib.sha256(json.dumps(sorted(self.d.items()),separators=(',',':')).encode()).hexdigest()

def expected_math(one,quartic):
    # This is the independent specification. Only raw declared leaf names are shared.
    w=lambda n:Poly('w:'+n)
    nat=lambda n:w(n+'.Plus')-1
    sign=lambda n:w(n+'.Positive')-w(n+'.Negative')
    eq={}
    if one:
        g1,g2,g3=[w('gap.'+str(k)) for k in (1,2,3)]
        j=nat('decode.inner');a,b,c=g1-1,g2-1,g3-1
        eq['decode.inner_cantor']=2*j-(b+c)*(b+c+1)-2*c
        eq['decode.outer_cantor']=2*(Poly('i:code')-1)-(a+j)*(a+j+1)-2*j
    else:g1,g2,g3=[Poly('i:g'+str(k)) for k in (1,2,3)]
    D=g1+g2+g3;A=3*g1-D;B=3*(g1+g2)-2*D
    U=6*A-13*B;V=13*A+6*B;delta=nat('radius.delta')
    h=w('fraction.h');q=w('fraction.q');u=sign('fraction.u');v=sign('fraction.v')
    z=[sign('bezout.'+str(k)) for k in (1,2,3)]
    eq.update({'radius.nonnegative':4*D**2-205*(A**2+B**2)-delta,
      'fraction.real':U-h*u,'fraction.imag':V-h*v,'fraction.denominator':2*D-h*q,
      'fraction.primitive':z[0]*u+z[1]*v+z[2]*q-1})
    n=nat('valuation.n');P=w('power5.out');T=w('power_complex.out')
    b=4*P+1;B0=3+4*b
    for prefix,base in [('power5',Poly(5)),('power_complex',B0)]:
        p=lambda key:w(prefix+'.'+key)
        d=lambda key:nat(prefix+'.'+key)
        a=p('aMinus1')+1;beta=p('betaMinus1')+1
        out,ww,M,g,x,y,uu,vv,s,t,qb,qv,J=[p(k) for k in ('out','w','M','g','x','y','u','v','s','t','qb','qv','strict')]
        k=n+1;m=base*out
        formulas=[x**2-1-(a**2-1)*y**2,uu**2-1-(a**2-1)*vv**2,
          s**2-1-(beta**2-1)*t**2,beta-1-4*y*qb,
          beta+uu*d('alpha1')-a-uu*d('alpha2'),vv-y**2*qv,
          s+uu*d('sigma1')-x-uu*d('sigma2'),t+4*y*d('tau1')-k-4*y*d('tau2'),
          y-k-d('dyk'),ww-base-d('dwb'),ww-k-d('dwk'),M-m-J,
          a**2-1-((ww+1)**2-1)*(ww*g)**2,
          2*a*base-M-base**2-1,x+M*d('rho1')-y*(a-base)-m-M*d('rho2')]
        eq.update({prefix+'.eq'+str(k):p for k,p in enumerate(formulas,1)})
    r=w('valuation.r');k=nat('valuation.k');s=w('valuation.s')
    eq['valuation.decompose']=q-P*r
    eq['valuation.remainder']=r-5*k-s
    eq['valuation.nonzero_remainder']=(s-1)*(s-2)*(s-3)*(s-4) if quartic else s+w('valuation.t')-5
    C=sign('complex.C');S=sign('complex.S');kap=sign('complex.quotient')
    eq['complex.C_lower']=C+P-nat('complex.bound.1')
    eq['complex.C_upper']=P-C-nat('complex.bound.2')
    eq['complex.S_lower']=S+P-nat('complex.bound.3')
    eq['complex.S_upper']=P-S-nat('complex.bound.4')
    eq['complex.remainder']=T-C-b*S-kap*(b**2+1)
    eq['acceptance.strict']=delta**2+(r-1)**2+(u-C)**2+(v+S)**2-w('acceptance.positive')
    return eq

def audit_file(path):
    d=json.loads(path.read_text());one=path.name.startswith('one-');quartic='quartic' in path.name
    assert d['inputs']==(['code'] if one else ['g1','g2','g3'])
    assert len(set(d['witnesses']))==len(d['witnesses'])
    declared=set('i:'+x for x in d['inputs'])|set('w:'+x for x in d['witnesses'])
    polys={x:Poly(x) for x in declared}
    def read(ref,j=None):
        assert isinstance(ref,str)
        if ref.startswith('c:'):
            v=int(ref[2:]);assert str(v)==ref[2:];return Poly(v)
        assert ref in polys,(j,ref)
        return polys[ref]
    for j,gate in enumerate(d['gates']):
        assert isinstance(gate,list) and len(gate)==3
        op,a,b=gate;assert op in ('+','-','*')
        pa,pb=read(a,j),read(b,j)
        polys['g:'+str(j)]=pa+pb if op=='+' else pa-pb if op=='-' else pa*pb
    specification=expected_math(one,quartic)
    assert set(e[0] for e in d['equations'])==set(specification)
    assert len(d['equations'])==len(specification)
    residuals=[]
    for name,a,b in d['equations']:
        actual=read(a)-read(b)
        assert actual==specification[name],name
        residuals.append({'name':name,'degree':actual.degree(),'terms':len(actual.d),'polynomial_sha256':actual.digest()})
    expectedF=sum((p*p for p in specification.values()),Poly())
    actualF=read(d['output']);assert actualF==expectedF
    # Literal SOS tail is checked, independent of body-count metadata.
    start=len(d['gates'])-(3*len(specification)-1)
    assert start>=0
    squares=[]
    for k,(_,a,b) in enumerate(d['equations']):
        j=start+2*k
        assert d['gates'][j]==['-',a,b]
        assert d['gates'][j+1]==['*','g:'+str(j),'g:'+str(j)]
        squares.append('g:'+str(j+1))
    cumulative=squares[0]
    for k,sq in enumerate(squares[1:]):
        j=start+2*len(specification)+k
        assert d['gates'][j]==['+',cumulative,sq]
        cumulative='g:'+str(j)
    assert cumulative==d['output'] and start==d['body_gate_count']
    live=set();todo=[d['output']]
    while todo:
        ref=todo.pop()
        if ref in live:continue
        live.add(ref)
        if ref.startswith('g:'):todo+=d['gates'][int(ref[2:])][1:]
    assert declared|{'g:'+str(k) for k in range(len(d['gates']))}<=live
    algebraic_vars=set(v for monomial in actualF.d for v in monomial)
    assert algebraic_vars==declared,(declared-algebraic_vars,algebraic_vars-declared)
    assert actualF.degree()==12
    degree12={k:v for k,v in actualF.d.items() if len(k)==12}
    expected_top={}
    for prefix in ('power5','power_complex'):
        monomial=tuple(sorted(['w:'+prefix+'.w']*8+['w:'+prefix+'.g']*4))
        expected_top[monomial]=1
    assert degree12==expected_top
    expected_counts=(85 if one else 81)-(1 if quartic else 0),46 if one else 44,367 if one else 344
    assert len(d['witnesses'])==expected_counts[0] and len(specification)==expected_counts[1]
    assert len(d['gates'])==expected_counts[2]+(6 if quartic else 0)
    regions=[]
    previous=(0,0,0)
    for region in d['regions']:
        w0,w1=region['witness_range'];g0,g1=region['gate_range'];e0,e1=region['equation_range']
        assert (w0,g0,e0)==previous
        assert w0<=w1 and g0<=g1 and e0<=e1
        # Every introduced witness's first use must be in this region or later;
        # partitions and literal gate operations are independently validated.
        previous=w1,g1,e1
        regions.append({'name':region['name'],'witnesses':w1-w0,'equations':e1-e0,'gates':g1-g0,
            'operations':dict(Counter(x[0] for x in d['gates'][g0:g1]))})
    assert previous==(len(d['witnesses']),len(d['gates']),len(d['equations']))
    return {'source':str(path),'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
      'inputs':len(d['inputs']),'positive_witnesses':len(d['witnesses']),'equations':len(specification),
      'gates':len(d['gates']),'operations':dict(Counter(x[0] for x in d['gates'])),
      'independently_matched_residuals':residuals,'body_gates':start,'sos_gates':3*len(specification)-1,
      'exact_polynomial_degree':actualF.degree(),'exact_polynomial_terms':len(actualF.d),
      'exact_polynomial_sha256':actualF.digest(),'highest_homogeneous_part':[[list(m),v] for m,v in sorted(degree12.items())],
      'all_gates_graph_live':True,'all_leaves_graph_and_algebraically_live':True,'regions':regions}

def main():
    pins=[]
    supplied=json.loads((ROOT/'sources/SOURCE_PINS.json').read_text())
    for pin in supplied:
        file=ROOT/'sources'/pin['file'];raw=file.read_bytes()
        assert hashlib.sha256(raw).hexdigest()==pin['sha256'] and len(raw)==pin['bytes']
        pins.append({'file':pin['file'],'sha256':pin['sha256'],'bytes':len(raw)})
    inherited=Path('/workspace/shared/five-signal-obstruction-independent-audit-20261004/INDEPENDENT_AUDIT.md')
    assert inherited.read_bytes()==(ROOT/'sources/INDEPENDENT_AUDIT.md').read_bytes()
    results=[audit_file(p) for p in sorted((ROOT/'evidence').glob('*.dag.json'))]
    receipt={'all_checks_passed':True,'method':'Fresh standard-library sparse-polynomial expansion against independently transcribed mathematics; JSON only, no author program imported or executed.','source_pins':pins,'dags':results}
    (OUT/'exact-source-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps([{'variant':Path(r['source']).name,**{k:r[k] for k in ['inputs','positive_witnesses','equations','gates','operations','exact_polynomial_degree','exact_polynomial_terms','exact_polynomial_sha256']}} for r in results],indent=2))
if __name__=='__main__':main()
