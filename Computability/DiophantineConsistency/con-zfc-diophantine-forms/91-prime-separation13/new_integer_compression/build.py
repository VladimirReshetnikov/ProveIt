#!/usr/bin/env python3
"""Construct explicit integer consistency polynomials by finite arithmetic.

The shared DAG utility is attributed in NOTICE.md.  This builder uses no
proof search and no undecided logical predicate.  Every output is an ordinary
integer polynomial with a finite straight-line specification.
"""
from pathlib import Path
import json
from circuit import DAG

ROOT = Path(__file__).resolve().parent
PORTS = ['beta','K0','MC','MF','cone_A','cone_B']

def require(condition,message):
    if not condition:raise ValueError(message)

class Algebra:
    def __init__(self, graph):
        self.g=graph; self.zero=graph.lit(0); self.one=graph.lit(1)
    def lit(self,n): return self.g.lit(n)
    def add(self,a,b): return self.g.op('add',a,b)
    def sub(self,a,b): return self.g.op('sub',a,b)
    def mul(self,a,b): return self.g.op('mul',a,b)
    def neg(self,a): return self.sub(self.zero,a)
    def pow(self,a,n): return self.g.power(a,n)
    def scale(self,n,a): return self.mul(self.lit(n),a)
    def trim(self,p):
        p=list(p)
        while len(p)>1 and p[-1]==self.zero:p.pop()
        return p
    def pconst(self,a):return [a]
    def padd(self,a,b):
        return self.trim([self.add(a[i] if i<len(a) else self.zero,b[i] if i<len(b) else self.zero) for i in range(max(len(a),len(b)))])
    def psub(self,a,b):
        return self.trim([self.sub(a[i] if i<len(a) else self.zero,b[i] if i<len(b) else self.zero) for i in range(max(len(a),len(b)))])
    def pmul(self,a,b):
        out=[self.zero]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):out[i+j]=self.add(out[i+j],self.mul(x,y))
        return self.trim(out)
    def pscale(self,a,p):return self.trim([self.mul(a,b) for b in p])
    def ppow(self,a,n):
        out=[self.one]
        for _ in range(n):out=self.pmul(out,a)
        return out
    def peval(self,p,x):
        out=p[-1]
        for v in reversed(p[:-1]):out=self.add(self.mul(out,x),v)
        return out
    def pairmul(self,p,q,trace,constant):
        # The abstract root w satisfies w^2 = trace*w + constant.
        e1,o1=p;e2,o2=q
        oo=self.pmul(o1,o2)
        even=self.padd(self.pmul(e1,e2),self.pscale(constant,oo))
        odd=self.padd(self.padd(self.pmul(e1,o2),self.pmul(o1,e2)),self.pscale(trace,oo))
        return even,odd
    def pairnorm(self,p,trace,constant):
        e,o=p
        # Sum and product of roots are trace and -constant.
        return self.psub(self.padd(self.pmul(e,e),self.pscale(trace,self.pmul(e,o))),self.pscale(constant,self.pmul(o,o)))
    def shift_and_norm(self,coeffs,scale,trace,constant,denominator=None):
        # Homogenized f(x-scale*w/denominator), then the quadratic norm.
        den=self.one if denominator is None else denominator
        n=len(coeffs)-1
        root=([self.zero,den],[self.neg(scale)])
        power=([self.one],[self.zero])
        total=([self.zero],[self.zero])
        for i,coef in enumerate(coeffs):
            multiplier=self.mul(coef,self.pow(den,n-i))
            total=(self.padd(total[0],self.pscale(multiplier,power[0])),
                   self.padd(total[1],self.pscale(multiplier,power[1])))
            power=self.pairmul(power,root,trace,constant)
        return self.pairnorm(total,trace,constant),total

def definitions(normalized=False,odd_c=False):
    d={
      'J':'6*J6+1' if normalized else '3*J3+1',
      'q':'beta*J+1','W':'4*(3*w3+1)','X':'q*W',
      'Y':'(2*v_scale+1)*q**3','E':'X*Y','a':'(X+1)*Y',
      'H':'4*a+3','Delta':'a**2+H',
      'F':'(K0+W)*C-z*(q-1)',
      'R':'(q*(q-F)-C)*(q**2-1)+(MC+q*MF)*J',
      'k':'R+1+h*E','eta':'c-Y*k','u':'E*Y*k','A':'u*(u+k)+1',
      'U':'(2*r+1)*c**2',
      'F2':'1+Delta*U**2' if normalized else 'f**2',
      'Q':'Delta**2*U**2' if normalized else 'U**2',
      'delta':'Q-1',
      'V':'F2*(c*T-R)-c' if normalized else 'f*c*T-F2*R-c',
      'D0':'X+a*c','Dm':'1+Delta*c**2',
      # Cancellation of the degree-14 terms is exposed exactly here.
      'M0':'X**2+2*X*a*c-H*c**2-1',
      't':'2*u+k','ell':'k**2-4',
      'j0':'9*delta*ell-4*(V**2-1)',
      'j1':'delta*(6*t+4*V)',
      'h0':'12*delta*t*V',
      'tail':'576*delta*A*(1-V**2)+144*delta**2*ell*V**2',
      'det':'(cone_A*F)*(cone_B*C)-(q-cone_A*F-cone_B*C)**2',
      'eta_zeta':'eta*(k-eta)',
      'Pos':'1+pair_pos1**2+pair_pos2**2+pair_pos3*(pair_pos3+1)',
      'G':'det*eta_zeta-(pair_root**2-det-eta_zeta+1)**2-Pos',
      'Bguard':'det*eta_zeta-(pair_root**2-det-eta_zeta+1)**2-1-pair_pos2**2-pair_pos3*(pair_pos3+1)',
      'Strong':'Q-Delta*(F2-1)',
      'Main':'(D0+H*gamma)**2-Dm',
      'f_center':'(a+2)*U',
    }
    if odd_c:d['c']='2*c1+1'
    return d

def live_packet(g,out,rows,name,extra):
    table={n['id']:n for n in g.nodes+g.fixed}; live=set()
    def visit(x):
        if x in live:return
        live.add(x)
        if x in table:visit(table[x]['left']);visit(table[x]['right'])
    visit(out)
    gates=[n for n in g.nodes if n['id'] in live]
    fixed=[n for n in g.fixed if n['id'] in live]
    require(all('v:'+v in live for v in g.variables),'every listed coordinate must be live')
    degree={}
    for v in g.variables:degree['v:'+v]=1
    for p in g.ports:degree['c:'+p]=0
    def dg(x):
        if x.startswith('n:'):return -10**9 if x=='n:0' else 0
        return degree[x]
    for n in g.fixed+g.nodes:
        a,b=dg(n['left']),dg(n['right'])
        degree[n['id']]=a+b if n['op']=='mul' else max(a,b)
    return dict(name=name,domain='unrestricted integers',variables=g.variables,
      variable_count=len(g.variables),fixed_ports=g.ports,fixed_recipes=fixed,nodes=gates,
      residual_outputs=rows,output=out,operation_count=len(gates),
      operation_histogram={op:sum(n['op']==op for n in gates) for op in ['add','sub','mul']},
      propagated_degree_upper_bound=degree[out],
      count_convention='Each live binary addition, subtraction, or multiplication costs one; constant-only arithmetic is precomputed; all repeated nodes are shared.',
      polynomial_definitions={key:g.definitions[key] for key in g.regs},**extra)

def build(n):
    require(n in (13,14,15,16),'supported coordinate count')
    normalized=n<=14
    variables=['J6' if normalized else 'J3','C','z','h','r','v_scale','w3','c','T',
               'pair_root','pair_pos1','pair_pos2','pair_pos3','xi']
    if n>=15:variables.insert(3,'f')
    if n==16:variables.insert(9,'gamma')
    if n==13:
        variables=['c1' if v=='c' else v for v in variables if v!='pair_pos1']
    require(len(variables)==n,'coordinate count')
    d=definitions(normalized,n==13)
    g=DAG(variables,PORTS,d); a=Algebra(g)
    def r(x):return g.parse(x)
    j=[r('j0'),r('j1'),r('delta')]
    coeffs=a.padd(a.padd(a.pmul(j,j),a.pscale(a.scale(2,r('h0')),j)),[r('tail')])
    require(len(coeffs)==5,'quartic first-pair norm')
    original_coeffs=coeffs
    main_coeffs=None
    if n<=15:
        coeffs, gamma_pair=a.shift_and_norm(coeffs,a.lit(2),a.scale(-2,r('D0')),a.neg(r('M0')),r('H'))
        require(len(coeffs)==9,'degree-eight three-root norm')
        main_coeffs=list(coeffs)
    if n<=14:
        # Center f at (a+2)U: (f-f_center)^2 + 2 f_center
        # (f-f_center) + U^2-1 = 0, with no high-degree cancellation hidden.
        coeffs,f_pair=a.shift_and_norm(coeffs,a.lit(18),a.scale(-2,r('f_center')),r('1-U**2'))
        require(len(coeffs)==17,'degree-sixteen four-root norm')
    strong_norm_coeffs=list(coeffs)
    if n==13:
        coeffs,guard_pair=a.shift_and_norm(coeffs,a.lit(54),a.zero,r('Bguard'))
        require(len(coeffs)==33,'degree-thirty-two five-root norm')
    norm=a.peval(coeffs,r('xi'))
    guard=None if n==13 else r('G')
    if n==16:
        rows=[r('Main'),r('Strong'),guard,norm]
        out=g.sumsq(rows)
        finalizer='sum of squares of four residuals'
    elif n==15:
        rows=[r('Strong'),guard,norm]
        ss=g.sumsq(rows[:2])
        out=a.add(a.add(norm,ss),a.mul(norm,ss))
        finalizer='N + S + N*S, with S=Strong^2+G^2'
    elif n==14:
        rows=[guard,norm]
        gg=a.pow(guard,2)
        out=a.add(a.add(norm,gg),a.mul(norm,gg))
        finalizer='N + G^2 + N*G^2'
    else:
        rows=[norm];out=norm;finalizer='one norm polynomial'
    desc={16:'fixed3_crt_integer16',15:'three_root_integer15',14:'four_root_integer14',13:'five_root_integer13'}[n]
    packet=live_packet(g,out,rows,desc,dict(
      finalizer=finalizer,norm_output=norm,
      exact_degree={16:108,15:244,14:696,13:1392}[n],
      exact_norm_degree={16:54,15:156,14:608,13:1392}[n],
      exact_degree_proof='PROOF.md, Section 12; DEGREE_LOWER_CERTIFICATES.json',
      norm_coefficients_in_xi=coeffs,first_pair_coefficients_in_xi=original_coeffs,
      main_norm_coefficients_in_xi=main_coeffs,
      strong_norm_coefficients_in_xi=strong_norm_coeffs,
      coefficient_binding='coefficients/BINDING.json',
      proof_status='Ordinary arithmetic proof with identified inherited compiler and calibration results; no new end-to-end proof-assistant certificate.',
      normalizations={'first_root':'3*tau','auxiliary_root':'y',
        'main_root':'d/H' if n<=15 else 'separate gamma',
        'strong_root':'9*f, centered at 9*(a+2)*U' if n<=14 else 'separate f',
        'guard_root':'27*pair_pos1' if n==13 else 'separate guard'}))
    ROOT.joinpath(desc+'.json').write_text(json.dumps(packet,indent=2)+'\n')
    return {k:packet[k] for k in ['name','variable_count','operation_count','operation_histogram','propagated_degree_upper_bound']}

if __name__=='__main__':
    summary=[build(n) for n in (16,15,14,13)]
    ROOT.joinpath('BUILD_METRICS.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
