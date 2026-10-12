"""Replay finite certificates and cutoff identities using exact rational arithmetic."""
from pathlib import Path
from functools import lru_cache
from fractions import Fraction as F
from collections import defaultdict
from itertools import combinations
import ast,json
import sympy as sp
from research import N,G,Z,A,C,comps,linearize,tail_words,mixed_moment,moment
from reduce_values import reduce
from pair_formula import pair_value,telescoper_residual
ROOT=Path(__file__).resolve().parents[1]

@lru_cache(None)
def stuffle_independent(u,v):
    if not u:return {v:F(1)}
    if not v:return {u:F(1)}
    result=defaultdict(F)
    for head,uu,vv in ((u[0],u[1:],v),(v[0],u,v[1:]),(u[0]+v[0],u[1:],v[1:])):
        for w,c in stuffle_independent(uu,vv).items():result[(head,)+w]+=c
    return dict(result)

def add(u,v,scale=F(1)):
    out=defaultdict(F,u)
    for w,c in v.items():out[w]+=scale*c
    return {w:c for w,c in out.items() if c}

def mul(u,v):
    out={}
    for a,c in u.items():
        for b,d in v.items():out=add(out,stuffle_independent(a,b),c*d)
    return out

def parse_expression(text):
    """Restricted arithmetic parser; no eval or executable input is accepted."""
    def read(node):
        if isinstance(node,ast.Constant) and isinstance(node.value,int):return {():F(node.value)}
        if isinstance(node,ast.Name) and node.id.startswith('Z_'):
            w=tuple(map(int,node.id[2:].split('_')))
            if w[0]<2 or any(a<1 for a in w):raise ValueError(w)
            return {w:F(1)}
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return {w:-c for w,c in read(node.operand).items()}
        if isinstance(node,ast.BinOp):
            a=read(node.left)
            if isinstance(node.op,ast.Pow):
                if not isinstance(node.right,ast.Constant) or not isinstance(node.right.value,int) or node.right.value<0:raise ValueError('Exponent')
                r={():F(1)}
                for _ in range(node.right.value):r=mul(r,a)
                return r
            b=read(node.right)
            if isinstance(node.op,ast.Add):return add(a,b)
            if isinstance(node.op,ast.Sub):return add(a,b,F(-1))
            if isinstance(node.op,ast.Mult):return mul(a,b)
            if isinstance(node.op,ast.Div) and set(b)=={()} and b[()]!=0:return {w:c/b[()] for w,c in a.items()}
        raise ValueError('Expression is outside the permitted rational/MZV grammar')
    return read(ast.parse(text,mode='eval').body)

def encode(w):return sum(((0,)*(p-1)+(1,) for p in w),())
def decode(w):
    ans=[];p=1
    for bit in w:
        if bit==0:p+=1
        else:ans.append(p);p=1
    if p!=1:raise ValueError('Word must end in 1')
    return tuple(ans)

def shuffle_by_positions(u,v):
    a,b=encode(u),encode(v);out=defaultdict(F)
    for chosen in combinations(range(len(a)+len(b)),len(a)):
        chosen=set(chosen);i=j=0;w=[]
        for k in range(len(a)+len(b)):
            if k in chosen:w.append(a[i]);i+=1
            else:w.append(b[j]);j+=1
        out[decode(tuple(w))]+=1
    return dict(out)

def relation(label):
    kind=label[0];u=tuple(label[1])
    if kind=='ds':return add(stuffle_independent(u,tuple(label[2])),shuffle_by_positions(u,tuple(label[2])),F(-1))
    if kind=='dual':
        v=decode(tuple(1-b for b in reversed(encode(u))))
        return add({u:F(1)},{v:F(-1)})
    raise ValueError(kind)

@lru_cache(None)
def harmonic(w,Ncut):
    if not w:return F(1)
    return sum((F(n)**(-w[0])*harmonic(w[1:],n) for n in range(1,Ncut)),F(0))

def run():
    checks=[];cert_results=[]
    def check(name,condition):
        assert condition,name
        checks.append(name)
    for name in ('J7','K8','K9'):
        obj=json.loads((ROOT/'certificates'/f'{name}_certificate.json').read_text())
        target=parse_expression(obj['target']); result=parse_expression(obj['result']);comb={}
        for term in obj['relation_terms']:
            r=relation(term['label'])
            check(f'{name} admissible relation {len(checks)}',all(w[0]>=2 and all(a>0 for a in w) for w in r))
            comb=add(comb,r,F(term['coefficient']))
        residual=add(add(target,result,F(-1)),comb,F(-1))
        check(f'{name} exact rational certificate',not residual)
        damaged=add(target,{(obj['weight'],):F(1)})
        check(f'{name} changed coefficient rejected',bool(add(add(damaged,result,F(-1)),comb,F(-1))))
        from double_shuffle import relations
        _, rebuilt, _=relations(obj['weight'])
        check(f'{name} exact recorded rank',len(rebuilt.T.rref()[1])==obj['rank'])
        cert_results.append({'name':name,'nonzero_relation_terms':len(obj['relation_terms']),'matrix_rows':obj['matrix_rows'],'matrix_columns':obj['matrix_columns'],'recorded_rank':obj['rank'],'residual':'exactly zero','corruption_control':'rejected'})
    # Independent finite harmonic and centered Faulhaber checks.
    for w in ((2,),(3,),(2,2),(2,3),(3,2),(2,2,2)):
        for m in range(7):
            poly=(sp.bernoulli(m+1,N+sp.Rational(1,2))-sp.bernoulli(m+1,sp.Rational(1,2)))/sp.Integer(m+1)
            coeff=sp.Poly(poly,N)
            for NN in (2,4,7):
                lhs=sum((F(2*n+1,2)**m*harmonic(w,n+1) for n in range(NN)),F(0))
                rhs=F(poly.subs(N,NN))*harmonic(w,NN)-sum((F(c)*harmonic((w[0]-h[0],)+w[1:],NN) for h,c in coeff.terms()),F(0))
                check(f'finite centered sum {w} {m} {NN}',lhs==rhs)
    for ps in ((2,3),(3,3),(2,2,3),(2,3,4)):
        tw=tail_words(ps)
        for NN in (2,5,8):
            # Rational arbitrary totals replace zeta constants; this is a polynomial identity.
            totals={Z((p,)):sp.Rational(7+p,3+p) for p in ps}
            lhs=sp.prod(totals[Z((p,))]-sp.Rational(harmonic((p,),NN)) for p in ps)
            rhs=sum(c.subs(totals)*sp.Rational(harmonic(w,NN)) for w,c in tw.items())
            check(f'finite product {ps} {NN}',sp.expand(lhs-rhs)==0)
    # Euler-constant cancellation and parity-refined weight bounds.
    table=[]
    for ps in ((2,),(3,),(4,),(2,2),(2,3),(3,3),(2,2,3),(2,3,4),(2,2,2),(2,2,2,2),(2,2,2,2,2)):
        R=sum(p-1 for p in ps);W=sum(ps)
        for m in range(R%2,10,2):
            expr=linearize(mixed_moment(ps,m))
            check(f'no Euler constant {ps} {m}',not expr.has(G))
            bound=W-(2 if m%2 else 1)
            weights=[sum(map(int,str(z)[2:].split('_'))) for z in expr.free_symbols if str(z).startswith('Z_')]
            check(f'weight ceiling {ps} {m}',all(w<=bound for w in weights))
            if len(ps)<=3 and W<=9:
                table.append({'orders':ps,'degree':m,'subtraction':'see article formula (regular centered subtraction)','MZV_expression':str(expr),'reduced_expression':str(reduce(expr))})
    for d in range(1,6):
        for m in range(d%2,10,2):
            check(f'equal-order independent expansion d={d} m={m}',linearize(mixed_moment((2,)*d,m)-moment(d,m))==0)
    # A normalization trap and two elementary nonzero checks.
    check('exclusive cutoff H_0 has CT -1',C((0,))==-1)
    check('single trigamma moment M_1,1=-1/4',linearize(mixed_moment((2,),1))==-sp.Rational(1,4))
    check('mixed first moment',reduce(mixed_moment((2,3),1))==(Z((2,))+Z((3,)))/2)
    for m in range(1,16,2):
        check(f'independent (2,3) formula m={m}',reduce(mixed_moment((2,3),m))==pair_value(m))
    check('rational -15 telescoper',telescoper_residual()==0)
    check('rational -15 combination',sp.expand(23*pair_value(1)+232*pair_value(3)+240*pair_value(5))==-15)
    result={'status':'passed','number_of_checks':len(checks),'certificate_checks':cert_results,'checks':checks,'proof_assistant_formalization':False}
    (ROOT/'results'/'exact.json').write_text(json.dumps(result,indent=2))
    (ROOT/'results'/'mixed_moments.json').write_text(json.dumps(table,indent=2))
    print('Exact checks passed:',len(checks),flush=True)
    return result
if __name__=='__main__':run()
