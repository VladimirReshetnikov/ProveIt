#!/usr/bin/env python3
"""Experimental direct quartic with nonnegative square-difference gates."""
from pathlib import Path
import json,sys,hashlib,argparse
ROOT=Path(__file__).resolve().parents[1]
UP=ROOT/'upstream'
sys.path[:0]=[str(UP/'code'),str(UP/'provenance/upstream')]
import synchronized_builder as syn
from shared_product_power import SharedProductPowerBuilder
from direct_source_factored import source_pair_calculus as pair_source
from build_equation import ONE,ZERO,TWO,FOUR,write_json
from affine_contract import contract,independent_verify,polynomial_and_metrics

class NonnegativeBuilder(syn.DeferredBinomialMixin,SharedProductPowerBuilder):
    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs)
        self.sqd_cache={}
        self.sqd_ledger=[]

    def sqdiff(self,a,b):
        if a==b:return ZERO
        if a==ZERO:return self.square(b)
        if b==ZERO:return self.square(a)
        if a[0]==b[0]=='c':return ('c',(a[1]-b[1])**2)
        a,b=sorted((a,b))
        key=(a,b)
        if key not in self.sqd_cache:
            out=self.new('sqd.'+str(len(self.sqd_cache)),'square_difference')
            self.row([(1,[out]),(-1,[a,a]),(2,[a,b]),(-1,[b,b])],
                     'nonnegative_square_difference',out[1])
            self.sqd_cache[key]=out
            self.sqd_ledger.append({'output':list(out),'left':list(a),'right':list(b)})
        return self.sqd_cache[key]

def direct_source(b,source,env,index,include_label_slacks,codes_only=False):
    if not hasattr(b,'sqdiff') and not codes_only:
        return pair_source(b,source,env,index,include_label_slacks)
    add,mul,square,sd=b.add,b.mul,b.square,getattr(b,'sqdiff',None)
    def I(x,y):
        s=add(x,y)
        return add(mul(TWO,mul(s,add(s,ONE))),mul(FOUR,y))
    def A(x,y):return add(I(x,y),TWO)
    def M(x,y):return add(I(x,y),ONE)
    def E(x,y):return add(I(x,y),('c',3))
    def N(x):return I(x,ONE)
    def X(x,y):return N(A(x,N(y)))
    def req(x,k,h):return A(x,I(h,N(A(x,I(h,N(M(x,k)))))))
    def clos(x,y,k,h):
        s=A(k,I(M(k,x),M(k,y)))
        tail=I(s,req(y,k,h))
        tail=N(A(x,tail))
        tail=N(A(x,I(h,tail)))
        return A(y,I(M(y,k),tail))
    def bundle(x,y,z):
        nks=A(z,I(clos(x,y,z,z),N(req(y,z,z))))
        vrel=I(M(x,y),A(z,M(x,y)))
        return N(I(vrel,nks))
    a,c_b,c,d,p,q,v=[env[s] for s in ('a','b','c','d','p','q','v')]
    codes=[X(a,E(a,c_b)),I(A(a,I(c_b,c)),I(A(a,c_b),A(a,c))),
           I(E(a,c_b),I(M(c,a),M(c,c_b))),I(A(a,A(c_b,c)),A(c_b,A(a,c))),
           I(E(c,a),I(M(c,c_b),M(a,c_b))),I(X(a,A(a,c_b)),c_b),
           I(E(c,a),I(E(c,c_b),A(M(a,c_b),E(a,c_b)))),
           I(I(I(c,d),a),I(I(a,c),I(c_b,c))),bundle(a,c_b,c)]
    if codes_only:return {'codes':codes,'I':I,'A':A}
    guard=sd(mul(sd(c,a),sd(c,c_b)),square(add(d,ONE)))
    bundle_factor=add(sd(v,codes[-1]),guard)
    axis_squared=b.product([square(v)]+[sd(v,code) for code in codes[:-1]])
    axiom=add(add(square(p),square(q)),mul(axis_squared,bundle_factor))
    mp=sd(q,I(p,v))
    gen=add(square(q),sd(v,A(a,p)))
    horn=b.product([axiom,mp,gen])
    carrier=add(env['M0'],ONE)
    def weight(name):return add(ONE,mul(env[name],carrier))
    rows=[(mul(env['Sp'],weight('v')),b.product([env['S'],weight('p'),weight('q')]))]
    if include_label_slacks:
        rows += [(add(env[name],env['d'+name]),env['m']) for name in ('p','q','v')]
    den=add(mul(add(index,ONE),env['y']),ONE)
    rows += [(env['x'],add(env['S'],mul(den,env['u']))),
             (env['x'],add(env['Sp'],mul(add(den,env['y']),env['vq'])))]
    return b.sum([horn]+[sd(left,right) for left,right in rows]),ZERO

def generate(out, caps=(4,16,64)):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    syn.source_pair_calculus=direct_source
    sourcebytes=(UP/'provenance/upstream/wire_eliminated_source.json').read_bytes()
    b,cert=syn.construct(NonnegativeBuilder,json.loads(sourcebytes))
    eq,poly,metrics=b.export(hashlib.sha256(sourcebytes).hexdigest(),'nonnegative_functional_gates',True)
    write_json(out/'equation.json',eq);write_json(out/'expanded_polynomial.json',poly)
    write_json(out/'majorant_certificate.json',cert)
    write_json(out/'gate_ledger.json',{'square_difference_gates':b.sqd_ledger,
                'all_variables':b.variables,'all_rows':b.rows,'gates':b.gates})
    counts={'source':metrics}
    for cap in caps:
        target,cc=contract(eq,support_cap=cap,terminal_quadratic=True)
        receipt=independent_verify(eq,target,cc)
        pp,mm=polynomial_and_metrics(target['residuals'],len(target['variables']))
        dest=out/('cap'+str(cap));dest.mkdir(exist_ok=True)
        for name,item in [('equation.json',target),('expanded_polynomial.json',pp),
                          ('elimination_certificate.json',cc),('VERIFICATION.json',receipt)]:
            write_json(dest/name,item)
        counts[str(cap)]=mm
    write_json(out/'METRICS.json',counts)
    return counts

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    args=p.parse_args();print(json.dumps(generate(args.output),indent=2))
