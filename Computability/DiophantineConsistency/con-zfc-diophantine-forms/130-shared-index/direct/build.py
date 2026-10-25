#!/usr/bin/env python3
"""Compose the frozen unified binomial source with a single indexed Pell cap.

Research artifact with the ordinary proof in PROOF.md. Semantic indices from modular digit calls
are deliberately added to the frame; omitting them invalidates the cap.
"""
from pathlib import Path
from math import factorial
import argparse, hashlib, json, sys

HERE = Path(__file__).resolve().parent
DIRECT = HERE / 'source/shared_binomial'
sys.path.insert(0, str(DIRECT))
import build_modular_factorial as mf
h, dl, ONE, TWO, const = mf.h, mf.dl, mf.ONE, mf.TWO, mf.const
FOUR = const(4)


class CombinedBuilder(mf.ModularFactorialBuilder):
    radix_variant = 'power'
    denominator_shift = True
    merge_factorial = True
    pooled_residue = True
    global_cap = True
    self_radix = False

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.cap_parameters = None
        self.cap_bound_certificate = None
        self.cap_residue_certificate = None

    def finalize_binomials(self):
        if not self.self_radix:
            return super().finalize_binomials()
        if getattr(self, 'binomials_finalized', False):
            raise ValueError('repeated binomial finalization')
        self.binomials_finalized = True
        moduli = {item[2] for item in self.range_requests}
        if len(moduli) != 1:
            raise ValueError('one common amplified modulus required')
        N = next(iter(moduli))
        K = self.amplification_data['K']
        reps = getattr(self, 'aggregate_requests', self.range_requests)
        total = self.sum(n for n,_,_,_ in reps)
        base = self.add(total,ONE)
        q = self.mul(N,self.power(base,K))
        qb = self.add(q,ONE)
        for i,((n,k),out) in enumerate(self.binomials.items()):
            den = self.denominator(q,k)
            self.modular_requests.append({'kind':'exact','n':n,'k':k,'output':out,
                'den':den,'label':'choose'+str(i)})
        for n,k,modulus,label in self.range_requests:
            den = self.denominator(q,k)
            self.modular_requests.append({'kind':'divisible','n':n,'k':k,
                'den':den,'label':label})
        unique = list(dict.fromkeys(r['den'] for r in self.modular_requests))
        t = self.amplification_data['t']
        dt = self.power(q,t)
        dt1 = self.denominator(q,self.add(t,ONE))
        if dt in unique and dt1 in unique:
            unique.remove(dt)
        self.modular_root = self.product([q]+unique)
        _,A,_ = self._scale()
        root_quotient = self.new('modular.root_quotient')
        self.eq(self.product([TWO,A,qb]),
            self.sum([self.square(qb),ONE,self.mul(self.modular_root,root_quotient)]),
            'modular.common_root')
        self.radix_data = {'radix':q,'root_base':qb,'modulus':N,'K':K,
            'V':self.factorial_radix['numerator'],
            'representative_sum':total,'base':base,
            'kind':'N*(1+sum(representatives))^K',
            'aggregate_bound_removed':True,'independent_representatives':len(reps),
            'bootstrap':'V0 <= B*F < B^2 <= N < q before binomial interpretation',
            'exact_binomials':len(self.binomials),'range_binomials':len(self.range_requests),
            'root_modulus':self.modular_root,'root_denominators':unique,
            'omitted_denominator':dt,'dominating_denominator':dt1,
            'root_quotient':root_quotient}

    def _cap(self):
        if self.cap_parameters is not None:
            return self.cap_parameters
        W, A, _ = self._scale()
        tag = 'index_cap'
        X, Y, U, V, S, R = [self.new(tag + '.' + s) for s in ('X','Y','U','V','S','R')]
        if not self.global_cap:
            margin = self.new(tag + '.YminusW')
            self.eq(Y, self.add(W,margin), tag + '.index_at_most_Y')
        fourY = self.mul(FOUR, Y)
        q4minus1 = self.new(tag + '.q4minus1')
        B = self.add(ONE, self.mul(fourY, self.add(q4minus1, ONE)))
        self.norm(A, X, Y, tag + '.norm1')
        self.norm(A, U, V, tag + '.norm2')
        self.norm(B, S, R, tag + '.norm3')
        vd = self.new(tag + '.Vquotient_minus1')
        self.eq(V, self.mul(self.square(Y),self.add(vd,ONE)),tag + '.V_positive_multiple')
        bq, sq, rq = [self.new(tag + '.' + s) for s in ('Bquotient','Squotient','Rquotient')]
        self.eq(B, self.add(A,self.mul(U,bq)), tag + '.B_mod_U')
        self.eq(S, self.add(X,self.mul(U,sq)), tag + '.S_mod_U')
        self.eq(R, self.add(W,self.mul(fourY,rq)), tag + '.R_mod_4Y')
        self.cap_parameters = {'index':W,'base':A,'pair':(X,Y),
                               'auxiliary':(U,V,B),'comparison':(S,R)}
        return self.cap_parameters

    def _index(self, k):
        if k in self.shared_indices:
            return self.shared_indices[k]
        definition = self.index_definitions.get(k)
        if definition and definition[0] == 'add':
            _, a, b = definition
            if a[0] == 'c' and 0 < a[1] <= 2 and b in self.known_exponents:
                pair = self._combine(self._index(b),self._small_index(a[1]))
                self.shared_indices[k] = pair
                self.index_derivations.append({'kind':'shift','target':k,'source':b,'shift':a[1],'pair':pair})
                return pair
            if b[0] == 'c' and 0 < b[1] <= 2 and a in self.known_exponents:
                pair = self._combine(self._index(a),self._small_index(b[1]))
                self.shared_indices[k] = pair
                self.index_derivations.append({'kind':'shift','target':k,'source':a,'shift':b[1],'pair':pair})
                return pair
            if a in self.known_exponents and b in self.known_exponents:
                pair = self._combine(self._index(a),self._index(b))
                self.shared_indices[k] = pair
                self.index_derivations.append({'kind':'sum','target':k,'sources':[a,b],'pair':pair})
                return pair
        cap = self._cap()
        A, Ycap = cap['base'], cap['pair'][1]
        tag = 'index' + str(len(self.shared_indices))
        X,Y = self.new(tag + '.X'), self.new(tag + '.Y')
        self.norm(A,X,Y,tag + '.norm1')
        if not self.pooled_residue:
            quotient = self.new(tag + '.residue_quotient')
            self.row([(1,[Y]),(-1,[k]),(-1,[A,quotient]),(1,[quotient])],tag + '.index_mod_Aminus1')
        if not self.global_cap:
            slack = self.new(tag + '.cap_slack')
            self.eq(Ycap,self.sum([Y,slack,ONE]),tag + '.below_cap')
        self.shared_indices[k] = (X,Y)
        self.seed_indices[k] = (X,Y)
        return X,Y

    def finalize_power_frame(self):
        if self.shared_frame_finalized:
            return
        if self.power_indices_ready:
            raise ValueError('repeated index finalization')
        self.known_exponents = {k for _,k,_,_ in self.pending_powers} | {r['n'] for r in self.modular_requests}
        self.index_definitions = {out:key for key,out in self.cache.items()}
        W,A,_ = self._scale()
        self._cap()
        for n,k,m,tag in self.pending_powers:
            X,Y = self._index(k)
            T = self._base(n)
            quotient = self.new(tag + '.quotient')
            self.eq(self.add(X,self.mul(Y,n)),
                    self.sum([self.mul(Y,A),m,self.mul(T,quotient)]),tag + '.power_congruence')
            self.macro_log.append({'macro':'power','output':m,'base':n,'exponent':k,
                                   'shared_scale':True,'common_index_cap':True})
        q,qb,N = [self.radix_data[n] for n in ('radix','root_base','modulus')]
        for request in self.modular_requests:
            n,den,label = [request[n] for n in ('n','den','label')]
            X,Y = self._index(n)
            quotient,remainder,slack = [self.new(label + '.modular_' + s)
                for s in ('quotient','remainder','rslack')]
            modulus = self.mul(den,q if request['kind']=='exact' else N)
            residue = remainder
            if request['kind'] == 'exact':
                out = request['output']
                os = self.new(label + '.modular_oslack')
                residue = self.add(remainder,self.mul(den,out))
                self.eq(q,self.sum([out,os,ONE]),label + '.digit_bound')
            self.eq(self.add(X,self.mul(qb,Y)),
                    self.sum([self.mul(A,Y),residue,self.mul(modulus,quotient)]),label + '.modular_digit')
            self.eq(den,self.sum([remainder,slack,ONE]),label + '.remainder_bound')
            request.update({'pair':(X,Y),'quotient':quotient,'remainder':remainder,
                            'remainder_slack':slack,'modulus':modulus})
        self.power_indices_ready = True
        cc = self._cap()
        if self.global_cap:
            slack = self.new('index_cap.aggregate_slack')
            self.eq(cc['pair'][1],self.sum([W,ONE,slack]+[Y for X,Y in self.seed_indices.values()]),
                    'index_cap.all_indices_bound')
            self.cap_bound_certificate = {'index':W,'cap_ordinate':cc['pair'][1],
                'slack':slack,'ordinates':[Y for X,Y in self.seed_indices.values()],
                'row_label':'index_cap.all_indices_bound'}
        if self.pooled_residue:
            quotient = self.new('index_cap.error_square_quotient')
            terms = [(-1,[A,quotient]),(1,[quotient])]
            for k,(X,Y) in self.seed_indices.items():
                terms.extend([(1,[Y,Y]),(-2,[Y,k]),(1,[k,k])])
            self.row(terms,'index_cap.squared_index_errors')
            self.cap_residue_certificate = {'base':A,'quotient':quotient,
                'seeds':[{'exponent':k,'pair':pair} for k,pair in self.seed_indices.items()],
                'row_label':'index_cap.squared_index_errors'}
        self.index_product_finalized = True
        # Essential extension: every modular upper index must be < W.
        atoms = {a for (n,k),m in self.powers.items() for a in (n,k,m)} | {r['n'] for r in self.modular_requests}
        self.frame_atoms = sorted(atoms)
        self.eq(W,self.sum([TWO]+self.frame_atoms),'shared.frame_definition')
        self.shared_frame_finalized = True


def construct(syntax='cantor',horizon_minimum=12,budget_R=False):
    """Literal parent source, with the proved optional amplification K=R."""
    if not budget_R:
        return dl.construct(syntax=syntax,horizon_minimum=horizon_minimum)
    bp = dl.bp
    bp.ng.direct_source = h.CANTOR_SOURCE
    if syntax != 'cantor':
        h.shell_source.SHELL_SCHEME = syntax
        bp.ng.direct_source = h.shell_source.direct_source
    b = h.HybridBuilder(positive_powers=True)
    src = (bp.ng.UP/'provenance/upstream/wire_eliminated_source.json').read_bytes()
    source = json.loads(src)
    t = b.add(b.new('t0','outer'),const(horizon_minimum))
    x,y = [b.new(n,'outer') for n in ('x','y')]
    F = b.factorial(t)
    params = {'t':t,'x':x,'y':y,'F':F}
    u0,r0,ut = [b.new('endpoint.'+n) for n in ('u0','r0','ut')]
    dt = b.add(b.mul(b.add(t,ONE),y),ONE)
    b.eq(x,b.sum([F,ONE,b.mul(b.add(y,ONE),u0)]),'endpoint.first_quotient')
    b.eq(y,b.sum([F,r0,ONE]),'endpoint.first_remainder')
    b.eq(x,b.add(ONE,b.mul(dt,ut)),'endpoint.last_quotient')
    bounds = {n:t if i<4 else y if i<6 else x for i,n in enumerate(dl.LOCAL_NAMES)}
    encoded = {n:b.add(b.new('crt.encoded.'+n),ONE) for n in dl.LOCAL_NAMES}
    C = b.add(b.new('crt.encoded_index_minus_one'),ONE)
    bc = dl.majorants(source)
    E,ell = bc['emitted_exponent'],bc['derived_label_majorant']['emitted_exponent']
    Fmin = factorial(horizon_minimum)
    a = Fmin.bit_length()-1
    if not (a*E<2**a and 2*E<=2**a and 2*Fmin>=3*ell*(horizon_minimum+1)):
        raise ValueError('derived label/amplification budget requires reproof')
    R = b.sum([TWO,t,x,y,F])
    K = R
    B = b.moduli_product(t,F)
    T = b.product_data['square']
    N = b.power(B,K)
    b.amplification_data = {'B':B,'K':K,'N':N,'F':F,'t':t,'R':R,'index':C,
        'local_degree_bound':E,'label_degree_bound':ell,'budget':'R',
        'horizon_minimum':horizon_minimum,'index_precision':'K','completeness_precision':'2K',
        'floor_exponent':a,'factorial_floor':Fmin,
        'derived_label_radix_budget':'ell*(t+1)<=2F/3<F<R=K'}
    for n in dl.LOCAL_NAMES:
        b.divisible_binomial(encoded[n],b.add(bounds[n],ONE),N,'crt.range.'+n)
    b.divisible_binomial(C,t,N,'crt.range.index')
    b.aggregate_requests = list(b.range_requests)
    iq = b.new('crt.index_quotient')
    b.eq(b.sum([C,T,ONE]),b.mul(B,iq),'crt.reciprocal_index_congruence')
    value,labels = dl.source_and_labels(b,source,params|encoded,C)
    b.divisible_binomial(labels,b.add(t,ONE),N,'crt.range.derived_label_sum')
    b.amplification_data['derived_label_sum'] = labels
    quotient = b.new('crt.nonnegative_quotient')
    b.eq(value,b.mul(N,quotient),'crt.nonnegative_evaluation')
    b.finalize_binomials()
    b.finalize_power_frame()
    return b,src,bc


def generate(output, support_cap=32, sparse=False, syntax='cantor',self_radix=True,budget_R=True,horizon_minimum=12):
    out = Path(output)
    if out.exists() and any(out.iterdir()):
        raise ValueError('output must be empty')
    class Target(CombinedBuilder):
        pooled_residue = not sparse
        global_cap = not sparse
    Target.self_radix = self_radix
    if budget_R and not self_radix:
        raise ValueError('K=R requires the self-sized radix in this composition')
    old = h.HybridBuilder
    h.HybridBuilder = Target
    try:
        b,src,bc = construct(syntax,horizon_minimum,budget_R)
    finally:
        h.HybridBuilder = old
    equation,expanded,metrics = b.export(hashlib.sha256(src).hexdigest(),
        'unified_binomial_common_index_cap_'+syntax,True)
    cap_data = {'cap':b.cap_parameters,'aggregate':b.cap_bound_certificate,
        'residue':b.cap_residue_certificate,'semantic_frame_atoms':b.frame_atoms,
        'seed_count':len(b.seed_indices)}
    meta = {'powers':[{'base':n,'exponent':k,'output':v} for (n,k),v in b.powers.items()],
        'factorials':b.factorial_certificates,
        'binomials':[{'n':n,'k':k,'output':v} for (n,k),v in b.binomials.items()],
        'ranges':b.range_requests,'radix':b.radix_data,'product':b.product_data,
        'amplification':b.amplification_data,'scale':b.shared_parameters,
        'lower_A':b.scale_lower,'auxiliary':b.common_index_parameters,
        'discriminant':b.pell_D,'derivations':b.index_derivations,
        'denominator_derivations':b.denominator_derivations,
        'seeds':[{'exponent':k,'pair':v} for k,v in b.seed_indices.items()],
        'indices':[{'exponent':k,'pair':v} for k,v in b.shared_indices.items()],
        'modular_requests':b.modular_requests,'variables':b.variables,'rows':b.rows,
        'gates':b.gates,'local_majorant':bc,'syntax':syntax,'local_names':dl.LOCAL_NAMES,
        'cap_certificate':cap_data,
        'wire_eliminated_source_sha256':equation['wire_eliminated_source_sha256']}
    for name,obj in [('equation.json',equation),('expanded_polynomial.json',expanded),
        ('METRICS.json',metrics),('raw_audit_input.json',meta),('cap_certificate.json',cap_data),
        ('local_majorant.json',bc)]:
        h.write(out/'raw'/name,obj)
    target,cert,poly = h.psd.contract(equation,support_cap=support_cap)
    receipt,independent = h.check.verify(equation,target,cert)
    if poly['terms'] != independent:
        raise ValueError('independent polynomial mismatch')
    for name,obj in [('equation.json',target),('expanded_polynomial.json',poly),
        ('elimination_certificate.json',cert),('VERIFICATION.json',receipt)]:
        h.write(out/'natural'/name,obj)
    counts = {'source':metrics,'natural':receipt,'syntax':syntax,
        'support_cap':support_cap,'sparse':sparse,'power_calls':len(b.powers),
        'seed_indices':len(b.seed_indices),'derived_indices':len(b.index_derivations),
        'modular_requests':len(b.modular_requests),'exact_binomials':len(b.binomials),
        'range_binomials':len(b.range_requests),'factorials':len(b.factorials),
        'semantic_frame_atoms':len(b.frame_atoms),'self_radix':self_radix,
        'budget_R':budget_R,'horizon_minimum':horizon_minimum}
    h.write(out/'SUMMARY.json',counts)
    return counts


if __name__ == '__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--support-cap',type=int,default=32)
    p.add_argument('--sparse',action='store_true')
    p.add_argument('--self-radix',action=argparse.BooleanOptionalAction,default=True)
    p.add_argument('--budget-R',action=argparse.BooleanOptionalAction,default=True)
    p.add_argument('--horizon-minimum',type=int,default=12)
    p.add_argument('--syntax',choices=['cantor','xx0','xy0'],default='cantor')
    a=p.parse_args()
    print(json.dumps(generate(a.output,a.support_cap,a.sparse,a.syntax,a.self_radix,
        a.budget_R,a.horizon_minimum),indent=2))
