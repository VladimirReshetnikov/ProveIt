#!/usr/bin/env python3
"""Compose the factorial-carrier CRT architecture with common Pell residues.

The frozen input is imported read-only. New files are written only beneath
the explicit output directory. All final variables are nonnegative integers.
"""
from pathlib import Path
import argparse, hashlib, json, sys

HERE = Path(__file__).resolve().parent
UPSTREAM = HERE.parent / 'round14'
sys.path.insert(0, str(UPSTREAM / 'architecture'))
import build_derived_label_range as dl
import build_factorial_carrier as fc
h = dl.h
ONE, TWO, const = h.ONE, h.TWO, h.const


class ModularFactorialBuilder(h.HybridBuilder):
    denominator_shift = True
    radix_variant = 'inherited'
    merge_factorial = False

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.modular_requests = []
        self.denominator_derivations = []

    def factorial(self,n):
        if not self.merge_factorial:
            return super().factorial(n)
        if n in self.factorials:
            return self.factorials[n]
        if self.factorials:
            raise ValueError('the merged architecture uses exactly one factorial')
        if self.radix_variant != 'power':
            raise ValueError('merged bootstrap requires the independently bounded power radix')
        F = self.new('fact0.output')
        self.factorials[n] = F
        top = self.new('fact0.square_minus1')
        self.eq(self.add(top,ONE),self.square(F),'fact0.square_minus1_definition')
        rho = self.add(top,ONE)
        B = self.new('reciprocal.B')
        self.binomials[(top,n)] = B
        self.macro_log.append({'macro':'binomial','output':B,'n':top,'k':n})
        V = self.power(top,n)
        remainder,slack = self.new('fact0.remainder'),self.new('fact0.slack')
        self.eq(V,self.add(self.mul(B,F),remainder),'fact0.floor')
        self.eq(B,self.sum([remainder,slack,ONE]),'fact0.remainder_bound')
        self.macro_log.append({'macro':'factorial','output':F,'n':n,
            'descending_binomial_floor':True,'shares_binomial_with_reciprocal_crt':True})
        self.factorial_certificates.append({'input':n,'output':F,'radius':rho,
            'binomial':B,'numerator':V,'remainder':remainder,'slack':slack,
            'selfbounding':'descending_floor_t_at_least_3_F_at_least_2'})
        self.factorial_radix={'H':n,'rho':rho,'numerator':V,'factorial':F}
        return F

    def _scale(self):
        if self.shared_parameters is None:
            W, L, slack, zm1 = [self.new('shared.' + n)
                for n in ('W', 'lower_A', 'A_slack', 'Zminus1')]
            A, Z = self.add(L, slack), self.add(zm1, ONE)
            self.norm(self.add(W, ONE), L, self.mul(W, Z), 'shared.last_norm_lower')
            self.shared_parameters = W, A, Z
            self.scale_lower = L
        return self.shared_parameters

    def denominator(self, q, k):
        t = self.amplification_data['t']
        if self.denominator_shift and k == self.add(t, ONE):
            result = self.mul(q, self.power(q, t))
            if not any(v['output'] == result for v in self.denominator_derivations):
                self.denominator_derivations.append({'base': q, 'exponent': k,
                    'output': result, 'source_exponent': t, 'kind': 'multiply_by_base'})
            return result
        return self.power(q, k)

    def moduli_product(self, t, F):
        if self.radix_variant != 'power':
            return super().moduli_product(t, F)
        n = ('v',next(i for i,v in enumerate(self.variables) if v['name']=='fact0.square_minus1'))
        T = self.add(n,ONE)
        if (n,t) in self.binomials:
            out = self.binomials[(n,t)]
        else:
            out = self.add(self.new('reciprocal.Bminus2'), TWO)
            self.binomials[(n,t)] = out
            self.macro_log.append({'macro':'binomial', 'output':out, 'n':n, 'k':t})
        self.product_data = {'horizon':t, 'factorial':F, 'square':T, 'product':out,
                             'positive_guard':'B = remainder+slack+1; power and floor force B>F>=2'}
        return out

    def finalize_binomials(self):
        if getattr(self, 'binomials_finalized', False):
            raise ValueError('repeated binomial finalization')
        self.binomials_finalized = True
        moduli = {item[2] for item in self.range_requests}
        if len(moduli) != 1:
            raise ValueError('one common amplified modulus required')
        N = next(iter(moduli))
        K = self.amplification_data['K']
        aggregate_requests = getattr(self, 'aggregate_requests', self.range_requests)
        count = len(aggregate_requests)
        aggregate = self.new('crt.aggregate_representative_slack')
        self.eq(self.mul(const(count), self.square(N)),
                self.add(self.sum(n for n, _, _, _ in aggregate_requests), aggregate),
                'crt.aggregate_representative_bound')
        V = self.factorial_radix['numerator']
        if self.radix_variant == 'power':
            q = self.power(N,K)
            kind = 'N^K with B >= 2'
        else:
            q = self.mul(N, self.power(self.sum([N,V,ONE]),K))
            kind = 'N*(N+V+1)^K'
        qb = self.add(q,ONE)
        for i, ((n,k),out) in enumerate(self.binomials.items()):
            den = self.denominator(q,k)
            self.modular_requests.append({'kind':'exact','n':n,'k':k,'output':out,
                'den':den, 'label':'choose'+str(i)})
        for n,k,modulus,label in self.range_requests:
            den = self.denominator(q,k)
            self.modular_requests.append({'kind':'divisible','n':n,'k':k,
                'den':den,'label':label})
        # This finite product replaces a new large-denominator power request.
        # Repeated lower indices share their existing exact denominator.
        unique = list(dict.fromkeys(r['den'] for r in self.modular_requests))
        t = self.amplification_data['t']
        dt = self.power(q,t)
        dt1 = self.denominator(q,self.add(t,ONE))
        # q^t divides q^(t+1), so omit the former from the root modulus.
        if dt in unique and dt1 in unique:
            unique.remove(dt)
        self.modular_root = self.product([q]+unique)
        _, A, _ = self._scale()
        root_quotient = self.new('modular.root_quotient')
        self.eq(self.product([TWO,A,qb]),
            self.sum([self.square(qb),ONE,self.mul(self.modular_root,root_quotient)]),
            'modular.common_root')
        self.radix_data = {'radix':q,'root_base':qb,'modulus':N,'K':K,'V':V,
            'aggregate_count':count,'aggregate_slack':aggregate,'kind':kind,
            'bound':'count*N^2','exact_binomials':len(self.binomials),
            'range_binomials':len(self.range_requests),
            'root_modulus':self.modular_root,'root_denominators':unique,
            'omitted_denominator':dt,'dominating_denominator':dt1,
            'root_quotient':root_quotient}

    def finalize_power_frame(self):
        if self.shared_frame_finalized:
            return
        if not self.power_indices_ready:
            self.known_exponents = {k for _,k,_,_ in self.pending_powers} | \
                                   {r['n'] for r in self.modular_requests}
            self.index_definitions = {out:key for key,out in self.cache.items()}
            _,A,_ = self._scale()
            for n,k,m,tag in self.pending_powers:
                X,Y = self._index(k)
                T = self._base(n)
                quotient = self.new(tag+'.quotient')
                self.eq(self.add(X,self.mul(Y,n)),
                    self.sum([self.mul(Y,A),m,self.mul(T,quotient)]),tag+'.power_congruence')
                self.macro_log.append({'macro':'power','output':m,'base':n,'exponent':k,
                    'shared_scale':True,'index_addition':True})
            q,qb,N = [self.radix_data[n] for n in ('radix','root_base','modulus')]
            for request in self.modular_requests:
                n,den,label = [request[n] for n in ('n','den','label')]
                X,Y = self._index(n)
                quotient,remainder,slack = [self.new(label+'.modular_'+s)
                    for s in ('quotient','remainder','rslack')]
                modulus = self.mul(den,q if request['kind']=='exact' else N)
                residue = remainder
                if request['kind']=='exact':
                    out = request['output']
                    os = self.new(label+'.modular_oslack')
                    residue = self.add(remainder,self.mul(den,out))
                    self.eq(q,self.sum([out,os,ONE]),label+'.digit_bound')
                self.eq(self.add(X,self.mul(qb,Y)),
                    self.sum([self.mul(A,Y),residue,self.mul(modulus,quotient)]),
                    label+'.modular_digit')
                self.eq(den,self.sum([remainder,slack,ONE]),label+'.remainder_bound')
                request.update({'pair':(X,Y),'quotient':quotient,'remainder':remainder,
                    'remainder_slack':slack,'modulus':modulus})
            self.power_indices_ready = True
        if not self.index_product_finalized:
            U,V,B = self._auxiliary_index()
            productY2 = self.product([self.square(Y) for X,Y in self.seed_indices.values()])
            vm1 = self.new('shared_index.Vquotient_minus1')
            self.eq(V,self.mul(productY2,self.add(vm1,ONE)),'shared_index.V_positive_product')
            self.index_product_finalized = True
        atoms = {a for (n,k),m in self.powers.items() for a in (n,k,m)}
        W,_,_ = self._scale()
        self.eq(W,self.sum([TWO]+sorted(atoms)),'shared.frame_definition')
        self.shared_frame_finalized = True


def generate(out, syntax='cantor', variant='inherited', shift=True, merge=False):
    out = Path(out)
    if out.exists() and any(out.iterdir()):
        raise ValueError('output directory must be empty')
    ModularFactorialBuilder.radix_variant = variant
    ModularFactorialBuilder.denominator_shift = shift
    ModularFactorialBuilder.merge_factorial = merge
    h.HybridBuilder = ModularFactorialBuilder
    b,src,bc = dl.construct(syntax=syntax, horizon_minimum=16)
    equation,expanded,metrics = b.export(hashlib.sha256(src).hexdigest(),
        'factorial_carrier_modular_pell_residues_'+syntax,True)
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
        'wire_eliminated_source_sha256':equation['wire_eliminated_source_sha256']}
    for name,obj in [('equation.json',equation),('expanded_polynomial.json',expanded),
                     ('METRICS.json',metrics),('raw_audit_input.json',meta),
                     ('local_majorant.json',bc)]:
        h.write(out/'raw'/name,obj)
    target,cert,poly = h.psd.contract(equation,support_cap=64)
    receipt,independent = h.check.verify(equation,target,cert)
    if poly['terms'] != independent:
        raise ValueError('independent expanded polynomial mismatch')
    for name,obj in [('equation.json',target),('expanded_polynomial.json',poly),
                     ('elimination_certificate.json',cert),('VERIFICATION.json',receipt)]:
        h.write(out/'natural'/name,obj)
    counts={'source':metrics,'natural':receipt,'syntax':syntax,'variant':variant,
        'merged_factorial_crt_binomial':merge,
        'power_calls':len(b.powers),'seed_indices':len(b.seed_indices),
        'derived_indices':len(b.index_derivations),'modular_requests':len(b.modular_requests),
        'denominator_derivations':len(b.denominator_derivations),
        'exact_binomials':len(b.binomials),'range_binomials':len(b.range_requests),
        'factorials':len(b.factorials),'local_degree_bound':bc['emitted_exponent']}
    h.write(out/'SUMMARY.json',counts)
    return counts


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--syntax',choices=['cantor','xx0','xy0'],default='cantor')
    p.add_argument('--radix',choices=['inherited','power'],default='inherited')
    p.add_argument('--no-denominator-shift',action='store_true')
    p.add_argument('--merge-factorial',action='store_true')
    a=p.parse_args()
    print(json.dumps(generate(a.output,a.syntax,a.radix,not a.no_denominator_shift,
                             a.merge_factorial),indent=2))
