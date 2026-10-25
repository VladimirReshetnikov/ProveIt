#!/usr/bin/env python3
"""Combine a single indexed Pell cap with the six-power modular compiler.

Deterministic constructor. All exported variables are natural.
Inherited arithmetic is loaded read-only from an explicitly specified source.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

sys.dont_write_bytecode = True


def construct(upstream, output, syntax='cantor', support_cap=64,
              dominant=False, coordinates='standard', protected=(),
              semantic_anchor=False):
    upstream, output = Path(upstream).resolve(), Path(output).resolve()
    if semantic_anchor and syntax != 'cantor':
        raise ValueError('The semantic-anchor completeness proof is for the Cantor source.')
    sys.path.insert(0, str(upstream / 'direct'))
    import build_modular_factorial as mf
    h, dl = mf.h, mf.dl
    ONE, TWO, const = h.ONE, h.TWO, h.const
    FOUR = const(4)

    class CombinedBuilder(mf.ModularFactorialBuilder):
        radix_variant = 'power'
        denominator_shift = True
        merge_factorial = True

        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)
            self.cap_parameters = None
            self.cap_residue_certificate = None
            self.cap_bound_certificate = None
            self.seed_certificates = []

        def finalize_binomials(self):
            super().finalize_binomials()
            if semantic_anchor:
                # In completeness, shift the encoded a-column by N^2. Its
                # congruences are preserved, and all nine representatives
                # then have sum at most 10N^2. This makes the derived label
                # index J dominate every other requested index.
                N = self.radix_data['modulus']
                aggregate = self.radix_data['aggregate_slack']
                records = getattr(self,'aggregate_requests',self.range_requests)
                for row_index,row in enumerate(self.rows):
                    if row['label']=='crt.aggregate_representative_bound':
                        break
                else:
                    raise ValueError('missing aggregate representative bound')
                self.eq(self.mul(const(10),self.square(N)),
                    self.add(self.sum(n for n,_,_,_ in records),aggregate),
                    'crt.aggregate_representative_bound')
                self.rows[row_index] = self.rows.pop()
                self.radix_data.update(aggregate_factor=10,bound='10*N^2',
                    completeness_lift='encoded a increased by N^2')
            if dominant:
                # Replace only the common-root row and its defining product.
                # Dead inherited product gates are removed by the exporter.
                q = self.radix_data['radix']
                N = self.radix_data['modulus']
                xi = [i for i,v in enumerate(self.variables) if v['name']=='x']
                if len(xi)!=1:
                    raise ValueError('expected one outer x coordinate')
                x = ('v',xi[0])
                dx = self.denominator(q, self.add(x, ONE))
                oldroot = self.modular_root
                self.modular_root = self.mul(N, dx)
                _, A, _ = self._scale()
                qb = self.radix_data['root_base']
                quotient = self.radix_data['root_quotient']
                # The equality row is not a gate. Rewrite it at emission time.
                for row_index,row in enumerate(self.rows):
                    if row['label'] == 'modular.common_root':
                        break
                else:
                    raise ValueError('missing root row')
                self.eq(self.product([TWO,A,qb]),
                    self.sum([self.square(qb),ONE,self.mul(self.modular_root,quotient)]),
                    'modular.common_root')
                # Preserve every earlier gate->row index. Only the last
                # nongate equality is moved to replace the inherited row.
                self.rows[row_index] = self.rows.pop()
                self.radix_data.update(root_modulus=self.modular_root,
                    old_root_modulus=oldroot, dominant_denominator=dx,
                    root_kind='N*q^(x+1)')

        def _cap(self):
            if self.cap_parameters is not None:
                return self.cap_parameters
            W,A,_ = self._scale()
            H = self.amplification_data['derived_label_sum'] if semantic_anchor else W
            tag = 'index_cap'
            X,Y,U,V,S,R = [self.new(tag+'.'+s) for s in ('X','Y','U','V','S','R')]
            fourY = self.mul(FOUR,Y)
            q4minus1 = self.new(tag+'.q4minus1')
            B = self.add(ONE,self.mul(fourY,self.add(q4minus1,ONE)))
            self.norm(A,X,Y,tag+'.norm1')
            self.norm(A,U,V,tag+'.norm2')
            self.norm(B,S,R,tag+'.norm3')
            vd = self.new(tag+'.Vquotient_minus1')
            self.eq(V,self.mul(self.square(Y),self.add(vd,ONE)),tag+'.V_positive_multiple')
            bq,sq,rq = [self.new(tag+'.'+s) for s in ('Bquotient','Squotient','Rquotient')]
            self.eq(B,self.add(A,self.mul(U,bq)),tag+'.B_mod_U')
            self.eq(S,self.add(X,self.mul(U,sq)),tag+'.S_mod_U')
            self.eq(R,self.add(H,self.mul(fourY,rq)),tag+'.R_mod_4Y')
            self.cap_parameters = dict(index=H,base=A,pair=(X,Y),
                auxiliary=(U,V,B),comparison=(S,R))
            return self.cap_parameters

        def _index(self,k):
            if k in self.shared_indices:
                return self.shared_indices[k]
            cap = self._cap()
            if semantic_anchor and k==cap['index']:
                self.shared_indices[k] = cap['pair']
                return cap['pair']
            A = cap['base']
            tag = 'index'+str(len(self.shared_indices))
            Y = self.new(tag+'.Y')
            if coordinates == 'standard':
                X = self.new(tag+'.X')
                self.norm(A,X,Y,tag+'.norm1')
                pair = X,Y
                record = dict(index=k,first=X,ordinate=Y,kind='standard',label=tag+'.norm1')
            elif coordinates == 'consecutive':
                Z = self.new(tag+'.previous_Y')
                product = self.mul(Y,Z)
                self.row([(1,[Y,Y]),(1,[Z,Z]),(-2,[A,product]),(-1,[])],tag+'.consecutive_norm')
                pair = Z,Y
                record = dict(index=k,first=Z,ordinate=Y,kind='consecutive',
                    product=product,label=tag+'.consecutive_norm')
            else:
                raise ValueError('unknown coordinate mode')
            self.shared_indices[k] = pair
            self.seed_indices[k] = pair
            self.seed_certificates.append(record)
            return pair

        def residue_equation(self,pair,base,terms,label):
            first,Y = pair
            if coordinates == 'standard' or pair==self.cap_parameters['pair']:
                A = self._scale()[1]
                self.eq(self.add(first,self.mul(Y,base)),
                    self.sum([self.mul(Y,A)]+terms),label)
            else:
                self.eq(self.mul(Y,base),self.sum([first]+terms),label)

        def finalize_power_frame(self):
            if self.shared_frame_finalized:
                return
            if self.power_indices_ready:
                raise ValueError('partial repeated finalization')
            W,A,_ = self._scale()
            cap = self._cap()
            for n,k,m,tag in self.pending_powers:
                pair = self._index(k)
                modulus = self._base(n)
                quotient = self.new(tag+'.quotient')
                self.residue_equation(pair,n,[m,self.mul(modulus,quotient)],tag+'.power_congruence')
                self.macro_log.append(dict(macro='power',output=m,base=n,exponent=k,
                    shared_scale=True,common_index_cap=True))
            q,qb,N = [self.radix_data[n] for n in ('radix','root_base','modulus')]
            for request in self.modular_requests:
                n,den,label = [request[n] for n in ('n','den','label')]
                pair = self._index(n)
                quotient,remainder,slack = [self.new(label+'.modular_'+s)
                    for s in ('quotient','remainder','rslack')]
                modulus = self.mul(den,q if request['kind']=='exact' else N)
                residue = remainder
                if request['kind']=='exact':
                    out = request['output']
                    os = self.new(label+'.modular_oslack')
                    residue = self.add(remainder,self.mul(den,out))
                    self.eq(q,self.sum([out,os,ONE]),label+'.digit_bound')
                self.residue_equation(pair,qb,[residue,self.mul(modulus,quotient)],label+'.modular_digit')
                self.eq(den,self.sum([remainder,slack,ONE]),label+'.remainder_bound')
                request.update(pair=pair,quotient=quotient,remainder=remainder,
                    remainder_slack=slack,modulus=modulus)
            slack = self.new('index_cap.aggregate_slack')
            ordinates = [Y for first,Y in self.seed_indices.values()]
            self.eq(cap['pair'][1],self.sum([cap['index'],ONE,slack]+ordinates),'index_cap.all_indices_bound')
            quotient = self.new('index_cap.error_square_quotient')
            terms = [(-1,[A,quotient]),(1,[quotient])]
            for k,(first,Y) in self.seed_indices.items():
                terms.extend([(1,[Y,Y]),(-2,[Y,k]),(1,[k,k])])
            self.row(terms,'index_cap.squared_index_errors')
            # Modular top indices were absent from the six-power-only frame.
            # Including them is necessary for sound simultaneous index recovery.
            atoms = {a for (n,k),m in self.powers.items() for a in (n,k,m)}
            atoms |= {r['n'] for r in self.modular_requests}
            # q is already an exact-power atom. The positive offset gives
            # q+1 < W, so the residue base qb needs no extra frame atom.
            offset = len(self.seed_indices)+2
            self.eq(W,self.sum([const(offset)]+sorted(atoms)),'shared.frame_definition')
            self.cap_bound_certificate = dict(index=cap['index'],cap_ordinate=cap['pair'][1],
                slack=slack,ordinates=ordinates,row_label='index_cap.all_indices_bound')
            self.cap_residue_certificate = dict(base=A,quotient=quotient,
                seeds=[dict(exponent=k,pair=pair) for k,pair in self.seed_indices.items()],
                row_label='index_cap.squared_index_errors')
            self.frame_certificate = dict(atoms=sorted(atoms),offset=offset,index=W,
                lower_A=self.scale_lower,base=A,modular_tops=[r['n'] for r in self.modular_requests])
            self.power_indices_ready = self.index_product_finalized = self.shared_frame_finalized = True

    old = h.HybridBuilder
    h.HybridBuilder = CombinedBuilder
    try:
        b,source,majorant = dl.construct(syntax=syntax,horizon_minimum=16)
    finally:
        h.HybridBuilder = old
    eq,expanded,metrics = b.export(hashlib.sha256(source).hexdigest(),
        'pooled_cap_six_power_'+coordinates+'_'+syntax,True)
    protected_indices = [i for i,v in enumerate(eq['variables']) if v['name'] in protected]
    if len(protected_indices)!=len(protected):
        raise ValueError('a protected coordinate was not found')
    target,certificate,polynomial = h.psd.contract(eq,support_cap=support_cap,
        protected_variables=protected_indices)
    receipt,independent = h.check.verify(eq,target,certificate)
    if polynomial['terms'] != independent:
        raise ValueError('coefficient expansion disagrees with independent checker')
    meta = dict(powers=[dict(base=n,exponent=k,output=m) for (n,k),m in b.powers.items()],
        factorials=b.factorial_certificates,
        binomials=[dict(n=n,k=k,output=v) for (n,k),v in b.binomials.items()],
        ranges=b.range_requests,radix=b.radix_data,product=b.product_data,
        amplification=b.amplification_data,scale=b.shared_parameters,lower_A=b.scale_lower,
        cap=b.cap_parameters,cap_bound=b.cap_bound_certificate,cap_residue=b.cap_residue_certificate,
        frame=b.frame_certificate,seed_certificates=b.seed_certificates,
        denominator_derivations=b.denominator_derivations,modular_requests=b.modular_requests,
        variables=b.variables,rows=b.rows,gates=b.gates,local_majorant=majorant,
        syntax=syntax,local_names=dl.LOCAL_NAMES,
        wire_eliminated_source_sha256=eq['wire_eliminated_source_sha256'],
        coordinates=coordinates,dominant_modulus=dominant,semantic_anchor=semantic_anchor)
    for name,obj in [('equation.json',eq),('expanded_polynomial.json',expanded),
                     ('METRICS.json',metrics),('semantic.json',meta),('local_majorant.json',majorant)]:
        h.write(output/'raw'/name,obj)
    for name,obj in [('equation.json',target),('expanded_polynomial.json',polynomial),
                     ('elimination_certificate.json',certificate),('VERIFICATION.json',receipt)]:
        h.write(output/'natural'/name,obj)
    summary = dict(source=metrics,natural=receipt,power_calls=len(b.powers),
        modular_requests=len(b.modular_requests),seed_indices=len(b.seed_indices),
        coordinates=coordinates,dominant_modulus=dominant,syntax=syntax,
        support_cap=support_cap,frame_offset=b.frame_certificate['offset'],
        protected_coordinates=list(protected),semantic_anchor=semantic_anchor)
    h.write(output/'SUMMARY.json',summary)
    return summary


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--upstream',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--syntax',choices=['cantor','xx0','xy0'],default='cantor')
    p.add_argument('--support-cap',type=int,default=64)
    p.add_argument('--dominant',action='store_true')
    p.add_argument('--coordinates',choices=['standard','consecutive'],default='standard')
    p.add_argument('--protect',action='append',default=[])
    p.add_argument('--semantic-anchor',action='store_true')
    a=p.parse_args()
    print(json.dumps(construct(a.upstream,a.output,a.syntax,a.support_cap,a.dominant,a.coordinates,a.protect,a.semantic_anchor),indent=2))
