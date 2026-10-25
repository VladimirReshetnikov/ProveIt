#!/usr/bin/env python3
"""Compose the shared factorial binomial with one Pell cap and pooled errors.

All variables are nonnegative integers. The semantic frame explicitly
includes the modular numerator indices as well as all exact-power ports.
"""
from pathlib import Path
import argparse, json, sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'incoming/shared319/direct'))
import build_modular_factorial as M
sys.path.insert(0,str(HERE/'incoming/cap261/portable/source/custom'))
import capped_pell as C
h=M.h
ONE,TWO=M.ONE,M.TWO
Original=M.ModularFactorialBuilder

class CappedModularBuilder(Original):
    global_cap=True
    pooled_residue=True
    use_additive_indices=True
    merged_cap=False
    recover_x=False
    latest=None
    _cap=C.CappedHybrid._cap
    _index=C.CappedHybrid._index

    def __init__(self,*args,**kw):
        super().__init__(*args,**kw)
        self.cap_parameters=None
        self.cap_residue_certificate=None
        self.cap_bound_certificate=None
        CappedModularBuilder.latest=self

    def finalize_power_frame(self):
        if self.shared_frame_finalized:return
        if not self.power_indices_ready:
            self.known_exponents={k for _,k,_,_ in self.pending_powers}|{r['n'] for r in self.modular_requests}
            self.index_definitions={out:key for key,out in self.cache.items()}
            _,A,_=self._scale()
            self._cap()
            for n,k,m,tag in self.pending_powers:
                X,Y=self._index(k);T=self._base(n)
                quotient=self.new(tag+'.quotient')
                self.eq(self.add(X,self.mul(Y,n)),self.sum([self.mul(Y,A),m,self.mul(T,quotient)]),tag+'.power_congruence')
                self.macro_log.append({'macro':'power','output':m,'base':n,'exponent':k,'shared_scale':True,'common_index_cap':True})
            q,qb,N=[self.radix_data[n] for n in ('radix','root_base','modulus')]
            for request in self.modular_requests:
                n,den,label=[request[n] for n in ('n','den','label')]
                X,Y=self._index(n)
                quotient,remainder,slack=[self.new(label+'.modular_'+s) for s in ('quotient','remainder','rslack')]
                modulus=self.mul(den,q if request['kind']=='exact' else N)
                residue=remainder
                if request['kind']=='exact':
                    out=request['output'];os=self.new(label+'.modular_oslack')
                    residue=self.add(remainder,self.mul(den,out))
                    self.eq(q,self.sum([out,os,ONE]),label+'.digit_bound')
                self.eq(self.add(X,self.mul(qb,Y)),self.sum([self.mul(A,Y),residue,self.mul(modulus,quotient)]),label+'.modular_digit')
                self.eq(den,self.sum([remainder,slack,ONE]),label+'.remainder_bound')
                request.update({'pair':(X,Y),'quotient':quotient,'remainder':remainder,'remainder_slack':slack,'modulus':modulus})
            self.power_indices_ready=True
            cc=self._cap()
            if not self.merged_cap:
                slack=self.new('index_cap.aggregate_slack')
                self.eq(cc['pair'][1],self.sum([cc['index'],ONE,slack]+[Y for X,Y in self.seed_indices.values()]),'index_cap.all_indices_bound')
                self.cap_bound_certificate={'index':cc['index'],'cap_ordinate':cc['pair'][1],'slack':slack,'ordinates':[Y for X,Y in self.seed_indices.values()],'row_label':'index_cap.all_indices_bound'}
            quotient=self.new('index_cap.error_square_quotient')
            terms=[(-1,[A,quotient]),(1,[quotient])]
            if self.merged_cap:
                terms.extend([(1,[cc['pair'][1]]),(-1,[cc['index']])])
            for k,(X,Y) in self.seed_indices.items():
                terms.extend([(-1,[Y,Y]),(2,[Y,k]),(-1,[k,k])] if self.merged_cap else [(1,[Y,Y]),(-2,[Y,k]),(1,[k,k])])
                if self.recover_x:
                    if not self.merged_cap:raise ValueError('abscissa recovery requires merged cap')
                    terms.extend([(-1,[X,X]),(2,[X]),(-1,[])])
            row_label='index_cap.merged_bound_errors' if self.merged_cap else 'index_cap.squared_index_errors'
            self.row(terms,row_label)
            self.cap_residue_certificate={'base':A,'quotient':quotient,'seeds':[{'exponent':k,'pair':pair} for k,pair in self.seed_indices.items()],'row_label':row_label,'recover_x':self.recover_x}
        self.index_product_finalized=True
        power_atoms={a for (n,k),m in self.powers.items() for a in (n,k,m)}
        modular_indices={r['n'] for r in self.modular_requests}
        atoms=power_atoms|modular_indices
        W,_,_=self._scale()
        total=self.sum([TWO]+sorted(atoms))
        self.eq(W,self.mul(TWO,total) if self.merged_cap else total,'shared.frame_definition')
        self.frame_certificate={'exact_power_atoms':sorted(power_atoms),'modular_indices':sorted(modular_indices),'all_atoms':sorted(atoms),'frame':W,'factor':2 if self.merged_cap else 1,'row_label':'shared.frame_definition'}
        self.shared_frame_finalized=True

def generate(out,syntax='cantor',cap=64,merged=False,recover_x=False):
    out=Path(out)
    M.ModularFactorialBuilder=CappedModularBuilder
    CappedModularBuilder.merged_cap=merged
    CappedModularBuilder.recover_x=recover_x
    oldcontract=h.psd.contract
    h.psd.contract=lambda equation,support_cap=64:oldcontract(equation,support_cap=cap)
    try:
        result=M.generate(out,syntax,'power',True,True)
    finally:
        M.ModularFactorialBuilder=Original
        h.psd.contract=oldcontract
    b=CappedModularBuilder.latest
    cc={'cap':b.cap_parameters,'aggregate':b.cap_bound_certificate,'residue':b.cap_residue_certificate,'frame':b.frame_certificate,'seed_count':len(b.seed_indices),'theorem':'one indexed cap, shared modular binomial, pooled index errors'}
    h.write(out/'raw/cap_certificate.json',cc)
    meta=json.loads((out/'raw/raw_audit_input.json').read_text());meta['cap_certificate']=cc
    h.write(out/'raw/raw_audit_input.json',meta)
    result.update({'combined_common_cap':True,'support_cap':cap,'modular_index_frame':True,'merged_cap':merged,'recover_x':recover_x})
    h.write(out/'SUMMARY.json',result)
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--syntax',choices=['cantor','xx0'],default='cantor');ap.add_argument('--cap',type=int,default=64);ap.add_argument('--merged',action='store_true');ap.add_argument('--recover-x',action='store_true');a=ap.parse_args()
    print(json.dumps(generate(a.out,a.syntax,a.cap,a.merged,a.recover_x),indent=2))
