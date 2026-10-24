#!/usr/bin/env python3
"""One certified Pell index cap replaces all individual index-comparison pairs."""
from pathlib import Path
import argparse,json,sys
from frame_environment import BASE,dl,h,bp,ONE,TWO,FOUR


class CappedHybrid(h.HybridBuilder):
    global_cap=True
    pooled_residue=True
    use_additive_indices=True
    latest=None

    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs)
        self.cap_parameters=None
        self.cap_residue_certificate=None
        self.cap_bound_certificate=None
        CappedHybrid.latest=self

    def _cap(self):
        if self.cap_parameters is not None:
            return self.cap_parameters
        W,A,_=self._scale()
        tag='index_cap'
        X,Y,U,V,S,R=[self.new(tag+'.'+s) for s in ('X','Y','U','V','S','R')]
        if not self.global_cap:
            margin=self.new(tag+'.YminusW')
            self.eq(Y,self.add(W,margin),tag+'.index_at_most_Y')
        fourY=self.mul(FOUR,Y)
        q4minus1=self.new(tag+'.q4minus1')
        B=self.add(ONE,self.mul(fourY,self.add(q4minus1,ONE)))
        self.norm(A,X,Y,tag+'.norm1')
        self.norm(A,U,V,tag+'.norm2')
        self.norm(B,S,R,tag+'.norm3')
        vd=self.new(tag+'.Vquotient_minus1')
        self.eq(V,self.mul(self.square(Y),self.add(vd,ONE)),tag+'.V_positive_multiple')
        bq,sq,rq=[self.new(tag+'.'+s) for s in ('Bquotient','Squotient','Rquotient')]
        self.eq(B,self.add(A,self.mul(U,bq)),tag+'.B_mod_U')
        self.eq(S,self.add(X,self.mul(U,sq)),tag+'.S_mod_U')
        self.eq(R,self.add(W,self.mul(fourY,rq)),tag+'.R_mod_4Y')
        self.cap_parameters={'index':W,'base':A,'pair':(X,Y),'auxiliary':(U,V,B),'comparison':(S,R)}
        return self.cap_parameters

    def _index(self,k):
        if k in self.shared_indices:
            return self.shared_indices[k]
        definition=self.index_definitions.get(k) if self.use_additive_indices else None
        if definition and definition[0]=='add':
            _,a,b=definition
            if a[0]=='c' and 0<a[1]<=2 and b in self.known_exponents:
                pair=self._combine(self._index(b),self._small_index(a[1]))
                self.shared_indices[k]=pair
                self.index_derivations.append({'kind':'shift','target':k,'source':b,'shift':a[1],'pair':pair})
                return pair
            if b[0]=='c' and 0<b[1]<=2 and a in self.known_exponents:
                pair=self._combine(self._index(a),self._small_index(b[1]))
                self.shared_indices[k]=pair
                self.index_derivations.append({'kind':'shift','target':k,'source':a,'shift':b[1],'pair':pair})
                return pair
            if a in self.known_exponents and b in self.known_exponents:
                pair=self._combine(self._index(a),self._index(b))
                self.shared_indices[k]=pair
                self.index_derivations.append({'kind':'sum','target':k,'sources':[a,b],'pair':pair})
                return pair
        cap=self._cap();A=cap['base'];Vcap=cap['pair'][1]
        tag='index'+str(len(self.shared_indices))
        names=['X','Y']
        if not self.pooled_residue:names.append('residue_quotient')
        if not self.global_cap:names.append('cap_slack')
        local={name:self.new(tag+'.'+name) for name in names}
        X,Y=local['X'],local['Y']
        self.norm(A,X,Y,tag+'.norm1')
        if not self.pooled_residue:
            q=local['residue_quotient']
            self.row([(1,[Y]),(-1,[k]),(-1,[A,q]),(1,[q])],tag+'.index_mod_Aminus1')
        if not self.global_cap:
            s=local['cap_slack']
            self.eq(Vcap,self.sum([Y,s,ONE]),tag+'.below_cap')
        self.shared_indices[k]=(X,Y)
        self.seed_indices[k]=(X,Y)
        return X,Y

    def finalize_power_frame(self):
        if self.shared_frame_finalized:return
        if not self.power_indices_ready:
            self.known_exponents={k for _,k,_,_ in self.pending_powers}
            self.index_definitions={out:key for key,out in self.cache.items()}
            _,A,_=self._scale()
            self._cap()
            for n,k,m,tag in self.pending_powers:
                X,Y=self._index(k)
                T=self._base(n)
                quotient=self.new(tag+'.quotient')
                self.eq(self.add(X,self.mul(Y,n)),self.sum([self.mul(Y,A),m,self.mul(T,quotient)]),tag+'.power_congruence')
                self.macro_log.append({'macro':'power','output':m,'base':n,'exponent':k,'shared_scale':True,'common_index_cap':True})
            self.power_indices_ready=True
            if self.global_cap:
                cc=self._cap()
                slack=self.new('index_cap.aggregate_slack')
                self.eq(cc['pair'][1],self.sum([cc['index'],ONE,slack]+[Y for X,Y in self.seed_indices.values()]),
                        'index_cap.all_indices_bound')
                self.cap_bound_certificate={'index':cc['index'],'cap_ordinate':cc['pair'][1],
                                            'slack':slack,'ordinates':[Y for X,Y in self.seed_indices.values()],
                                            'row_label':'index_cap.all_indices_bound'}
            if self.pooled_residue:
                _,A,_=self._scale()
                quotient=self.new('index_cap.error_square_quotient')
                terms=[(-1,[A,quotient]),(1,[quotient])]
                for k,(X,Y) in self.seed_indices.items():
                    terms.extend([(1,[Y,Y]),(-2,[Y,k]),(1,[k,k])])
                self.row(terms,'index_cap.squared_index_errors')
                self.cap_residue_certificate={'base':A,'quotient':quotient,
                    'seeds':[{'exponent':k,'pair':pair} for k,pair in self.seed_indices.items()],
                    'row_label':'index_cap.squared_index_errors'}
        # The cap's independent index certificate replaces the former
        # auxiliary multiple of all principal ordinate squares.
        self.index_product_finalized=True
        super().finalize_power_frame()


def generate(out,syntax='cantor',horizon_minimum=16,cap=96,self_radix=False,budget_R=False,no_derived=False,sparse=False):
    if self_radix:
        sys.path.insert(0,str(Path(__file__).resolve().parent))
        import build_self_radix as sr
        class Target(CappedHybrid):
            finalize_binomials=sr.SelfRadixBuilder.finalize_binomials
    else:
        Target=CappedHybrid
    class RunTarget(Target):
        use_additive_indices=not no_derived
        global_cap=not sparse
        pooled_residue=not sparse
    Target=RunTarget
    old=h.HybridBuilder;old_contract=h.psd.contract
    h.HybridBuilder=Target
    def contract(equation,support_cap=64):
        return old_contract(equation,support_cap=cap)
    h.psd.contract=contract
    try:
        if budget_R:
            sys.path.insert(0,str(Path(__file__).resolve().parent))
            import build_radix_R as rr
            result=rr.generate(out,syntax,horizon_minimum,builder=Target)
        else:
            result=dl.generate(out,syntax,horizon_minimum)
    finally:
        h.HybridBuilder=old;h.psd.contract=old_contract
    result['common_index_cap']=True;result['global_cap']=not sparse
    result['pooled_residue']=not sparse
    result['self_radix']=self_radix;result['budget_R']=budget_R;result['support_cap']=cap
    result['all_exponents_are_seeds']=no_derived
    h.write(Path(out)/'SUMMARY.json',result)
    b=CappedHybrid.latest
    cap_data={'cap':b.cap_parameters,'aggregate':b.cap_bound_certificate,
              'residue':b.cap_residue_certificate,
              'semantic_frame_atoms':sorted({a for (n,k),m in b.powers.items() for a in (n,k,m)}),
              'seed_count':len(b.seed_indices),
              'theorem':('one indexed cap with individual range and residue rows' if sparse else
                         'one indexed cap, one aggregate bound, one sum-of-squares congruence')}
    h.write(Path(out)/'raw'/'cap_certificate.json',cap_data)
    meta_path=Path(out)/'raw'/'raw_audit_input.json'
    meta=json.loads(meta_path.read_text());meta['cap_certificate']=cap_data
    h.write(meta_path,meta)
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    p.add_argument('--syntax',choices=['cantor','xx0','xy0'],default='cantor')
    p.add_argument('--horizon-minimum',type=int,default=16);p.add_argument('--cap',type=int,default=96)
    p.add_argument('--self-radix',action='store_true')
    p.add_argument('--budget-R',action='store_true')
    p.add_argument('--no-derived',action='store_true')
    p.add_argument('--sparse',action='store_true')
    a=p.parse_args()
    print(json.dumps(generate(a.output,a.syntax,a.horizon_minimum,a.cap,a.self_radix,a.budget_R,a.no_derived,a.sparse),indent=2))
