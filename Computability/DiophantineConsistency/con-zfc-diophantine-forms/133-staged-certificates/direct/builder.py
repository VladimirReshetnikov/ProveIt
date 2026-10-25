#!/usr/bin/env python3
"""Shared cap for exact powers AND modular binomial numerator indices."""
from pathlib import Path
import sys,json,argparse
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'upstream'))
import build_modular_factorial as mf
h,ONE,TWO=mf.h,mf.ONE,mf.TWO
FOUR=('c',4)
const=mf.const

class Combined(mf.ModularFactorialBuilder):
    global_cap=True
    pooled_residue=True
    use_additive_indices=True
    latest=None
    staged=False
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

    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs)
        self.cap_parameters=None
        self.cap_bound_certificate=None
        self.cap_residue_certificate=None
        Combined.latest=self
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
        dominant = next(r['den'] for r in self.modular_requests if r['label']=='crt.range.u')
        self.modular_root = self.mul(N,dominant)
        _, A, _ = self._scale()
        root_quotient = self.new('modular.root_quotient')
        self.eq(self.product([TWO,A,qb]),
            self.sum([self.square(qb),ONE,self.mul(self.modular_root,root_quotient)]),
            'modular.common_root')
        self.radix_data = {'radix':q,'root_base':qb,'modulus':N,'K':K,'V':V,
            'aggregate_count':count,'aggregate_slack':aggregate,'kind':kind,
            'bound':'count*N^2','exact_binomials':len(self.binomials),
            'range_binomials':len(self.range_requests),
            'root_modulus':self.modular_root,'root_denominators':[dominant],
            'omitted_denominator':dt,'dominating_denominator':dominant, 'root_kind':'N*D_x; dominant endpoint denominator',
            'root_quotient':root_quotient}

    def finalize_power_frame(self):
        if self.shared_frame_finalized:return
        if not self.power_indices_ready:
            self.known_exponents={k for _,k,_,_ in self.pending_powers}|{r['n'] for r in self.modular_requests}
            self.index_definitions={out:key for key,out in self.cache.items()}
            _,A,_=self._scale()
            self._cap()
            for n,k,m,tag in self.pending_powers:
                X,Y=self._index(k); T=self._base(n)
                quotient=self.new(tag+'.quotient')
                self.eq(self.add(X,self.mul(Y,n)),self.sum([self.mul(Y,A),m,self.mul(T,quotient)]),tag+'.power_congruence')
                self.macro_log.append({'macro':'power','output':m,'base':n,'exponent':k,'shared_scale':True,'common_index_cap':True})
            q,qb,N=[self.radix_data[n] for n in ('radix','root_base','modulus')]
            for request in self.modular_requests:
                n,den,label=[request[key] for key in ('n','den','label')]
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
            slack=self.new('index_cap.aggregate_slack')
            self.eq(cc['pair'][1],self.sum([cc['index'],ONE,slack]+[Y for X,Y in self.seed_indices.values()]),'index_cap.all_indices_bound')
            quotient=self.new('index_cap.error_square_quotient')
            if self.staged:
                first={k for n,k,m,tag in self.pending_powers}|{r['n'] for r in self.modular_requests if r['kind']=='exact'}
                groups=[[(k,p) for k,p in self.seed_indices.items() if k in first],[(k,p) for k,p in self.seed_indices.items() if k not in first]]
            else:groups=[list(self.seed_indices.items())]
            group_data=[]
            for i,group in enumerate(groups):
                qi=quotient if i==0 else self.new('index_cap.range_error_quotient')
                terms=[(-1,[A,qi]),(1,[qi])]
                for k,(X,Y) in group:
                    terms.extend([(1,[Y,Y]),(-2,[Y,k]),(1,[k,k])])
                self.row(terms,'index_cap.squared_index_errors.'+str(i))
                group_data.append({'quotient':qi,'seeds':[{'exponent':k,'pair':p} for k,p in group]})
            self.cap_groups=group_data
            self.cap_bound_certificate={'index':cc['index'],'cap_ordinate':cc['pair'][1],'slack':slack,'ordinates':[Y for X,Y in self.seed_indices.values()]}
            self.cap_residue_certificate={'base':A,'groups':group_data}
        atoms={a for (n,k),m in self.powers.items() for a in (n,k,m)}|{r['n'] for r in self.modular_requests if not self.staged}
        W,_,_=self._scale()
        self.eq(W,self.sum([TWO]+sorted(atoms)),'shared.frame_definition')
        self.index_product_finalized=True
        self.shared_frame_finalized=True
        self.frame_atoms=sorted(atoms)


def generate(out,syntax='cantor',support_cap=20,staged=True):
    Combined.staged=staged
    old=mf.ModularFactorialBuilder
    old_contract=h.psd.contract
    actual_cap=support_cap
    def contract(equation,support_cap=64):return old_contract(equation,support_cap=actual_cap)
    h.psd.contract=contract
    mf.ModularFactorialBuilder=Combined
    try:result=mf.generate(out,syntax,'power',True,True)
    finally:
        mf.ModularFactorialBuilder=old
        h.psd.contract=old_contract
    b=Combined.latest
    data={'cap':b.cap_parameters,'bound':b.cap_bound_certificate,'residue':b.cap_residue_certificate,'frame_atoms':b.frame_atoms,'seeds':len(b.seed_indices),'modular_indices_in_frame':not staged,'staged':staged,'groups':b.cap_groups}
    h.write(Path(out)/'raw/cap_certificate.json',data)
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();print(json.dumps(generate(a.output),indent=2))
