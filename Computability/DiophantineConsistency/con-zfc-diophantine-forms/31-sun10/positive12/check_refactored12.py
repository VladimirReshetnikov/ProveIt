"""Independent arithmetic diagnostics plus exact small polynomial identities.

The universal equivalence follows from REFACTORED12_PROOF.md; the finite
assignments here corroborate the transcription and do not decide Con(ZFC).
"""
import gzip
import hashlib
import json
import random
from collections import Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def value(x, env):
    return env[x] if isinstance(x,str) else x

def evaluate(packet, witnesses, coefficients, prime):
    env=dict(witnesses,**coefficients)
    for name,op,a,b in packet['source']:
        x,y=value(a,env),value(b,env)
        env[name]=({'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]())%prime
    return env

def audit_graph(packet):
    inputs=set(packet['witnesses']+packet['fixed_numerals'])
    known=set(inputs); definitions={}
    for name,op,a,b in packet['source']:
        require(name not in known, 'Duplicate node '+name)
        require(op in ('+','-','*'),'Invalid operation')
        require(all(not isinstance(x,str) or x in known for x in (a,b)), 'Forward reference')
        definitions[name]=(a,b); known.add(name)
    roots=[packet['output']] if 'output' in packet else [x for pair in packet['comparisons'] for x in pair if isinstance(x,str)]
    live=set();todo=roots[:]
    while todo:
        x=todo.pop()
        if x in live:continue
        live.add(x)
        todo.extend(y for y in definitions.get(x,()) if isinstance(y,str))
    require(live==known, 'Dead or missing names '+str(known-live))
    ledger=dict(operations=len(definitions),multiplications=sum(r[1]=='*' for r in packet['source']),
                additions_subtractions=sum(r[1]!='*' for r in packet['source']))
    require(ledger==packet['ledger'],'Wrong ledger')
    return ledger

# Small exact sparse polynomial ring; exponents are represented by sorted monomials.
class Poly:
    def __init__(self,terms):self.terms={m:c for m,c in terms.items() if c}
    @staticmethod
    def var(name):return Poly({(name,):1})
    @staticmethod
    def coerce(x):return x if isinstance(x,Poly) else Poly({():x})
    def __add__(self,other):
        other=self.coerce(other);d=Counter(self.terms)
        for m,c in other.terms.items():d[m]+=c
        return Poly(dict(d))
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.terms.items()})
    def __sub__(self,other):return self+(-self.coerce(other))
    def __rsub__(self,other):return self.coerce(other)+(-self)
    def __mul__(self,other):
        other=self.coerce(other);d=Counter()
        for m,c in self.terms.items():
            for n,e in other.terms.items():d[tuple(sorted(m+n))]+=c*e
        return Poly(dict(d))
    __rmul__=__mul__
    def __pow__(self,k):
        out=Poly({():1})
        for _ in range(k):out=out*self
        return out
    def __eq__(self,other):return self.terms==self.coerce(other).terms

def exact_identities():
    d,w,l,h,q,D,v,b,U,T,K=[Poly.var(x) for x in ['d','w','l','h','q','D','v','b','U','T','K']]
    require(d**2*(w-l)**2==(d*(w-l))**2,'Squared product identity')
    require(h**2*(q*(D*v**2))==(h**2*q)*(D*v**2),'Shared HP identity')
    require(h**2*(q*b**2)==(h**2*q)*b**2,'Shared HU identity')
    require(U**2+T*U*v+K*v**2==K*v**2-(-U)*(T*v-(-U)), 'Factored norm identity')
    k,w,c,qq,f,z=[Poly.var(x) for x in ['k','w','c','qq','f','z']]
    require((k+w)*c+qq-f-(z+1)*(qq-1)-1==(k+w)*c-f-z*(qq-1),'Transport shift identity')
    return 5

def main():
    names=['product108','system103','shifted_system102']
    packets={name:json.loads((HERE/'generated'/f'{name}.json').read_text()) for name in names}
    old=json.loads((HERE/'upstream/positive12_system.json').read_text())
    report={'exact_sparse_polynomial_identities':exact_identities(),
            'ledgers':{name:audit_graph(p) for name,p in packets.items()}}
    rng=random.Random(20261022); tested=0
    for prime in [251,65521,1000003]:
        for _ in range(80):
            w={name:rng.randrange(-20,21) for name in old['witnesses']}
            coeff={name:rng.randrange(-20,21) for name in old['fixed_numerals']}
            ref=evaluate(old,w,coeff,prime)
            new=evaluate(packets['product108'],w,coeff,prime)
            require(new['N']==ref['N'], 'Changed norm polynomial')
            require(new['polynomial']==(ref['Nk']*ref['Nt']*(1+ref['N'])-1)%prime,'Changed product polynomial')
            for name in ['system103','shifted_system102']:
                env=evaluate(packets[name],w,coeff,prime)
                shifted_w=dict(w,z=w['z']+1) if name=='shifted_system102' else w
                old_env=evaluate(old,shifted_w,coeff,prime)
                residuals=[(value(a,env)-value(b,env))%prime for a,b in packets[name]['comparisons']]
                require(residuals==[(old_env['Nk']-1)%prime,(old_env['Nt']-1)%prime,old_env['N']], 'System changed')
            tested+=1
    report['signed_modular_assignments']=tested
    binding=json.loads((HERE/'COEFFICIENT_BINDING.json').read_text())
    require(binding['instance']=='wang943-mixed-121x8801','Unexpected active tuple')
    coefficients={}; hashes={}
    for port,record in binding['coefficient_files'].items():
        raw=gzip.decompress((HERE/record['path']).read_bytes())
        digest=hashlib.sha256(raw).hexdigest()
        require(digest==record['sha256'],'Bad active coefficient '+port)
        require(int.from_bytes(raw,'little').bit_length()==record['bit_length'],'Bad port bit length')
        hashes[port]=digest
        coefficients[port]=int.from_bytes(raw,'little')%1000003
    for _ in range(12):
        w={name:rng.randrange(-20,21) for name in old['witnesses']}
        ref=evaluate(old,w,coefficients,1000003)
        new=evaluate(packets['product108'],w,coefficients,1000003)
        require(new['N']==ref['N'],'Changed active-instance norm')
        require(new['polynomial']==(ref['Nk']*ref['Nt']*(1+ref['N'])-1)%1000003,'Changed active-instance product')
    report['active_instance']=binding['instance']
    report['actual_coefficient_hashes']=hashes
    report['actual_instance_assignments']=12
    report['scope']='Exact local ring identities and circuit diagnostics; no proof-assistant endpoint build and no consistency decision.'
    (HERE/'CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
