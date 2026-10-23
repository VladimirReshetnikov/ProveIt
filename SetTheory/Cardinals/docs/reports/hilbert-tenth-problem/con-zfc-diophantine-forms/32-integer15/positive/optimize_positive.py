#!/usr/bin/env python3
"""Exact local circuit optimizations of the pinned positive12 polynomial.

Upstream files are read only as inert JSON arithmetic schedules. No upstream
program is imported. The three rewrites are proved as polynomial identities
below, then checked at signed finite-field points as an implementation audit.
"""
import argparse, copy, hashlib, json, os, random
from pathlib import Path

HERE=Path(__file__).resolve().parent
PIN='8c6eec9d19ef80538c8e61ff6e0180040583446a'

def check(cond, msg):
    if not cond: raise ValueError(msg)

def live_source(rows, outputs):
    live=set(outputs); out=[]
    for row in reversed(rows):
        n,op,a,b=row
        if n in live:
            out.append(row);live.update([a,b])
    return list(reversed(out))

def ledger(rows):
    return {'operations':len(rows),'multiplications':sum(r[1]=='*' for r in rows),
            'additions_subtractions':sum(r[1]!='*' for r in rows)}

def evaluate(rows, values, modulus=None):
    env=dict(values)
    for n,op,a,b in rows:
        x=a if isinstance(a,int) else env[a]
        y=b if isinstance(b,int) else env[b]
        z=x+y if op=='+' else x-y if op=='-' else x*y
        env[n]=z if modulus is None else z%modulus
    return env

def optimized(rows):
    out=[]
    for n,op,a,b in rows:
        if n=='HP':
            out += [['HQ','*','H2','Q'],['HP','*','HQ','g53']]
        elif n=='HU': out += [['HU','*','HQ','g55']]
        elif n=='Knorm':
            out += [['signed_knorm_root','*','d','g80'],
                    ['Knorm','*','signed_knorm_root','signed_knorm_root']]
        elif n=='N':
            out += [['trace_vr','*','Trace','vr'],
                    ['norm_horner_linear','+','ur','trace_vr'],
                    ['norm_horner_term','*','ur','norm_horner_linear'],
                    ['N','+','norm_horner_term','g106']]
        else: out.append([n,op,a,b])
    return live_source(out,['Nk','Nt','N'])

def emit(path,data):
    (HERE/path).write_text(json.dumps(data,indent=2)+'\n')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coefficient-binding',type=Path,
        default=HERE.parent/'compiler/coefficients/COEFFICIENT_BINDING.json',
        help='Replace the entire coefficient binding with this independently proved coherent tuple. Never splice individual ports.')
    args=parser.parse_args()
    src=HERE/'upstream/positive12_system.json'
    old=json.loads(src.read_text())
    rows=optimized(old['source'])
    check(len(old['source'])==107,'unexpected upstream operation count')
    check(len(rows)==104,'unexpected optimized count')
    data=copy.deepcopy(old)
    data.update(name='positive12_system104',source=rows,ledger=ledger(rows),
                proof='OPTIMIZATION_PROOF.md',source_pin=PIN,
                upstream_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),
                source_equivalence='Exactly the same three output polynomials as upstream; all four coefficient ports are symbolic in the identities.')
    if args.coefficient_binding is not None:
        raw=args.coefficient_binding.read_bytes()
        data['coefficient_binding']=json.loads(raw)
        data['coefficient_binding_file']=os.path.relpath(args.coefficient_binding.resolve(),HERE)
        data['binding_mode']='Complete tuple rebinding; arithmetic identities are universal in all four coefficient ports. The new tuple compiler theorem is a separate dependency.'
        data['binding_file_sha256']=hashlib.sha256(raw).hexdigest()
    emit('positive12_system104.json',data)
    prodrows=rows+[['unit_pair','*','Nk','Nt'],['norm_plus_one','+','N',1],
                  ['unit_product','*','unit_pair','norm_plus_one'],['polynomial','-','unit_product',1]]
    product=copy.deepcopy(data)
    product.pop('comparisons',None);product.pop('exact_degrees',None)
    product.update(name='positive12_product108',source=prodrows,output='polynomial',
                   exact_degree=1081,ledger=ledger(prodrows))
    emit('positive12_product108.json',product)
    # An existence-equivalent shifted system. z_old=z+1; equality comparisons
    # are uncharged, as in the source convention. The old polynomial above is
    # unchanged and does not use this coordinate shift.
    shifted=rows+[['shifted_transport_rhs','+','F','g41']]
    shifted=live_source(shifted,['Nk','N','g39','shifted_transport_rhs'])
    check(len(shifted)==103,'unexpected shifted count')
    shiftdata=copy.deepcopy(data)
    shiftdata.update(name='positive12_shifted_system103',source=shifted,
        comparisons=[['Nk',1],['g39','shifted_transport_rhs'],['N',0]],
        ledger=ledger(shifted),source_equivalence='Existence-equivalent after z_old=z_new+1; see strict-positivity argument in OPTIMIZATION_PROOF.md.')
    emit('positive12_shifted_system103.json',shiftdata)
    # Exhaustive coefficients in local identities, via a tiny sparse ring.
    # Each variable is a named indeterminate; equality is exact over Z.
    class P(dict):
        def __add__(self,b):
            b=const(b) if isinstance(b,int) else b;r=P(self)
            for m,c in b.items():r[m]=r.get(m,0)+c
            return P({m:c for m,c in r.items() if c})
        __radd__=__add__
        def __neg__(self):return P({m:-c for m,c in self.items()})
        def __sub__(self,b):return self+(-const(b) if isinstance(b,int) else -b)
        def __mul__(self,b):
            b=const(b) if isinstance(b,int) else b;r=P()
            for m,c in self.items():
                for n,d in b.items():
                    k=tuple(sorted(m+n));r[k]=r.get(k,0)+c*d
            return P({m:c for m,c in r.items() if c})
        __rmul__=__mul__
        def __pow__(self,n):
            out=const(1)
            for _ in range(n):out=out*self
            return out
    def const(v):return P({():v}) if v else P()
    def var(n):return P({(n,):1})
    h,q,d,v,b,w,l,u,tr,r,k=map(var,['h','q','d','v','b','w','l','u','tr','r','k'])
    identities=[h*(q*(d*v))-(h*q)*(d*v),h*(q*b**2)-(h*q)*b**2,
                d**2*(w-l)**2-(d*(w-l))**2,
                u**2+tr*u*r+k*r**2-(u*(u+tr*r)+k*r**2)]
    check(all(not x for x in identities),'exact polynomial identity failed')
    rng=random.Random(104108103);p=2147483647
    witness=old['witnesses'];ports=old['fixed_numerals']
    for _ in range(1000):
        values={name:rng.randrange(-p,p) for name in witness+ports}
        lhs=evaluate(old['source'],values,p);rhs=evaluate(rows,values,p)
        check(all(lhs[k]==rhs[k] for k in ['Nk','Nt','N']),'modular equivalence failed')
        shifted_values=dict(values);shifted_values['z']=values['z']-1
        se=evaluate(shifted,shifted_values,p)
        check((se['g39']-se['shifted_transport_rhs'])%p==(lhs['Nt']-1)%p,'transport shift failed')
    report={'status':'PASS','source_pin':PIN,'exact_local_polynomial_identities':4,
        'finite_field_signed_checks':1000,'modulus':p,
        'optimized_system':ledger(rows),'optimized_product':ledger(prodrows),
        'shifted_system':ledger(shifted),'unchanged_product_degree':1081,
        'unchanged_residual_degrees':old['exact_degrees'],
        'proof_scope':'Exact circuit rewrites and implementation audit. Inherited Pell/compiler/calibration proofs are not re-proved or machine-checked here.'}
    emit('OPTIMIZATION_CHECKS.json',report)
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
