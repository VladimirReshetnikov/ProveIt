"""Standard-library finite checks; no semantic compiler proof asserted.

All verification gates use explicit exceptions and remain active under -O/-OO.
"""
import json,random,gzip,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parent
p=json.loads((ROOT/'p12_desaturated_product.json').read_text())
old=json.loads((ROOT/'upstream/positive12_none_lean_product.json').read_text())

def require(condition,message):
    if not condition:
        raise ValueError(message)

def trim(a):
    n=len(a)
    while n>1 and a[n-1]==0:
        n-=1
    return a[:n]

def poly_mul(a,b,mod):
    """Exact modular convolution by carry-free Kronecker packing.

    The coefficients are residues in [0, mod-1]. Every unreduced product
    coefficient is at most min(len(a),len(b))*(mod-1)**2. Choose a byte
    width whose base 256**width is STRICTLY larger than that bound. Packing
    a polynomial as its value at this base, multiplying the two integers,
    and unpacking therefore recovers every convolution coefficient with
    no carries between positions. Reduction modulo mod happens afterwards.
    Python integers are exact, so no machine-word overflow is involved.
    """
    require(mod>=2 and len(a)>0 and len(b)>0,'Invalid convolution input')
    require(all(0<=v<mod for v in a+b),'Convolution coefficients are not residues')
    bound=min(len(a),len(b))*(mod-1)**2
    width=max(1,(bound.bit_length()+7)//8)
    pa=int.from_bytes(b''.join(v.to_bytes(width,'little') for v in a),'little')
    pb=int.from_bytes(b''.join(v.to_bytes(width,'little') for v in b),'little')
    count=len(a)+len(b)-1
    raw=(pa*pb).to_bytes(width*count,'little')
    return trim([int.from_bytes(raw[j:j+width],'little')%mod
                 for j in range(0,len(raw),width)])

def check_convolution():
    """Deterministic implementation cross-checks against a separate naive loop."""
    cases=0
    for mod in [2,3,17,257,10007,10037]:
        fixtures=[([0],[0]),([mod-1],[mod-1]),
                  ([mod-1]*17,[mod-1]*8),
                  ([(j*j+3*j+1)%mod for j in range(31)],
                   [(7*j*j+2*j)%mod for j in range(23)])]
        for a,b in fixtures:
            expected=[0]*(len(a)+len(b)-1)
            for i,u in enumerate(a):
                for j,v in enumerate(b):
                    expected[i+j]=(expected[i+j]+u*v)%mod
            require(poly_mul(a,b,mod)==trim(expected),
                    f'Kronecker convolution mismatch modulo {mod}')
            cases+=1
    return cases

def run_poly(mod,seed,fixed=None):
    rng=random.Random(seed)
    vals={v:[rng.randrange(1,mod),rng.randrange(1,mod)] for v in p['witnesses']}
    vals.update({v:[fixed[v]%mod if fixed is not None else rng.randrange(1,mod)] for v in p['fixed_numerals']})
    def get(x):return [x%mod] if isinstance(x,int) else vals[x]
    for name,op,x,y in p['source']:
        a,b=get(x),get(y)
        if op=='*':r=poly_mul(a,b,mod)
        else:
            require(op in ['+','-'],f'Unknown polynomial operator {op}')
            r=[0]*max(len(a),len(b))
            for j,u in enumerate(a):r[j]=u
            for j,v in enumerate(b):r[j]=(r[j]+(v if op=='+' else -v))%mod
        vals[name]=trim(r)
    return {'coefficient_mode':'actual_fixed_tuple' if fixed is not None else 'formal_port_fixture','prime':mod,'seed':seed,'N_degree':len(vals['N'])-1,'P_degree':len(vals[p['output']])-1,'P_leading_coefficient':int(vals[p['output']][-1])}
def scalar(values,mod,packet=p):
    vals=dict(values)
    def g(x):return x%mod if isinstance(x,int) else vals[x]
    for name,op,x,y in packet['source']:
        a,b=g(x),g(y);vals[name]=({'*':lambda:a*b,'+':lambda:a+b,'-':lambda:a-b}[op]())%mod
    return vals
def algebra_mul(x,y,r,mod):
    z=[0]*8
    for i,u in enumerate(x):
        for j,v in enumerate(y):
            f=1
            for k in range(3):
                if i&j&(1<<k):f=f*r[k]%mod
            z[i^j]=(z[i^j]+u*v*f)%mod
    return z

def literal_norm(v,mod):
    out=[1]+[0]*7
    for sg in [-1,1]:
      for sa in [-1,1]:
       for sf in [-1,1]:
        x=[v['W'],-sg*v['L'],-sa*v['S'],0,0,0,0,0]
        sq=algebra_mul(x,x,[v['G'],v['A'],v['D']],mod)
        f=[v['d']*z%mod for z in sq]
        S2=v['S']**2%mod; Q=v['Q'];b=v['b'];c=v['c'];T=v['T'];D=v['D']; vv=c*T%mod
        e=(Q*(D*vv**2+b**2)-1)%mod;Baux=2*Q*vv*b%mod
        f[0]=(f[0]-S2*e)%mod;f[4]=(f[4]+sf*S2*Baux)%mod
        out=algebra_mul(out,f,[v['G'],v['A'],v['D']],mod)
    require(out[1:]==[0]*7,'Formal norm has nonconstant radical coordinates')
    return out[0]

def load_fixed():
    binding_path=(ROOT/p['coefficient_binding_file']).resolve()
    binding=json.loads(binding_path.read_text())
    aliases={native:local for local,native in p['port_aliases'].items()}
    require(p['port_aliases']=={'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'},
            'Incorrect fixed-port aliases')
    fixed={};receipts=[]
    require(binding['d']%2==1,'Native exponent d must be odd')
    for item in binding['materialization']['files']:
        fp=binding_path.parent/item['file'];compressed=fp.read_bytes()
        require(hashlib.sha256(compressed).hexdigest()==item['gzip_sha256'],
                f'Compressed coefficient hash mismatch: {fp}')
        raw=gzip.decompress(compressed)
        require(hashlib.sha256(raw).hexdigest()==item['sha256'],
                f'Raw coefficient hash mismatch: {fp}')
        value=int.from_bytes(raw,'little')
        require(value.bit_length()==item['bits'],f'Coefficient bit length mismatch: {fp}')
        fixed[aliases[item['port']]]=value
        receipts.append({'port':item['port'],'sha256':item['sha256'],'bits':item['bits']})
    require(fixed['beta']+1==1<<binding['d'],'Incorrect beta numeral')
    return fixed,receipts

def source_hashes():
    ledger=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for item in ledger['files']:
        b=(ROOT/item['local_path']).read_bytes()
        require(len(b)==item['bytes'],f'Source length mismatch: {item["local_path"]}')
        require(hashlib.sha256(b).hexdigest()==item['sha256'],
                f'Source SHA-256 mismatch: {item["local_path"]}')
        require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==item['git_blob'],
                f'Source Git blob mismatch: {item["local_path"]}')
    return len(ledger['files'])

def main():
    convolution_cases=check_convolution()
    pin_count=source_hashes()
    fixed,payloads=load_fixed()
    rays=[run_poly(pr,s,fp) for fp in [None,fixed] for pr,s in [(10007,11),(10009,17),(10037,23)]]
    for r in rays:
        require(r['N_degree']==622 and r['P_degree']==629,f'Degree ray mismatch: {r}')
    rng=random.Random(83912); cases=0;identity_cases=0
    for mod in [101,1009,10007]:
        for _ in range(20):
            inp={v:rng.randrange(mod) for v in p['witnesses']+p['fixed_numerals']}
            vals=scalar(inp,mod)
            require(vals['N']==literal_norm(vals,mod),f'Formal norm mismatch modulo {mod}')
            cases+=1
        for _ in range(20):
            inp={v:rng.randrange(mod) for v in p['witnesses']}
            inp.update({k:v%mod for k,v in fixed.items()})
            vals=scalar(inp,mod);q=vals['q']
            if q==0:continue
            mapped=dict(inp);mapped['J']=(3*inp['J']+1)%mod
            sold=inp['s']*pow(q,-2,mod)%mod
            mapped['s']=sold;mapped['t']=(inp['t']+sold)%mod
            oldvals=scalar(mapped,mod,old)
            require(vals['N']==pow(q,32,mod)*oldvals['N']%mod,
                    f'Old-norm substitution mismatch modulo {mod}')
            require(vals['Nk']==oldvals['Nk'] and vals['Nt']==oldvals['Nt'],
                    f'Old transport/index mismatch modulo {mod}')
            identity_cases+=1
    result={'arithmetic':'Python standard library; exact carry-free Kronecker convolution',
            'optimization_safe':True,'convolution_checks':convolution_cases,
            'ray_checks':rays,'literal_norm_checks':cases,'old_norm_substitution_checks':identity_cases,
            'source_pins_checked':pin_count,'fixed_payloads_checked':payloads,
            'operations':p['operations'],'status':'Finite algebra diagnostics passed; proof of unbounded equivalence is separate.'}
    (ROOT/'p12_check_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
