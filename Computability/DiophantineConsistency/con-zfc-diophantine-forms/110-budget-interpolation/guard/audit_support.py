"""Retained independent coefficient reconstruction and modular norm tools.
Adapted verbatim from pinned root-fusion archive; see licenses.
"""

from pathlib import Path
from collections import Counter,defaultdict
import gzip,hashlib,json

PORTS = ('beta','K0','MC','MF','cone_A','cone_B')

EXPECTED_HASHES = {
 'beta':'6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea',
 'K0':'18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af',
 'MC':'3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777',
 'MF':'78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722',
 'cone_A':'66463b4c98a7cd43faffe6cc0462f7f4fa65b7fd9bc57cba38789e585d59c615',
 'cone_B':'42be64ea01465eb227e9c993dba41affc2d9244aed8ec8f33d3268bda7c6b401'}

def require(ok, msg):
    if not ok: raise ValueError(msg)

def coefficients(root):
    folder=root/'coefficients'
    binding=json.loads((folder/'BINDING.json').read_text())
    values={}
    for name in PORTS:
        rec=binding['payloads'][name]
        raw=gzip.decompress((folder/rec['file']).read_bytes())
        digest=hashlib.sha256(raw).hexdigest()
        require(digest==rec['raw_sha256']==EXPECTED_HASHES[name], 'fixed numeral digest: '+name)
        number=int.from_bytes(raw,'little')
        require(number.bit_length()==rec['bits'], 'bit length: '+name)
        require(len(raw)==rec['raw_bytes']==(number.bit_length()+7)//8, 'minimal numeral: '+name)
        values[name]=number
    recipe=folder/'recipe'
    require(hashlib.sha256((recipe/'k215.tm').read_bytes()).hexdigest()==
      'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090',
      'literal machine digest')
    tiles=json.loads((recipe/'wang943_tiles.json').read_text())
    require(len(tiles)==943 and all(len(t)==4 for t in tiles), 'tile shape')
    # Independently encode the native tuple from the literal tile list.
    bit_weights=[1 << (10+2*j) for j in range(44)]
    rows={}
    for i,tile in enumerate(tiles):
        active=[10*side+j for side,label in enumerate(tile)
                for j in range(10) if (label+512)&(1<<j)]
        rows[i]=1+sum(bit_weights[j] for j in active+list(range(40,44)))
    for side,offset in enumerate((1020,1000,980,960)):
        for j in range(10): rows[offset+2*j]=bit_weights[10*side+j]
    for j,anchor in enumerate((1095,1096,2195,3296)):
        rows[anchor]=bit_weights[40+j]
    rows[1063]=rows[1064]=0
    require(len(rows)==989, 'native support')
    convolution=defaultdict(int)
    for e in (40,41,1100,2200): convolution[e]+=1
    for e,value in rows.items():
        convolution[4393-e]+=value
        convolution[5495-e]+=value
    d=121*8801
    B=1<<d
    beta=B-1
    K0=sum(value << (121*e) for e,value in convolution.items())+(B<<121)
    MC=beta-sum(1 << (121*e) for e in rows if e!=1)-(2 << (121*1063))
    mu=1022+sum(bit_weights)
    MF=4+(mu << (121*4393))+(mu << (121*5495))
    MF+=sum(1 << (121*(1000+2*j)) for j in range(10))
    MF+=sum(1 << (121*(1021+2*j)) for j in range(10))
    MF+=(1 << (121*2195))+(1 << (121*3296))
    MF+=sum(((1<<119)-1) << (121*e) for e in range(8792,8799))
    MF+=((1<<27)-1) << (121*8799)
    expected=dict(beta=beta,K0=K0,MC=MC,MF=MF+beta,
                  cone_A=1<<1113,cone_B=1<<666104)
    require(values==expected, 'full actual integer coefficient reconstruction')
    return values, {'complete_integer_reconstruction':True,
                    'fixed_digest_checks':len(PORTS),
                    'literal_machine_digest':True,
                    'tile_count':len(tiles),'native_support':len(rows)}

class Fp:
    """Tiny field element, used only for independent finite diagnostics."""
    def __init__(self,value,p):self.value,self.p=value%p,p
    def coerce(self,x):return x if isinstance(x,Fp) else Fp(x,self.p)
    def __add__(self,x):return Fp(self.value+self.coerce(x).value,self.p)
    __radd__=__add__
    def __neg__(self):return Fp(-self.value,self.p)
    def __sub__(self,x):return self+(-self.coerce(x))
    def __rsub__(self,x):return self.coerce(x)+(-self)
    def __mul__(self,x):return Fp(self.value*self.coerce(x).value,self.p)
    __rmul__=__mul__
    def __pow__(self,n):return Fp(pow(self.value,n,self.p),self.p)

def formal_conjugate_norm(center, radicands, prime):
    """Literal product in F_p[r_i]/(r_i^2-A_i), reverse conjugation order."""
    def multiply(left,right):
        out={}
        for m,v in left.items():
            for n,w in right.items():
                common=m&n
                coefficient=v*w
                while common:
                    bit=common&-common
                    coefficient*=radicands[bit.bit_length()-1]
                    common-=bit
                mask=m^n
                out[mask]=(out.get(mask,0)+coefficient)%prime
        return {m:v for m,v in out.items() if v}
    product={0:center%prime}
    for i in range(len(radicands)):product[1<<i]=prime-1
    for i in reversed(range(len(radicands))):
        conjugate={m:(-v if m&(1<<i) else v)%prime for m,v in product.items()}
        product=multiply(product,conjugate)
    require(all(m==0 for m in product), 'formal field norm elimination')
    return product.get(0,0)

def evaluate_dag(packet, inputs, ports, prime):
    values=[]
    for node in packet['nodes']:
        op=node[0]
        if op=='integer':v=node[1]
        elif op=='variable':v=inputs[node[1]]
        elif op=='coefficient':v=ports[node[1]]
        elif op=='add':v=values[node[1]]+values[node[2]]
        elif op=='sub':v=values[node[1]]-values[node[2]]
        elif op=='mul':v=values[node[1]]*values[node[2]]
        else:raise ValueError('unknown DAG operation')
        values.append(v%prime)
    return values
