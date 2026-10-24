"""Independent, exact verification; standard library only.

This checker imports the generic sparse ring, but neither circuit builder.
It proves equality of complete norm tails over a free seven-variable ring,
authenticates all unchanged prefixes, and verifies literal fixed coefficients.
"""
import gzip
import hashlib
import json
import random
from collections import Counter
from pathlib import Path
import norm_identity as ring

HERE=Path(__file__).resolve().parent
CASES=(
    ('trace13_parent.json','symmetric_trace13.json',116,
     {67:0,115:1,108:2,65:3,79:4,105:5,74:6},127,536),
    ('scalar12_rational_parent.json','symmetric_scalar12_rational.json',125,
     {88:0,124:1,112:2,86:3,102:4,80:5,97:6},139,1200),
    ('scalar12_integral_parent.json','symmetric_scalar12_integral.json',125,
     {88:0,124:1,112:2,86:3,102:4,80:5,97:6},138,1456),
    ('trace13_parent.json','compact_trace13.json',116,
     {67:0,115:1,108:2,65:3,79:4,105:5,74:6},126,536),
    ('scalar12_rational_parent.json','compact_scalar12_rational.json',125,
     {88:0,124:1,112:2,86:3,102:4,80:5,97:6},138,1200),
    ('scalar12_integral_parent.json','compact_scalar12_integral.json',125,
     {88:0,124:1,112:2,86:3,102:4,80:5,97:6},137,1456),
)

def fail(message):raise ValueError(message)
def load(name):return json.loads((HERE/name).read_text())

def check_graph(packet):
    nodes=packet['nodes'];counts=Counter();variables=[];coefficients=[]
    for i,row in enumerate(nodes):
        kind,*args=row
        if kind in ('add','sub','mul'):
            counts[kind]+=1
            if len(args)!=2 or any(type(j)!=int or not 0<=j<i for j in args):fail(('topology',i))
        elif kind=='variable':variables.append(args[0])
        elif kind=='coefficient':coefficients.append(args[0])
        elif kind!='integer':fail(('operation',i,kind))
    used=set()
    def mark(i):
        if i in used:return
        used.add(i)
        if nodes[i][0] in ('add','sub','mul'):
            for j in nodes[i][1:]:mark(j)
    mark(packet['output'])
    if len(used)!=len(nodes):fail('nonlive node')
    if packet['operations']!=sum(counts.values()) or packet['operation_counts']!=counts:fail('count mismatch')
    if packet['variables']!=variables or packet['variable_count']!=len(variables):fail('variable mismatch')
    return counts,coefficients

def abstract_tail(packet,start,seed):
    values={i:ring.const(row[1]) for i,row in enumerate(packet['nodes'][:start]) if row[0]=='integer'}
    values.update({i:ring.var(j) for i,j in seed.items()})
    for i in range(start,len(packet['nodes'])):
        kind,*args=packet['nodes'][i]
        if kind=='integer':v=ring.const(args[0])
        elif kind in ('add','sub','mul'):
            a,b=(values[j] for j in args)
            v={'add':ring.add,'sub':ring.sub,'mul':ring.mul}[kind](a,b)
        else:fail(('unexpected tail leaf',kind))
        values[i]=v
    return values[packet['output']]

def evalmod(packet,inputs,coeffs,p):
    values=[]
    for kind,*args in packet['nodes']:
        if kind=='integer':v=args[0]
        elif kind=='variable':v=inputs[args[0]]
        elif kind=='coefficient':v=coeffs[args[0]]
        else:
            a,b=(values[j] for j in args)
            v=a+b if kind=='add' else a-b if kind=='sub' else a*b
        values.append(v%p)
    return values[packet['output']]

def main():
    # Direct 16-conjugate expansion, not a sampled identity check.
    ring.main();ring.N=7
    binding=load('coefficients/BINDING.json');coeffs={};payloads={}
    for name,spec in binding['payloads'].items():
        path=HERE/'coefficients'/spec['file'];raw=gzip.decompress(path.read_bytes())
        digest=hashlib.sha256(raw).hexdigest();v=int.from_bytes(raw,'little')
        if digest!=spec['raw_sha256'] or len(raw)!=spec['raw_bytes'] or v.bit_length()!=spec['bits']:fail(('coefficient',name))
        if name=='beta' and v!=(1<<1064921)-1:fail('wrong beta')
        if name=='cone_A' and v!=1<<1113:fail('wrong first cone coefficient')
        if name=='cone_B' and v!=1<<666104:fail('wrong second cone coefficient')
        coeffs[name]=v;payloads[name]={'sha256':digest,'bits':v.bit_length(),'bytes':len(raw)}
    scalar_binding=load('source/candidates/scalar-carrier12/coefficients/BINDING.json')
    if scalar_binding!=binding:fail('mixed coefficient tuples')
    pins=load('SOURCE_PINS.json')
    for pin in pins['files']:
        data=(HERE/pin['path']).read_bytes()
        if hashlib.sha256(data).hexdigest()!=pin['sha256']:fail(('source digest',pin['path']))
        if hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()!=pin['git_blob']:fail(('Git blob',pin['path']))
    results=[];rng=random.Random(20261024)
    for pname,cname,start,seed,count,degree in CASES:
        parent,child=load(pname),load(cname)
        pcounts,pcoeffs=check_graph(parent);counts,ccoeffs=check_graph(child)
        if parent['nodes'][:start]!=child['nodes'][:start]:fail(('changed prefix',cname))
        if pcoeffs!=ccoeffs or set(ccoeffs)!=set(coeffs):fail(('coefficient leaves',cname))
        if child['operations']!=count or child['exact_degree']!=degree:fail(('metrics',cname))
        a=abstract_tail(parent,start,seed);b=abstract_tail(child,start,seed)
        if a!=b:fail(('polynomial mismatch',cname))
        # Concrete controls exercise actual complete six-port numerals.
        for p in (101,1009,1000003):
            cp={k:v%p for k,v in coeffs.items()}
            for _ in range(100):
                x={k:rng.randrange(-p,p) for k in child['variables']}
                if evalmod(parent,x,cp,p)!=evalmod(child,x,cp,p):fail(('actual coefficient control',cname))
        results.append({'file':cname,'unchanged_prefix_nodes':start,'abstract_tail_terms':len(a),'universal_polynomial_identity':True,
                        'variables':child['variable_count'],'operations':count,'operation_counts':dict(sorted(counts.items())),
                        'parent_operations':parent['operations'],'exact_degree_by_identical_polynomial':degree,
                        'actual_coefficient_modular_controls':300,'sha256':hashlib.sha256((HERE/cname).read_bytes()).hexdigest()})
    receipt={'generic_16_conjugate_terms':495,'source_commit':pins['commit'],'source_files_authenticated':len(pins['files']),
             'six_coefficient_payloads':payloads,'equations':results,
             'scope':'Universal ring identities and exact finite specification checks; source semantic calibration inherited, no new Lean or object-ZFC proof.'}
    (HERE/'VERIFICATION.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'verified':True,'equations':results},indent=2))

if __name__=='__main__':main()
