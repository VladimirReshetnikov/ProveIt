#!/usr/bin/env python3
"""Exact source, arithmetic, degree and binding checks, plus scoped fixtures.

No consistency assumption or refutation search is used. The ordinary semantic
proof is PROOF.md and the explicitly named inherited results.
"""
from pathlib import Path
from collections import Counter
import gzip,hashlib,importlib.util,json,random,sys,tempfile
ROOT=Path(__file__).resolve().parent
from build_source import require,add,mul,build

def invariant(c,pool):
    """Canonical expression modulo exact B-exponent addition identities only."""
    base=c['named_nodes']['B'];tags=[];powers=[];base_tag=None
    def intern(key):
        if key not in pool:pool[key]=len(pool)
        return pool[key]
    for idx,n in enumerate(c['nodes']):
        k=n['kind'];p=None
        if k=='literal':t=('literal',n['value']);p=0 if n['value']==1 else None
        elif k in ['variable','fixed']:t=(k,n['name'])
        else:
            a,b=n['left'],n['right'];require(a<idx and b<idx,'acyclic circuit')
            if k=='mul' and powers[a] is not None and powers[b] is not None:
                p=powers[a]+powers[b];t=('power',base_tag,p)
            else:
                xx,yy=tags[a],tags[b]
                if k in ['add','mul']:xx,yy=sorted((xx,yy))
                t=(k,xx,yy)
        if idx==base:
            require(k=='mul','base definition is a multiplication')
            base_tag=intern(t);p=1
        if p==1:
            require(base_tag is not None,'base defined before its powers')
            tags.append(base_tag);powers.append(p);continue
        if p==0:t=('literal',1)
        powers.append(p);tags.append(intern(t))
    return base_tag,tags[c['output']]

def evaluate(c,inputs,fixed,mod):
    vals=[]
    for node in c['nodes']:
        k=node['kind']
        if k=='variable':v=inputs[node['name']]
        elif k=='fixed':v=fixed[node['name']]
        elif k=='literal':v=node['value']
        else:
            a,b=vals[node['left']],vals[node['right']];v=a+b if k=='add' else a-b if k=='sub' else a*b
        vals.append(v%mod)
    return vals[c['output']]

def identity_checks():
    # Exact sparse polynomial identity for the non-obvious majorant error.
    zero=(0,)*4;one={zero:1}
    def var(i):return {tuple(int(i==j) for j in range(4)):1}
    D,k,G,H=[var(i) for i in range(4)]
    def scale(a,c):return {m:c*v for m,v in a.items()}
    def sq(a):return mul(a,a)
    F=add(mul(mul(sq(k),sq(D)),add(D,one,-1)),one)
    T=mul(k,add(add(scale(sq(D),8),scale(D,4),-1),one,-1))
    I=add(mul(add(sq(G),one,-1),sq(H)),one)
    lhs=add(sq(mul(mul(T,G),H)),scale(mul(mul(D,F),I),64),-1)
    err=add(mul(add(scale(D,8),one),sq(k)),scale(D,64),-1)
    rhs=add(mul(err,sq(mul(G,H))),scale(mul(mul(D,F),add(sq(H),one,-1)),64))
    require(lhs==rhs,'majorant error identity')
    # Four-factor norm and cancellation are ordinary polynomial identities;
    # checking the error above supplies the less immediate degree cancellation.
    return {'majorant_error_polynomial_identity':True,'expanded_terms':len(lhs)}

def verify_native():
    bind=json.loads((ROOT/'upstream/COMPACT_BINDING.json').read_text());total=0
    for r in bind['ports']:
        compressed=(ROOT/'coefficients'/r['gzip_file']).read_bytes();raw=gzip.decompress(compressed)
        require(hashlib.sha256(raw).hexdigest()==r['sha256'],'native raw hash');require(len(raw)==r['bytes'],'native size');require(int.from_bytes(raw,'little').bit_length()==r['bits'],'native bit length');total+=len(raw)
    path=ROOT/'upstream/build_native_coefficients.py';spec=importlib.util.spec_from_file_location('native_builder',path);native=importlib.util.module_from_spec(spec);spec.loader.exec_module(native)
    data=native.recipe();geometry=native.finite_audit(data);pad=native.padding_certificate(data)
    with tempfile.TemporaryDirectory() as td:
        native.HERE=Path(td);native.materialize(data)
        for r in bind['ports']:
            got=gzip.decompress((Path(td)/'coefficients'/r['gzip_file']).read_bytes());require(hashlib.sha256(got).hexdigest()==r['sha256'],'native recipe reconstruction')
    return {'whole_tuple_raw_bytes':total,'native_reconstruction':True,'basis_checks':geometry['basis_convolution_checks'],'rank_controller':pad['status']}

def main():
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for entry in pins['files']:
        raw=(ROOT/entry['path']).read_bytes()
        require(hashlib.sha256(raw).hexdigest()==entry['sha256'],'pinned local source '+entry['path'])
        if 'git_blob' in entry:
            require(hashlib.sha1(('blob '+str(len(raw))+'\0').encode()+raw).hexdigest()==entry['git_blob'],'pinned Git blob '+entry['path'])
    source=build();native=verify_native();ident=identity_checks()
    positive=json.loads((ROOT/'generated/split_116_positive.json').read_text());final=json.loads((ROOT/'generated/split_116_positive_global.json').read_text())
    natural=json.loads((ROOT/'generated/split_116_natural_global.json').read_text());cert=json.loads((ROOT/'generated/split_116_positive_certificate.json').read_text())
    pool={}
    require(invariant(positive,pool)==invariant(final,pool),'exact pure-power rewrite equivalence')
    chain=json.loads((ROOT/'generated/split_116_positive_global.certificate.json').read_text())
    known={1}
    for e,a,b in chain['chain']:require(a in known and b in known and e==a+b,'exponent chain');known.add(e)
    require(set(chain['required_exponents'])<=known,'chain coverage')
    for c,cost in [(final,453),(natural,460)]:
        counts=Counter(n['kind'] for n in c['nodes'] if n['kind'] in ['add','sub','mul']);require(sum(counts.values())==cost==c['total_operations'],'count')
        live={c['output']};todo=list(live)
        while todo:
            n=c['nodes'][todo.pop()]
            if n['kind'] in ['add','sub','mul']:
                for k in [n['left'],n['right']]:
                    if k not in live:live.add(k);todo.append(k)
        require(len(live)==len(c['nodes']),'dead circuit node')
    from build_nine import degree_certificate
    deg=degree_certificate(cert);require(deg['exact_degree']==1834516,'exact diagonal degree')
    require(104*8743+400*2310+8*116+316==deg['exact_degree'],'independent closed degree formula')
    from materialize import values
    fixed=values(final);binding=json.loads((ROOT/'fixed/BINDING.json').read_text())
    for r in binding['entries']:
        raw=gzip.decompress((ROOT/r['file']).read_bytes());require(hashlib.sha256(raw).hexdigest()==r['raw_sha256'],'derived leaf hash');require(r['sign']*int.from_bytes(raw,'little')==fixed[r['name']],'actual fixed coefficient')
    rng=random.Random(20261023);fixtures=0
    for prime in [1000003,1000033,2147483647]:
        for _ in range(40):
            inp={v:rng.randrange(1,1000) for v in final['variables']};nat={v:x-1 for v,x in inp.items()}
            expected=evaluate(positive,inp,fixed,prime)
            require(expected==evaluate(final,inp,fixed,prime)==evaluate(cert,inp,fixed,prime)==evaluate(natural,nat,fixed,prime),'scoped modular transcription fixture');fixtures+=1
    kap=1182966;cexp=8872234
    for k in range(100):
        v=kap+2*k;u=k+2186*v;pop=139*v-31*k-22
        require(u+pop==2*(cexp+1155*v),'exact calibration')
    # Finite small binary blocks illustrate the general algebraic identity.
    blocks=0
    for u in range(1,9):
        L=1<<u
        for S in range(min(L,30)):
            for T in range(min(L-S,30)):
                R=(L-1)*S+L*T+L-1;tau=S.bit_count()+T.bit_count()-(S+T).bit_count()
                require(R.bit_count()==u+T.bit_count()-tau,'two-block identity');require((tau==0)==((S&T)==0),'carry defect fixture');blocks+=1
    receipt={'status':'PASS','source':source,'native':native,'identities':ident,'exact_degree':deg['exact_degree'],'positive_operations':453,'natural_operations':460,'power_rewrite_exact':True,'power_chain_gates':len(chain['chain']),'source_scale_exponent':kap,'threshold_scale_exponent':cexp,'modular_fixtures':fixtures,'binary_block_fixtures':blocks,'calibration_fixtures':100,'scope':'Finite algebra, data and implementation verification; unbounded consistency semantics imported and proved in PROOF.md, no kernel certificate.'}
    (ROOT/'certificates/VERIFIED.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
