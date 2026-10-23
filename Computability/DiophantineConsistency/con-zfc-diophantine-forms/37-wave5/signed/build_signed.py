#!/usr/bin/env python3
"""Explicit unrestricted-integer Jones forms. Standard library only.
Proof: SIGNED_PROOF.md. Sources29/30 and source27 evaluation, pinned upstream.
Binary +,-,* convention includes scalar multiplication and squaring.
"""
from pathlib import Path
import json,hashlib
import fast_jones_base as jb
ROOT=Path(__file__).resolve().parent
NU=31
L=5**(NU+1)
S_INDEX=45933757
KAPPA=(S_INDEX+1)*(L+1)+1

def verify_source_pins():
    records=json.loads((ROOT/'SOURCE_PINS.json').read_text())['files']
    for record in records:
        data=(ROOT/record['path']).read_bytes()
        assert hashlib.sha256(data).hexdigest()==record['sha256'],record['path']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==record['git_blob_sha1'],record['path']
    return len(records)

def construct(count=16):
    assert count in (14,15,16)
    constants=json.loads((ROOT/'upstream/COMPACT_CONSTANTS.json').read_text())
    keys,aliases=jb.canonical_coefficients(constants)
    core=jb.make_body(NU,keys,'structured',False)
    d=jb.DAG(); c,A,M,S,P=d.const,d.plus,d.times,d.minus,d.power
    mapping={}
    shifted={name+'0':name for name in ['g','h','s','w','i','j']}
    oldvars={n['name']:k for k,n in enumerate(core['nodes']) if n['kind']=='variable'}
    ones={k for k,n in enumerate(core['nodes']) if n['kind']=='literal' and n['value']==1}
    shift_nodes={}
    for k,n in enumerate(core['nodes']):
        if n['kind']=='add':
            for old,new in shifted.items():
                if oldvars[old] in (n['left'],n['right']) and ({n['left'],n['right']}&ones):shift_nodes[k]=new
    for k,n in enumerate(core['nodes']):
        kind=n['kind']
        if k==core['named_nodes']['b'] and count<=15:
            out=M(d.fixed('base_scale'),P(d.var('epsilon'),2))
        elif k in shift_nodes:
            name=shift_nodes[k]
            out=P(d.var('w'),2) if count==14 and name=='w' else d.var(name)
        elif kind=='literal':out=c(n['value'])
        elif kind=='fixed':out=d.fixed(n['name'])
        elif kind=='variable':
            out=d.var(shifted.get(n['name'],n['name']))
        else:out=d.op(kind,mapping[n['left']],mapping[n['right']])
        mapping[k]=out
    d.names={name:mapping[k] for name,k in core['named_nodes'].items()}
    get=lambda name:d.names[name]
    guards=['epsilon','g','s','w','phi']
    if count<=15:guards.remove('epsilon')
    if count<=14:guards.remove('w')
    zz=[d.var('z'+str(j)) for j in range(1,len(guards)+2)]
    residue,normroot=d.var('residue'),d.var('normroot')
    stack=c(1)
    for j,name in enumerate(guards):
        # 4*(3x+2) is evaluated directly as 12x+8.
        disc4=(A(M(c(12),d.var(name)),c(8)) if name in ('epsilon','phi') else S(M(c(12),d.var(name)),c(4)))
        factor=A(c(1),M(disc4,P(M(stack,zz[j]),2)))
        stack=d.save('Cguard'+str(j+1),M(stack,factor))
    disc4=S(M(c(12),get('margin')),c(4))
    factor=A(c(1),M(disc4,P(M(stack,zz[-1]),2)))
    stack=d.save('Cguard',M(stack,factor))
    divisor=d.save('Ddiv',M(get('J'),get('F')))
    dividend=d.save('Tdiv',A(M(get('Q'),get('F')),M(get('J'),S(get('H'),get('C')))))
    nonzero_args=[d.var('i')]+zz
    if count<=15:nonzero_args.append(d.var('epsilon'))
    if count<=14:nonzero_args.append(d.var('w'))
    nonzero=d.save('Znonzero',M(*nonzero_args))
    denom=d.save('Smerge',M(nonzero,P(divisor,5)))
    rr=A(dividend,M(divisor,residue));div2=P(divisor,2)
    homogeneous=d.save('Tmerge',M(S(S(P(rr,3),M(div2,rr)),M(div2,divisor)),A(P(rr,2),M(c(23),div2))))
    w1=d.save('weight1',A(c(1),stack))
    w2=d.save('weight2',M(w1,A(P(get('P'),2),P(get('K'),2),c(2))))
    X=d.save('Xnorm',S(M(denom,normroot),homogeneous));S2=P(denom,2)
    A0=d.save('A0norm',M(S2,stack));A1=d.save('A1norm',M(S2,P(w1,2),get('a0')))
    A2=d.save('A2norm',M(S2,P(w2,2),get('a1')));X2=P(X,2)
    V=d.save('Vnorm',S(S(A(X2,A2),A0),A1));V2=P(V,2)
    fourXA=M(c(4),X2,A2)
    W=d.save('Wnorm',S(A(V2,fourXA),M(c(4),A0,A1)))
    output=d.save('signed'+str(count),S(P(W,2),M(c(4),V2,fourXA)))
    nodes,output,names=d.prune(output)
    variables=[n['name'] for n in nodes if n['kind']=='variable']
    assert len(variables)==count and len(set(variables))==count
    return {'schema':'proveit-signed-jones-wave5-v1','domain':'unrestricted integers',
      'variables':variables,'nu':NU,'L':L,'nodes':nodes,'output':output,'named_nodes':names,
      'guards':guards,'operation_counts':{k:sum(n['kind']==k for n in nodes) for k in ('add','sub','mul')},
      'coefficient_binding':{'path_base':'package_root','manifest':'INSTANCE.json','tuple':'wang943-compact-5pow10','fixed_recipes':'signed/FIXED_RECIPES.json'},
      'fixed_leaf_recipes':{'path_base':'package_root','coefficient_records':'signed/upstream/COMPACT_CONSTANTS.json','index_and_scale':'signed/FIXED_RECIPES.json','aliases':'signed/generated/COEFFICIENT_ALIASES.json'},
      'proof':{'path_base':'package_root','path':'signed/SIGNED_PROOF.md'},'status':'ordinary proof, not kernel checked'},aliases

def degree_audit(body,p=1000003):
    """Structural upper bound plus symbolic diagonal head modulo prime p.
    An output head that is a nonzero scalar times a power of positive base_scale
    proves the exact degree at the actual fixed coefficient specialization.
    """
    rows=[]
    def add(a,b,sgn=1):
        v=dict(a)
        for k,c in b.items():v[k]=(v.get(k,0)+sgn*c)%p
        return {k:c for k,c in v.items() if c}
    # Sparse monomials use (name, exponent) pairs instead of repeated symbols.
    def mul(a,b):
        v={}
        for ma,ca in a.items():
            for mb,cb in b.items():
                ex=dict(ma)
                for name,e in mb:ex[name]=ex.get(name,0)+e
                m=tuple(sorted(ex.items()));v[m]=(v.get(m,0)+ca*cb)%p
        return {k:c for k,c in v.items() if c}
    for n in body['nodes']:
        k=n['kind']
        if k=='literal':r=(0,{():n['value']%p} if n['value']%p else {})
        elif k=='fixed':r=(0,{((n['name'],1),):1})
        elif k=='variable':r=(1,{():1})
        else:
            a,b=rows[n['left']],rows[n['right']]
            if k=='mul':r=(a[0]+b[0],mul(a[1],b[1]))
            else:
                deg=max(a[0],b[0]);r=(deg,add(a[1] if a[0]==deg else {},b[1] if b[0]==deg else {},1 if k=='add' else -1))
        rows.append(r)
    deg,head=rows[body['output']]
    assert len(head)==1
    mon,coef=next(iter(head.items()))
    assert coef and all(name=='base_scale' for name,e in mon)
    selected={name:{'degree':rows[idx][0], 'head_modular':[{'powers':dict(m),'coefficient':co} for m,co in rows[idx][1].items()]} for name,idx in body['named_nodes'].items() if name in ['b','R','P','K','a0','a1','margin','Cguard','Smerge','Tmerge','weight1','weight2','A2norm','signed14','signed15','signed16']}
    return {'exact_degree':deg,'modulus':p,'leading_scalar_modulus':coef,'leading_fixed_monomial':dict(mon),'selected':selected}

def run():
    verify_source_pins()
    out=ROOT/'generated';out.mkdir(exist_ok=True)
    ledger={}
    for count in [16,15,14]:
        body,aliases=construct(count);audit=degree_audit(body)
        body['exact_degree']=audit['exact_degree']
        fn=out/f'signed{count}.json';fn.write_text(json.dumps(body,separators=(',',':'))+'\n')
        ledger[str(count)]={'variables':count,'operations':sum(body['operation_counts'].values()),'operation_counts':body['operation_counts'],'fixed_leaves':sum(n['kind']=='fixed' for n in body['nodes']),'degree_audit':audit}
    (out/'LEDGER.json').write_text(json.dumps(ledger,indent=2)+'\n')
    (out/'COEFFICIENT_ALIASES.json').write_text(json.dumps(aliases,indent=2)+'\n')
    (ROOT/'FIXED_RECIPES.json').write_text(json.dumps({'nu':NU,'L':L,'index_exponent':S_INDEX,'z_index':f'2^{S_INDEX}','y_index':'sum((z+c_alpha)*(2z)^(L-expo(alpha)), |alpha|<=4), including zero coefficients','kappa':KAPPA,'base_scale':f'2^{KAPPA}','base_scale_used_by':[14,15],'compiler_tuple':'complete source30 compact943 tuple','port_binding':{'path_base':'package_root','manifest':'INSTANCE.json','tuple':'wang943-compact-5pow10','binding':'coefficients/COMPACT_COEFFICIENT_BINDING.json'}},indent=2)+'\n')
    print(json.dumps({k:{'variables':v['variables'],'operations':v['operations'],'degree':v['degree_audit']['exact_degree']} for k,v in ledger.items()},indent=2))
if __name__=='__main__':run()
