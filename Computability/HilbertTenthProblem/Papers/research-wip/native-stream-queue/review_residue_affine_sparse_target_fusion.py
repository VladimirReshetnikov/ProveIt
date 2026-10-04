"""Independent full-array review; all author/predecessor code is inert."""
import argparse
import hashlib
import json
from pathlib import Path

AUTHOR={
 'residue_affine_sparse_target_fusion.py':'256892e0f2431d150dd059d55cbdf58bb2d44dd45e9bfe723faf6ed262b9fd2f',
 'residue_affine_sparse_target_fusion.json':'5b94b171976f73b6bfedb6b068fb145652c8c62e79d6ef8103d9a5da393ae855',
 'residue_affine_sparse_target_fusion.md':'0e6dc11d51d4bcb52eff1d678deb03496f99af3694112d3b2ef5a86bb0943b60',
}
PARENT={
 'residue_affine_sparse_prime_recenter.py':'c5d8b2690f1e2a9b50aa063a95f81297ff388b276ab83ce487aa4cbaacc46798',
 'residue_affine_sparse_prime_recenter.json':'e35399b892850ace2bf860fd37f0e3e9f8af34dd8e516f66718547e0689fe26c',
 'residue_affine_sparse_prime_recenter.md':'78e81a12145ecf2b5b57fecdbef614cafa2a96ff0b86e488c4479546914c108c',
}
OUTPUT='norm_output'
HATS={f'edge{i}_hat' for i in range(36)}
EXCEPTIONS={'joint_35'}|{f'joint_{i}' for i in range(47,56)}

def require(x,s):
    if not x:raise ValueError(s)
def sha(x):return hashlib.sha256(x).hexdigest()
def canon(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):
    def pairs(xs):
        d={}
        for k,v in xs:
            require(k not in d,'duplicate JSON key');d[k]=v
        return d
    def bad(x):raise ValueError('noninteger JSON '+x)
    return json.loads(p.read_bytes(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def const(n):return {():n} if n else {}
def symbol(n):return {(n,):1}
def add(a,b,s=1):
    r=dict(a)
    for m,c in b.items():r[m]=r.get(m,0)+s*c
    return {m:c for m,c in r.items() if c}
def mul(a,b):
    r={}
    for m,c in a.items():
        for n,d in b.items():
            k=tuple(sorted(m+n));r[k]=r.get(k,0)+c*d
    return {m:c for m,c in r.items() if c}
def serial(p):return [[list(m),c] for m,c in sorted(p.items())]
def unpack(a):return {tuple(m):c for m,c in a}
def ledger(rows):
    m=sum(r[1]=='*' for r in rows)
    return dict(operations=len(rows),multiplications=m,additions_subtractions=len(rows)-m)
def cone(rows,roots):
    d={r[0]:r for r in rows};live=set();todo=list(roots)
    while todo:
        n=todo.pop()
        if type(n)is str and n in d and n not in live:
            live.add(n);todo.extend(d[n][2:])
    return live

def validate(rows,free):
    d={};deps={n:{n} for n in free}
    require(len(free)==len(deps),'unique free ports')
    for row in rows:
        require(type(row)is list and len(row)==4,'literal row')
        n,o,a,b=row
        require(type(n)is str and n not in deps and o in ('+','-','*'),'SSA/opcode')
        require(all(type(v)is int or type(v)is str and v in deps for v in(a,b)),'topological source')
        deps[n]=set().union(*(deps[v] for v in(a,b) if type(v)is str));d[n]=row
    live=cone(rows,[OUTPUT]);require(live==set(d),'complete liveness')
    supplied={v for r in rows for v in r[2:] if type(v)is str and v not in d}
    require(supplied==set(free),'all supplied ports live')
    return deps

def reconstruct(rows):
    d={r[0]:r for r in rows}
    expected=[['joint_34','*',6,'edge_29'],['joint_46','+','joint_45','joint_34'],
              ['joint_35','*',7,'prime_selector_112'],['joint_47','+','joint_46','joint_35'],
              ['joint_56','+','joint_55','selectors_70'],['selectors_70','+','u21_grouped_J_7','edge_29']]
    for row in expected:require(d[row[0]]==row,'independent literal guard '+row[0])
    for n,consumer in [('joint_34','joint_46'),('joint_46','joint_47')]:
        require([r[0] for r in rows if n in r[2:]]==[consumer],'private removed gate')
    changes={'joint_35':['joint_35','*',7,'target_seven_group'],
             'joint_47':['joint_47','+','joint_45','joint_35'],
             'joint_56':['joint_56','+','joint_55','u21_grouped_J_7']}
    result=[]
    for r in rows:
        if r[0] in ('joint_34','joint_46'):continue
        if r[0]=='joint_35':result.append(['target_seven_group','+','prime_selector_112','edge_29'])
        result.append(list(changes.get(r[0],r)))
    return result

def exact_all_rows(old,new,free):
    intern={}
    def ident(x):
        if x not in intern:intern[x]=len(intern)
        return intern[x]
    def polyid(p):return ident(('hat-polynomial',tuple(sorted(p.items()))))
    def run(rows):
        deps=validate(rows,free);ids={n:polyid(symbol(n)) if n in HATS else ident(('free',n)) for n in free}
        polys={n:symbol(n) for n in free if n in HATS}
        for n,o,a,b in rows:
            if deps[n]<=HATS:
                x=polys[a] if type(a)is str else const(a);y=polys[b] if type(b)is str else const(b)
                p=mul(x,y) if o=='*' else add(x,y,1 if o=='+' else -1)
                require(all(len(m)<=1 for m in p),'the complete actual-hat-only cone stays affine')
                polys[n]=p;ids[n]=polyid(p)
            else:
                x=ids[a] if type(a)is str else polyid(const(a));y=ids[b] if type(b)is str else polyid(const(b))
                args=tuple(sorted((x,y))) if o in ('+','*') else (x,y)
                ids[n]=ident((o,args))
        return ids,polys
    a,pa=run(old);b,pb=run(new)
    common=set(r[0] for r in old)&set(r[0] for r in new)
    changed={n for n in common if a[n]!=b[n]}
    require(changed==EXCEPTIONS,'exact retained-value differences')
    require(a[OUTPUT]==b[OUTPUT],'whole output equal as exact expressions')
    e=add(symbol('edge29_hat'),const(1),-1);differences={}
    for n in sorted(changed):
        delta=add(pb[n],pa[n],-1);factor=7 if n=='joint_35' else 1
        require(delta==mul(const(factor),e),'actual-hat discrepancy '+n);differences[n]=serial(delta)
    return dict(equal_retained=len(common)-len(changed),exceptions=sorted(changed),differences=differences,
                whole_output_equal=True,old_hat_only_computed=len(pa)-36,new_hat_only_computed=len(pb)-36,
                exact_expression_nodes=len(intern)),pa,pb

def expand(rows,target,cuts):
    d={r[0]:r for r in rows};memo={n:symbol(n) for n in cuts}
    def get(n):
        if type(n)is int:return const(n)
        if n not in memo:
            _,o,a,b=d[n];x,y=get(a),get(b)
            memo[n]=mul(x,y) if o=='*' else add(x,y,1 if o=='+' else -1)
        return memo[n]
    return get(target)

def degrees(rows,free,two):
    cuts=['native__wn2','native__R12','native__R10a','native__gam']
    X,a,c,G=map(symbol,cuts)
    expected=add(add(add(add(add(mul(X,X),mul(const(2),mul(mul(a,c),X))),mul(const(2),mul(G,X))),mul(const(2),mul(mul(a,c),G))),mul(G,G)),add(mul(const(4),mul(a,mul(c,c))),mul(const(3),mul(c,c))),-1)
    actual=expand(rows,'native__R15',cuts);require(actual==expected,'fresh full main-norm cancellation')
    def prop(special=None):
        ds={n:1 for n in free}
        for n,o,a,b in rows:
            x=ds[a] if type(a)is str else 0;y=ds[b] if type(b)is str else 0
            ds[n]=x+y if o=='*' else max(x,y)
            if n=='native__R15' and special is not None:ds[n]=special
        return ds
    naive=prop();bound=max(sum(naive[v] for v in mon) for mon in actual);ds=prop(bound)
    target=(827,5062,98,5160,5227) if two else (816,4993,98,5091,5157)
    require((bound,ds['sparse_all_units'],ds['norm_sum5'],ds[OUTPUT],naive[OUTPUT])==target,'complete fresh degree ceilings')
    return dict(main_norm=serial(actual),cut_degrees={n:naive[n] for n in cuts},main_norm_upper=bound,
                native_product_upper=ds['sparse_all_units'],outer_sum_upper=ds['norm_sum5'],
                full_upper=ds[OUTPUT],naive_upper=naive[OUTPUT],exact_degree_claimed=False)

def evaluate(rows,ports,modulus):
    env=dict(ports)
    for n,o,a,b in rows:
        x=env[a] if type(a)is str else a;y=env[b] if type(b)is str else b
        env[n]=(x*y if o=='*' else x+y if o=='+' else x-y)%modulus
    return env

def build(root,author):
    for folder,pins in [(root,PARENT),(author,AUTHOR)]:
        for name,h in pins.items():require(sha((folder/name).read_bytes())==h,'pinned inert file '+name)
    old=read(root/'residue_affine_sparse_prime_recenter.json');new=read(author/'residue_affine_sparse_target_fusion.json')
    snapshots=(canon(old),canon(new))
    require(old['source_sha256']==PARENT['residue_affine_sparse_prime_recenter.py'] and new['source_sha256']==AUTHOR['residue_affine_sparse_target_fusion.py'],'both helper-byte bindings')
    require(old['literal_edges']==new['literal_edges'] and old['state_codes']==new['state_codes'],'all actual state codes and36edges unchanged')
    require(len(old['packets'])==len(new['packets'])==2,'exact two full packets')
    codes=new['state_codes'];require(len(codes)==len(set(codes))==23 and codes[0]==0 and codes[-1]==14 and max(codes)==40 and len(new['literal_edges'])==36,'actual state/edge dimensions and endpoint codes')
    results=[]
    for which,(before,after) in enumerate(zip(old['packets'],new['packets'])):
        require(before['interface']==after['interface']==('two_program' if which else 'one_program'),'two-interface order')
        p,q=before['packet'],after['packet'];oldrows=p['source'];rows=reconstruct(oldrows);free=q['parameters']+q['witnesses']
        require(rows==q['source'],'every actual child row independently reconstructed')
        require(sha(canon(oldrows))==p['source_sha256'] and sha(canon(rows))==q['source_sha256'],'both complete-array hashes')
        require({k:v for k,v in p.items() if k not in {'source','source_sha256','ledger','certificate_ledger'}}=={k:v for k,v in q.items() if k not in {'source','source_sha256','ledger','certificate_ledger'}},'all semantic/domain/degree/interface metadata unchanged')
        require(len(free)==(70 if which else 69) and len(q['witnesses'])==67,'paid supplied arity')
        validate(oldrows,free);validate(rows,free)
        require(ledger(rows)=={k:v for k,v in q['ledger'].items() if k!='witnesses'},'complete paid ledger')
        require(ledger(rows)==dict(operations=464 if which else 465,multiplications=170,additions_subtractions=294 if which else 295),'actual465/464 counts')
        for prefix,n in [('native__',72),('norm_',20)]:
            left=[r for r in oldrows if r[0].startswith(prefix)];right=[r for r in rows if r[0].startswith(prefix)]
            require(left==right and len(right)==n,'literal protected '+prefix)
        byname={r[0]:r for r in rows}
        for r in q['literal_height_radix_rows']:require(byname[r[0]]==r,'actual unchanged height/radix')
        identity,pa,pb=exact_all_rows(oldrows,rows,free)
        require(identity['equal_retained']==(453 if which else 454),'all retained value count')
        words={}
        for label,node,pos in [('current','joint_24',0),('target','joint_61',1)]:
            coeff=[new['state_codes'][e[pos]] for e in new['literal_edges']]
            expected=const(-sum(coeff))
            for j,k in enumerate(coeff):expected=add(expected,mul(const(k),symbol(f'edge{j}_hat')))
            require(pa[node]==pb[node]==expected,'all36 actual-hat '+label+' coefficients')
            require(after['full_actual_hat_words'][label]==serial(expected),'saved whole word')
            words[label]=serial(expected)
        for n in ['edge_29','prime_selector_112','selectors_70','u21_grouped_J_7']:
            require(pb[n]==unpack(after['paid_donor_polynomials'][n]),'paid donor vector '+n)
        require(after['exact_intermediate_differences']==identity['differences'],'all10 saved discrepancy vectors')
        bound=degrees(rows,free,bool(which));require(q['polynomial_degree_upper_bound']==bound['full_upper'],'unchanged claimed degree upper bound')
        finalcuts={'sparse_all_units'}|{f'norm_residual{i}' for i in range(6)}
        final=expand(rows,OUTPUT,finalcuts);expected=add(symbol('sparse_all_units'),const(1),-1)
        for j in range(6):expected=add(expected,mul(symbol('sparse_all_units'),mul(symbol(f'norm_residual{j}'),symbol(f'norm_residual{j}'))))
        require(final==expected==expand(oldrows,OUTPUT,finalcuts),'literal entire finalizer identity')
        # All these cuts are equal in the complete expression interpretation above.
        certificate=ledger([r for r in rows if not r[0].startswith('norm_')]);certificate.update(equations=7,witnesses=67)
        require(certificate==q['certificate_ledger'],'full445/444 certificate ledger')
        base=cone(oldrows,['sparse_all_units']+[f'norm_residual{j}' for j in [0,2,3,4,5]])
        d={r[0]:r for r in oldrows};require(len(base)==(388 if which else 389) and all(d[n]==byname[n] for n in base),'entire noncontrol base literal')
        current=cone(rows,['joint_24'])-base;target=cone(rows,['joint_61'])-base
        wordledger=ledger([r for r in rows if r[0] in current|target])
        require(wordledger==dict(operations=58,multiplications=19,additions_subtractions=39) and current&target=={'joint_12'},'paid joint word cone')
        for test in after['signed_modular_checks']:
            require(set(test['ports'])==set(free),'diagnostic full input assignment')
            a,b=evaluate(oldrows,test['ports'],test['prime']),evaluate(rows,test['ports'],test['prime'])
            require(a[OUTPUT]==b[OUTPUT]==test['output'],'full saved modular output')
            for n in set(d)&set(byname)-EXCEPTIONS:require(a[n]==b[n],'diagnostic retained value')
        results.append(dict(interface=after['interface'],source=rows,source_sha256=q['source_sha256'],supplied=free,
                            ledger=ledger(rows),certificate=certificate,whole_identity=identity,full_words=words,
                            native_rows_literal=72,finalizer_rows_literal=20,base_rows_literal=len(base),
                            joint_word_ledger=wordledger,formal_finalizer=serial(final),degree=bound,
                            modular_checks_recomputed=len(after['signed_modular_checks']),
                            domain_metadata={k:q[k] for k in ['valid_recipe','parameters','ordinary_input_parameter','fixed_program_parameters','witnesses','literal_height_radix_rows']}))
    require(len(results)==2 and (canon(old),canon(new))==snapshots,'exactly two interfaces; all input data immutable')
    return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR,parent_pins=PARENT,
                packets=results,all_ring_identity='Each complete polynomial equals its own parent, not the other interface.',
                method='Exact actual-hat-only polynomials and shared expression tuples for every other paid register; no hash-as-algebra assumption.',
                predecessor_execution=False,author_execution=False,exact_degree_claimed=False)

def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--author-root',type=Path)
    g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
    a=p.parse_args();result=build(a.root,a.author_root or a.root)
    if a.output:
        with a.output.open('x') as f:f.write(json.dumps(result,sort_keys=True,indent=2)+'\n')
    else:require(canon(result)==canon(read(a.expect)),'exact type-sensitive replay')
    print('PASS465/464 full paid-donor fusion review')
if __name__=='__main__':main()
