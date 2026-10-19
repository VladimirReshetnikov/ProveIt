#!/usr/bin/env python3
"""Rebuild the exact K227 source and table from frozen K230 inputs.

Source normalization, four closed H identities, two boundary rotations, and
five closed reassociations are checked here. The native local-role equivalence
is independently checked by verify_roles.py; the inherited two native folds
and complete unbounded interpreter audit are separate deliverables.
"""
from pathlib import Path
from functools import cache
import argparse,hashlib,json
import source_math as g
HERE=Path(__file__).resolve().parent
PIN_TABLE='e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8'
PIN_SITES='400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487'
FINAL_TABLE='1e08e34a1d33d8cfd14a10f56049b4a9a67fef66909630655157b5250b90f3ea'
FINAL_SOURCE='40379cead096b3605a86f26940a84be5be4869a037dfeeb6c56d293237a82e24'
H_OLD=((('CD',6),(('CI',5),('CC',2))),('CI',5))
H_NEW=(('CI',5),(('CD',6),('CC',2)))
ROTATIONS=[(202,201,'right'),(174,119,'left'),(148,154,'left'),(210,174,'right'),(174,101,'right')]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read_table(p):
    t={}
    for line in Path(p).read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert(q,b) not in t
        assert b in(0,1) and w in(0,1) and d in('L','R');t[q,b]=(w,1 if d=='R' else -1,z)
    return t
def encode(t,start=0):return f'#! start {start}\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for(q,b),(w,d,z) in sorted(t.items()))
def at(t,p):
    for b in p:t=t[int(b)]
    return t
def put(t,p,v):
    if not p:return v
    i=int(p[0]);z=list(t);z[i]=put(z[i],p[1:],v);return tuple(z)
def normalize(raw):
    ops={'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC','EHalt':'CH'}
    return [[p,ops[x.split()[0]],int(x.split()[1]) if len(x.split())>1 else None] for p,x in raw]
def save_stage(out,name,root,table,receipt):
    d=out/name;d.mkdir(parents=True,exist_ok=True);ss=g.sites(root)
    (d/'sites.json').write_text(json.dumps(ss,indent=2)+'\n')
    (d/'sites.txt').write_text(''.join(f'{p} {o} {r if r is not None else 0}\n' for p,o,r in ss))
    (d/'table_k230labels.tm').write_text(encode(table))
    receipt.update(source_sha256=sha(d/'sites.json'),table_sha256=sha(d/'table_k230labels.tm'),metrics=g.metrics(root),states=len(table)//2)
    (d/'certificate.json').write_text(json.dumps(receipt,indent=2)+'\n');return receipt
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,default=HERE/'generated');a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    tablepath=HERE/'inputs/k230.tm';sitepath=HERE/'inputs/sites230.json'
    assert sha(tablepath)==PIN_TABLE and sha(sitepath)==PIN_SITES
    original=read_table(tablepath);assert len(original)==460
    root=g.tree(normalize(json.loads(sitepath.read_text())));initial=root;table=dict(original);stages=[]
    stages.append(save_stage(a.out,'00_k230',root,table,{'status':'EXACT_FROZEN_K230_INPUT','raw_source_sha256':PIN_SITES}))
    hpaths=[]
    def find_h(t,p=''):
        if t==H_OLD:hpaths.append(p);return
        if not g.is_leaf(t):find_h(t[0],p+'0');find_h(t[1],p+'1')
    find_h(root);assert len(hpaths)==4
    assert g.boundary(H_OLD)==g.boundary(H_NEW)==(0,0,False)
    @cache
    def repl(t):return H_NEW if t==H_OLD else t if g.is_leaf(t) else (repl(t[0]),repl(t[1]))
    root=repl(root)
    assert table[121,0]==(0,1,31) and table[121,1]==(1,1,63)
    table[121,0]=(0,1,63);table[121,1]=(1,1,13)
    stages.append(save_stage(a.out,'01_h_rotation230',root,table,{'status':'FOUR_CLOSED_H_IDENTITIES','replacement_prefixes':hpaths,'before_macro':H_OLD,'after_macro':H_NEW,'contract':'R5=a,R6=b maps to R5=a+b+1,R6=0; other registers unchanged; terminates for all natural a,b.'}))
    hreference=g.graph(g.sites(root))
    # Compose inherited positive-block native reductions.
    table={(q,b):(w,d,63 if z==79 else 71 if z==140 else z) for(q,b),(w,d,z) in table.items() if q not in(79,140)}
    table[63,0]=(0,-1,123);table[63,1]=(1,-1,30)
    table[71,0]=(0,-1,91);table[80,1]=(1,-1,138)
    assert len(table)==456
    stages.append(save_stage(a.out,'02_h_delayed228',root,table,{'status':'TWO_INHERITED_NATIVE_FOLDS','deleted_states':[79,140],'local_proofs':'See native backend certificates for H and delayed erasure.'}))
    boundary=[]
    for p in ['11101001001','111010010011']:
        (x,y),z=at(root,p);root=put(root,p,(x,(y,z)))
        assert g.graph(g.sites(root))[1:]==hreference[1:]
        boundary.append({'prefix':p,'direction':'right','chunk_boundaries':list(map(g.boundary,(x,y,z))),'chunk_leaf_counts':[len(g.sites(v)) for v in(x,y,z)]})
    assert table[52,0]==(0,1,67) and table[52,1]==(0,-1,27)
    assert table[67,0]==(0,1,76) and table[67,1]==(1,1,229)
    assert table[229,0]==(0,1,204) and table[229,1]==(1,1,228)
    assert table[103,1]==(0,-1,52) and table[162,1]==(0,-1,27)
    table[52,0]=(0,1,76);table[52,1]=(1,1,67)
    table[67,0]=(0,1,204);table[67,1]=(1,1,229)
    table[229,0]=(0,1,228);table[229,1]=(0,-1,103);table[103,1]=(0,-1,162)
    stages.append(save_stage(a.out,'03_boundary228',root,table,{'status':'ALL_6656_SOURCE_GUARDS_PRESERVED','boundary_rotations':boundary}))
    closed=[]
    for number,(q,q2,direction) in enumerate(ROTATIONS,1):
        root,table,cert=g.stage(root,table,q,q2,direction)
        assert g.graph(g.sites(root))[1:]==hreference[1:];closed.append(cert)
        stages.append(save_stage(a.out,f'rotation_{number}',root,table,{'status':'ALL_6656_SOURCE_GUARDS_PRESERVED','rotation':cert}))
        if number==3:
            rejected=dict(table);rejected[150,1]=(1,-1,173);rejected[155,1]=rejected[176,1]=(1,1,150)
            rejected={(p,bit):(w,d,152 if z==175 else z) for(p,bit),(w,d,z) in rejected.items() if p!=175}
            rejected[152,0]=(0,-1,159);rejected[152,1]=(1,-1,169)
            rejected_receipt=save_stage(a.out,'rejected227_zero7',root,rejected,{'status':'REJECTED_NATIVE_SCANNER_COUNTEREXAMPLE','failing_leaf':1042,'instruction':['CD',2],'path':'11101001001110010000000','scope':'Exact rejected control; full counterexample trace is in the native evidence packet.'})
            assert rejected_receipt['table_sha256']=='0ebe027040e7d7705d8f44db8903f1bc23814e29876353d3bfeaf49473fa9e4f'
    # All source changes are now complete. Preserve the 228-state fold basis.
    basis=dict(table)
    stages.append(save_stage(a.out,'04_rotated_basis228',root,basis,{'status':'SOURCE_ROTATIONS_COMPLETE','closed_rotations':closed}))
    # Reassign the pi role to pp-state150, and zi to W-state152.
    assert table[150,0]==(0,1,90) and table[150,1]==(1,1,90)
    assert table[155,1]==table[176,1]==(1,1,175)
    table[150,1]=(1,-1,173);table[155,1]=table[176,1]=(1,1,150)
    assert sorted((q,b) for(q,b),v in table.items() if v[2]==175)==[(184,0)]
    table={(q,b):(w,d,152 if z==175 else z) for(q,b),(w,d,z) in table.items() if q!=175}
    table[152,0]=(0,-1,159);table[152,1]=(1,-1,169)
    assert len(table)==454 and {q for q,b in table}==set(range(230))-{79,140,175}
    final=save_stage(a.out,'05_k227',root,table,{'status':'EXACT_K227_CONSTRUCTION','deleted_states':[79,140,175],
        'retained_edits_vs_basis':[{'row':row,'before':basis[row],'after':table[row]} for row in sorted(table) if table[row]!=basis[row]],
        'guarded_cases':6656,'scope':'Construction and source certificate. Verify native roles and complete runtime separately.'})
    assert final['table_sha256']==FINAL_TABLE and final['source_sha256']==FINAL_SOURCE
    order=sorted({q for q,b in table});renumber={q:i for i,q in enumerate(order)}|{230:227}
    canonical={(renumber[q],b):(w,d,renumber[z]) for(q,b),(w,d,z) in table.items()}
    (a.out/'05_k227/k227.tm').write_text(encode(canonical))
    (a.out/'05_k227/renumbering.json').write_text(json.dumps({'k230_to_k227':renumber},indent=2)+'\n')
    report={'status':'EXACT_K227_SOURCE_AND_TABLE_PASS','input_table_sha256':PIN_TABLE,'input_source_sha256':PIN_SITES,
       'final_table_k230labels_sha256':final['table_sha256'],'final_table_canonical_sha256':sha(a.out/'05_k227/k227.tm'),
       'final_source_sha256':FINAL_SOURCE,'working_states':227,'transition_rows':454,'source_leaves':5121,'guarded_cases':6656,
       'h_replacements':4,'boundary_rotations':2,'closed_rotations':5,'source_metrics':g.metrics(root),'stages':stages}
    (a.out/'construction.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='stages'},indent=2))
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Run with assertions enabled')
    main()
