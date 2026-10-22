#!/usr/bin/env python3
"""Three closed layouts around the provider188 source decoder; no search."""
import sys
sys.dont_write_bytecode=True
import argparse,hashlib,json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
REF=ROOT.parent if (ROOT.parent/'k215.tm').exists() else ROOT.parent/'deliverable'

def minimize(T):
    states=sorted({q for q,b in T});halt=254
    assert all(z in states or z==halt for w,d,z in T.values())
    labels={q:0 for q in states};labels[halt]=1
    while True:
        signatures={q:tuple((w,d,labels[z])for b in (0,1)for w,d,z in [T[q,b]])for q in states}
        groups={};new={halt:-1}
        for q in states:
            key=signatures[q]
            if key not in groups:groups[key]=len(groups)
            new[q]=groups[key]
        old_pairs={(p,q)for p in states for q in states if labels[p]==labels[q]}
        new_pairs={(p,q)for p in states for q in states if new[p]==new[q]}
        if old_pairs==new_pairs:
            classes={}
            for q in states:classes.setdefault(new[q],[]).append(q)
            return dict(working_classes=len(classes),nontrivial_classes=[g for g in classes.values()if len(g)>1])
        labels=new

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--code-dir',type=Path,default=ROOT/'reference');ap.add_argument('--reference',type=Path,default=REF/'reference/k215');ap.add_argument('--out',type=Path,default=ROOT/'layout188_results.json');a=ap.parse_args()
    assert __debug__ and not sys.flags.optimize, 'Assertions must be enabled'
    bound=json.loads((ROOT/'layout_reference_bindings.json').read_text())
    for item in bound['files']:
        p=a.code_dir/Path(item['local_path']).name;raw=p.read_bytes()
        assert hashlib.sha256(raw).hexdigest()==item['sha256']
        assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==item['git_blob_sha1']
    sys.path.insert(0,str(a.code_dir));import source_language as s,build221 as b
    T=b.read_table((a.reference/'k215.native.tm').read_bytes());sites=json.loads((a.reference/'sites215.json').read_text());tree=s.tree(sites)
    canonical=json.loads((a.reference/'canonicalization.json').read_text());dense={int(k):int(v)for k,v in canonical['native_to_canonical'].items()};inv={v:k for k,v in dense.items()}
    groups,paths=b.decoder_map(T,tree)
    roles=[]
    for d in [95,188,213]:
        q=inv[d];assert len(groups[q])==1
        subtree=next(iter(groups[q]));ctx=paths[q]
        roles.append(dict(dense=d,native=q,rows={str(bit):[w,di,dense[z]]for bit in (0,1)for w,di,z in [T[q,bit]]},
                          incoming_dense=[[dense[st],bit,w,di]for (st,bit),(w,di,z)in sorted(T.items())if z==q],
                          prefixes=ctx,subtree_leaves=s.sites(subtree),boundary=s.boundary(subtree),
                          occurrence_site_intervals=[[min(i for i,row in enumerate(sites)if row[0].startswith(p)),max(i for i,row in enumerate(sites)if row[0].startswith(p))]for p in ctx]))
    P='11010010011101';A,(B,C)=s.subtree(tree,P)
    assert B==(('CD',7),(('CI',6),('CC',2)))
    assert C==(('CD',4),(('CI',5),('CC',2)))
    assert all(s.boundary(x)==(0,0,False)for x in [A,B,C])
    q=next(q for q,ps in paths.items()if ps==[P]);r=inv[188]
    assert paths[r]==[P+'1'] and T[q,1][2]==r
    assert all(T[v,bit][:2]==(bit,1)for v in [q,r]for bit in [0,1])
    aa,bb,cc=T[q,0][2],T[r,0][2],T[r,1][2]
    oldcfg,_=s.graph_arithmetic(sites)
    baseline=dict(metrics=s.metrics(tree),decoder_states=len(groups),minimization=minimize(T))
    layouts=[('A_(C_B)',(A,(C,B)),((aa,r),(cc,bb))),
             ('(A_B)_C',((A,B),C),((r,cc),(aa,bb))),
             ('(A_C)_B',((A,C),B),((r,bb),(aa,cc)))]
    results=[]
    for name,tr,targets in layouts:
        U=dict(T)
        for v,ts in zip([q,r],targets):
            for bit,z in enumerate(ts):U[v,bit]=(bit,1,z)
        newtree=s.replace(tree,P,tr);newsites=s.sites(newtree)
        gg,pp=b.decoder_map(U,newtree)
        assert gg[q]=={tr}
        assert gg[r]=={tr[1] if name=='A_(C_B)' else tr[0]}
        old_at={p:v for v,ps in paths.items() for p in ps}
        substitutions={'A_(C_B)':[('0','0'),('10','11'),('11','10')],
                       '(A_B)_C':[('00','0'),('01','10'),('1','11')],
                       '(A_C)_B':[('00','0'),('01','11'),('1','10')]}[name]
        expected={};context_changes=[]
        for v,ps in pp.items():
            for prefix in ps:
                if prefix==P:old_prefix=P
                elif prefix==P+('1' if name=='A_(C_B)' else '0'):old_prefix=P+'1'
                elif prefix.startswith(P):
                    tail=prefix[len(P):]
                    matches=[P+old+tail[len(new):] for new,old in substitutions if tail.startswith(new)]
                    assert len(matches)==1
                    old_prefix=matches[0]
                else:old_prefix=prefix
                if old_at[old_prefix]!=v:
                    context_changes.append(dict(new_prefix=prefix,old_prefix=old_prefix,new_native=v,old_native=old_at[old_prefix]))
                expected.setdefault(v,set()).add(s.subtree(newtree,prefix))
        assert gg==expected
        cfg,_=s.graph_arithmetic(newsites);assert cfg==s.graph_intervals(newsites)
        same_word=[row[1:]for row in newsites]==[row[1:]for row in sites]
        if same_word:assert cfg==oldcfg
        raw=b.table_bytes(U)
        results.append(dict(name=name,metrics=s.metrics(newtree),decoder_states=len(gg),listed_working_states=len(U)//2,minimization=minimize(U),
                            primitive_word_equal=same_word,ordinal_guarded_cfg_equal=cfg==oldcfg,
                            mapped_prefix_state_changes=context_changes,
                            physical_certification='Only known-prefix motion and listed-state Mealy refinement checked; literal leaf-entry correspondence and full runtime not checked. A source subtree move may change context-sensitive decoder controls.',
                            source_safety='Three factors are syntactically closed. The order-preserving rotation preserves the guarded ordinal CFG; the other two reorder only the disjoint total transfers R7→R6 and R4→R5, which commute on every natural register file. This source fact does not certify the binary rewire.',
                            changed_native_rows=[[v,bit,*U[v,bit]]for v in [q,r]for bit in (0,1)if U[v,bit]!=T[v,bit]],
                            native_table_sha256=hashlib.sha256(raw).hexdigest(),source_sha256=hashlib.sha256((json.dumps(newsites,separators=(',',':'))+'\n').encode()).hexdigest()))
    out=dict(status='THREE_CONCRETE_CLOSED_LAYOUTS_CHECKED',parent_native=q,parent_dense=dense[q],provider_native=r,provider_dense=188,
             parent_prefix=P,factor_boundaries=[s.boundary(x)for x in [A,B,C]],factor_leaf_counts=[len(s.sites(x))for x in [A,B,C]],
             roles=roles,append_helper=dict(dense=189,native=inv[189],decoder_prefixes=paths.get(inv[189],[]),rows={str(bit):[w,di,dense[z]]for bit in (0,1)for w,di,z in [T[inv[189],bit]]},incoming_dense=[[dense[st],bit,w,di]for (st,bit),(w,di,z)in sorted(T.items())if z==inv[189]]),baseline=baseline,variants=results,
             scope='Exact finite known-prefix traversal, source metrics, and physical Mealy-state minimization for these three particular rotations/swaps. Context-sensitive decoding means prefix traversal alone is not a literal leaf-entry or runtime certificate for the rewired tables. No global optimum claim, no arbitrary source search, no new kernel theorem or binary consistency calibration.',
             hashes={str(p):hashlib.sha256(p.read_bytes()).hexdigest()for p in [a.code_dir/'source_language.py',a.code_dir/'build221.py',a.reference/'k215.native.tm',a.reference/'sites215.json',a.reference/'canonicalization.json',Path(__file__)]})
    a.out.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(baseline=baseline,variants=[{k:r[k]for k in ['name','metrics','decoder_states','listed_working_states','minimization']}for r in results]),indent=2))

if __name__=='__main__':main()
