#!/usr/bin/env python3
"""Build an exact multi-entry component library, never a complete proof TM.

Only proof-backed read domains enable symbol packing. Return ports are distinct
external labels without rows. Failure states are counted and kept distinct.
Every row and entry is projected, including arbitrary incoming edges.
"""
if not __debug__: raise RuntimeError('Assertions must be enabled')
from pathlib import Path
import sys,json,hashlib,argparse
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path[:0]=[str(ROOT/'architectures'),str(ROOT/'native_copier'),str(ROOT/'arithmetic_core')]
import pattern_oracle as O
import encoded_native_edge as N
import anchor_mode_writer as W
import reverse_path_copy as R
import tag_edge as E
import unary_locator as L
import biased_reference_copy19 as C


def build(*,full=True,reverse_guards=False,oracle_direction='R'):
    rows={};entries={};ports={};domains={};proofs={};ledger={};protected=set();names={}
    def add(prefix,table,oldports,entry,forced,labels=None,failure=None):
        working=sorted({q for q,b in table})
        ledger[prefix]={'working_states':len(working),'rows':len(table)}
        def key(q):return f'{prefix}:{q}'
        for q in working:
            names[key(q)]={'component':prefix,'local_state':q,'role':str(labels[q]) if labels else str(q)}
            domains[key(q)]=[0,1]
        for q,label in oldports.items():ports[key(q)]={'component':prefix,'name':label,'status':'UNLINKED_EXTERNAL_PORT'}
        for (q,b),(w,d,t) in table.items():
            assert t in working or t in oldports
            rows[key(q),b]=(w,d,key(t))
        entries.update({f'{prefix}.{label}':key(q) for label,q in entry.items()})
        for q,(b,proof) in forced.items():domains[key(q)]=[b];proofs[key(q)]=proof
        for q in failure or []:protected.add(key(q));names[key(q)]['distinguished_failure']=True
    _,_,templates=O.load_source();oracle=O.compile_oracle(templates)
    ot={k:(w,oracle_direction,t)for k,(w,d,t)in oracle['table'].items()}
    of={q:(0,'ORACLE_PADDING: genuine complete leaf path followed by at least three untouched zero cells; fresh cells consumed monotonically.')for q in range(oracle['constructors'],oracle['halt'])}
    add('oracle',ot,{oracle['halt']:'ORACLE_RETURN'},{f'rule_{k}':v for k,v in oracle['roots'].items()},of)
    nt,ns,nr,nj,nn=N.compile_step();nf={q:(1,why)for q,why in [(13,'NATIVE_CHILD: successful tag check selects first one of nonempty biased reference.'),(40,'NATIVE_NEXT: locator advances only with positive index and valid next record, whose first tag cell is one.'),(48,'NATIVE_COUNTER: copier returns exactly on rightmost counter one.'),(52,'NATIVE_RESET: copy restored the selected source and every tag; record zero first tag cell is one.') ]}
    add('native',nt,{nr:'NATIVE_SUCCESS'},{'fetch':ns},nf,nn,[nj])
    wt,we,wr,wi=W.compile_writer();wf={wi[n]:(1,'WRITER_COMPLETE_16: all four old and new modes; reads only seven header cells; see anchor_mode_writer_guards.json.')for n in ('unseen4','seen0','seen1','seen2')}
    add('writer',wt,{wr:'WRITER_RETURN'},{f'mode_{k}':q for k,q in we.items()},wf,{v:k for k,v in wi.items()},[wi['reject']])
    if full:
        rt,rs,rr,ri=R.compile_copy();rf={}
        if reverse_guards:
            for n in ('payload1','payload2',('mark_previous',0),('mark_previous',1)):
                rf[ri[n]]=(1,'REVERSE_FIELD: branch fields have length3 or4 and sentinel length5; restored marker is their last one, preceding required payload and previous-field last cells are ones.')
            for n in ('restore','append'):
                rf[ri[n]]=(0,'REVERSE_MARKER: restore enters on erased last-one marker; append enters first untouched gap zero with capacity n+2.')
        add('reverse',rt,{rr:'REVERSE_RETURN'},{'restore':rs},rf,{v:k for k,v in ri.items()},[ri['reject']])
        prefixes=['']+[format(i,f'0{d}b') for d in (1,2,3)for i in range(2**d)if i<<(4-d)<12]
        si={p:i for i,p in enumerate(prefixes)};st={};sp={12:'RULE_0',13:'RULE_1',14:'RULE_2',15:'SELECT_REJECT'}
        # Other rule exits get linked to actual oracle roots below.
        sp.update({16+k:f'RULE_{k}'for k in oracle['roots']})
        for p,q in si.items():
            for b in range(2):
                nxt=p+str(b)
                if int(nxt,2)<<(4-len(nxt))>=12:t=15
                elif len(nxt)==4:t=12+int(nxt,2) if int(nxt,2)<3 else 16+int(nxt,2)
                else:t=si[nxt]
                st[q,b]=(b,oracle_direction,t)
        add('selector',st,sp,{'root':0},{}, {v:k for k,v in si.items()})
        for k,q in oracle['roots'].items():
            old=f'selector:{16+k}';target=f'oracle:{q}'
            rows={key:(w,d,target if t==old else t)for key,(w,d,t)in rows.items()};ports.pop(old)
        # Direction reflected together with the oracle, if selected. Seek contract:
        # at zero gap followed (in direction) by positive one block then zero.
        rev='L' if oracle_direction=='R' else 'R'
        add('seek',{(0,0):(0,oracle_direction,0),(0,1):(1,oracle_direction,1),(1,1):(1,oracle_direction,1),(1,0):(0,rev,2)}, {2:'SEEK_COUNTER_RETURN'},{'gap':0},{})
        add('boundary',{(0,0):(1,oracle_direction,1),(0,1):(1,oracle_direction,2)}, {1:'BOUNDARY_RETURN',2:'BOUNDARY_INVALID'},{'write':0},{0:(0,'BOUNDARY_ZERO: entry is the first untouched zero immediately beyond three emitted leaf bits; caller must prove a fourth zero padding cell.')})
    assert len(rows)==2*len(domains)
    return dict(rows=rows,entries=entries,ports=ports,domains=domains,proofs=proofs,ledger=ledger,protected=protected,names=names,oracle=oracle)


def build_retained(*,reverse_guards=False,selector_guards=False,comparator27=False,include_compare=True,omit_unreachable_query=False):
    """Current actual inventory: retained query133, native68, writer11, compare29."""
    import retained_template_query as Q
    import compare_biased_counter as K
    data=build(full=False)
    for field in ('rows','entries','ports','domains','proofs','names'):
        data[field]={k:v for k,v in data[field].items() if not ((k[0]if isinstance(k,tuple)else k).startswith('oracle:') or (isinstance(k,str)and k.startswith('oracle.')))}
    data['ledger'].pop('oracle')
    def add(pref,table,entries,ports,guards,names,failure):
        working=sorted({q for q,b in table});key=lambda q:f'{pref}:{q}'
        data['ledger'][pref]={'working_states':len(working),'rows':len(table)}
        for(q,b),(w,d,t)in table.items():data['rows'][key(q),b]=(w,d,key(t))
        for q in working:
            data['domains'][key(q)]=[0,1];data['names'][key(q)]={'component':pref,'local_state':q,'role':str(names.get(q,q))}
        for q,(bits,why)in guards.items():data['domains'][key(q)]=bits;data['proofs'][key(q)]=why
        for label,q in entries.items():data['entries'][f'{pref}.{label}']=key(q)
        for q,label in ports.items():data['ports'][key(q)]={'component':pref,'name':label,'status':'UNLINKED_EXTERNAL_PORT'}
        for q in failure:data['protected'].add(key(q));data['names'][key(q)]['distinguished_failure']=True
    qt,qs,qr,o=Q.compile_query();_,_,cr,ci=R.compile_copy()
    qg={cr+q:([0],'RETAINED_ORACLE_PADDING: source contains exactly four valid rule bits and one complete leaf path; counter-origin cells c-1,c-2,c-3 are zero and untouched by copier; mirrored oracle reads these fresh cells.')for q in range(o['constructors'],o['halt'])}
    qn={v:k for k,v in ci.items()}
    if reverse_guards:
        for n in ('payload1','payload2',('mark_previous',0),('mark_previous',1)):
            qg[ci[n]]=([1],'REVERSE_FIELD_INDUCTION: restored last-cell marker lies in a length3/4 branch field or length5 sentinel; first two preceding payload cells and previous-field last cells are ones.')
        for n in ('restore','append'):
            qg[ci[n]]=([0],'REVERSE_MARKER_INDUCTION: restore reads the erased last cell; append reads an untouched counter-gap zero under capacity n+2.')
    add('query',qt,{'start':qs},{qr:'QUERY_RETURN'},qg,qn,[ci['reject']])
    kt,ks,kp,ki,aliases,forced=K.compile_compare()
    if comparator27:
        import compare_biased_counter27 as K27
        kt,ks,kp,ki=K27.compile_compare()
    kg={ki[n]:([0],'COMPARE_MARKER_INDUCTION: designated erased source/counter cell, established in compare_biased_counter_PROOF.md.')for n in ('init','back_one','restore_old_left','restore_exhausted','failed_restore_left','restore_right','restore_left')}
    if comparator27:kg[ki['dummy_counter_one']]=([0],'COMPARE27_DUMMY: exhausted counter cell c+1 has been cleared, or was original blank; requires loaded counter gap at least THREE.')
    add('compare',kt,{'start':ks},{q:label for label,q in kp.items()},kg,{v:k for k,v in ki.items()},[ki['reject']])
    # Import all reviewed native zero guards too; proofs are source/hash bound.
    cert=json.loads((ROOT/'verification/encoded_native_edge_68_guards_reviewed.json').read_text())
    assert hashlib.sha256((ROOT/'architectures/encoded_native_edge_68.tm').read_bytes()).hexdigest()==cert['table_sha256']
    for q,bits in cert['allowed_reads'].items():
        key=f'native:{q}';data['domains'][key]=bits
        if len(bits)==1:data['proofs'][key]=cert['proof_reasons'][q]
    if selector_guards:
        assert reverse_guards
        qc=json.loads((ROOT/'verification/retained_template_query_133_guards_reviewed.json').read_text())
        assert hashlib.sha256((ROOT/'architectures/retained_template_query_133.tm').read_bytes()).hexdigest()==qc['table_sha256']
        for q,bits in qc['allowed_reads'].items():
            data['domains'][f'query:{q}']=bits
            if len(bits)==1:data['proofs'][f'query:{q}']='REVIEWED_RETAINED_QUERY: '+str(qc.get('proof_reasons',{}).get(q,'See retained_template_query_133_guards_reviewed.json and its universal composition proof.'))
    if not include_compare:
        for field in ('rows','entries','ports','domains','proofs','names'):
            data[field]={k:v for k,v in data[field].items()if not((k[0]if isinstance(k,tuple)else k).startswith('compare:')or(isinstance(k,str)and k.startswith('compare.')))}
        data['protected']={q for q in data['protected']if not q.startswith('compare:')};data['ledger'].pop('compare')
    if omit_unreachable_query:
        assert selector_guards
        reachable=set(data['entries'].values());todo=list(reachable)
        while todo:
            q=todo.pop()
            if q not in data['domains']:continue
            for b in data['domains'][q]:
                t=data['rows'][q,b][2]
                if t not in reachable:reachable.add(t);todo.append(t)
        dead='query:127';assert dead not in reachable and dead not in data['entries'].values()
        data['reachability_certificate']={'entry_states':list(data['entries'].values()),'reachable_states':sorted(reachable),'excluded_state':dead,'all_incoming_rows':[[q,b,b in data['domains'][q]]for(q,b),(w,m,t)in data['rows'].items()if t==dead],'scope':'Admitted-row reachability from documented component entries only; new internal entry invalidates the proof.'}
        data['domains'][dead]=[];data['proofs'][dead]='UNREACHABLE_ADMITTED_GRAPH: no path from any documented entry in the allowed-row graph; only incoming query124/read0 is forbidden.'
    data['build_options']={'reverse_guards':reverse_guards,'selector_guards':selector_guards,'comparator27':comparator27,'include_compare':include_compare,'omit_unreachable_query':omit_unreachable_query}
    return data


def quotient(data):
    rows=data['rows'];working=sorted(data['domains']);ports=data['ports'];protected=data['protected']
    # Universal bisimulation on the full binary table, with all terminal and
    # distinguished failure states protected. No read invariant is used here.
    block={q:0 for q in working}
    for i,q in enumerate(sorted(protected),1):block[q]=i
    for i,q in enumerate(sorted(ports),1+len(protected)):block[q]=i
    while True:
        signatures={};new={}
        for q in working:
            sig=('protected',q) if q in protected else tuple((w,d,block[t])for b in (0,1)for w,d,t in [rows[q,b]])
            if sig not in signatures:signatures[sig]=len(signatures)
            new[q]=signatures[sig]
        for q in ports:new[q]=len(signatures)+list(sorted(ports)).index(q)
        equivalent=all((block[a]==block[b])==(new[a]==new[b])for a in block for b in block)
        block=new
        if equivalent:break
    groups={}
    for q in working:groups.setdefault(block[q],[]).append(q)
    universal=[sorted(v)for k,v in sorted(groups.items())]
    domains=[sorted(set(b for q in g for b in data['domains'][q]))for g in universal]
    zeros=[i for i,a in enumerate(domains)if a==[0]];ones=[i for i,a in enumerate(domains)if a==[1]]
    pairs=list(zip(zeros,ones));merged={b:a for a,b in pairs}
    classes={}
    for i,g in enumerate(universal):classes.setdefault(merged.get(i,i),[]).extend(g)
    classes=list(classes.values());projection={q:i for i,g in enumerate(classes)for q in g}
    port_ids={q:len(classes)+i for i,q in enumerate(sorted(ports))};projection.update(port_ids)
    out={};structural=[]
    for q2,g in enumerate(classes):
        for b in (0,1):
            eligible=[q for q in g if b in data['domains'][q]]
            # A still-forced unpaired class has an irrelevant other row, which
            # is totalized with any member's original row; no new port is hidden.
            chosen=eligible[0]if eligible else g[0]
            w,d,t=rows[chosen,b];out[q2,b]=(w,d,projection[t])
            for q in eligible:
                w0,d0,t0=rows[q,b]
                assert (w0,d0,projection[t0])==out[q2,b],(q,b,g)
                structural.append([q,b,q2,w0,d0,projection[t0]])
    return dict(table=out,projection=projection,classes=classes,universal_classes=universal,pairs=pairs,ports=port_ids,entries={k:projection[q]for k,q in data['entries'].items()},structural=structural)


def save(data,result,out):
    out.mkdir(parents=True,exist_ok=True);N=len(result['classes'])
    lines=[f'# MULTI_ENTRY_LIBRARY working_states={N}; no global start; no global halt', '# External ports have no rows and remain separately charged when linked.']
    for k,q in result['entries'].items():lines.append(f'# ENTRY {k} {q}')
    for q,i in result['ports'].items():lines.append(f'# PORT {i} {q} {data["ports"][q]["name"]}')
    lines += [f'{q} {b} {w} {d} {t}'for(q,b),(w,d,t)in sorted(result['table'].items())]
    content='\n'.join(lines)+'\n';(out/'library.tm').write_text(content)
    manifest={k:v for k,v in result.items()if k not in ('table','structural')}
    manifest.update({'scope':'Prepared-frame multi-entry library; all external ports unlinked; no complete TM state bound.', 'build_options':data.get('build_options',{}),'reachability_certificate':data.get('reachability_certificate'),'component_ledger':data['ledger'],'input_working_states':len(data['domains']),'working_states':N,'rows':len(result['table']),'external_port_count':len(data['ports']),'universal_bisimulation_savings':len(data['domains'])-len(result['universal_classes']),'forced_symbol_savings':len(result['pairs']),'domains':data['domains'],'guard_justifications':data['proofs'],'state_roles':data['names'],'external_ports':data['ports'],'sha256':hashlib.sha256(content.encode()).hexdigest()})
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    (out/'row_projection_certificate.json').write_text(json.dumps({'checked_allowed_rows':len(result['structural']),'rows':result['structural']},indent=2)+'\n')
    return manifest

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--core-only',action='store_true');p.add_argument('--inventory',choices=['loose','retained'],default='loose');p.add_argument('--reverse-guards',action='store_true');p.add_argument('--selector-guards',action='store_true');p.add_argument('--comparator27',action='store_true');p.add_argument('--without-comparator',action='store_true');p.add_argument('--direction',choices=['L','R'],default='R');p.add_argument('--output',type=Path,default=HERE/'full');a=p.parse_args()
    data=build_retained(reverse_guards=a.reverse_guards,selector_guards=a.selector_guards,comparator27=a.comparator27,include_compare=not a.without_comparator) if a.inventory=='retained' else build(full=not a.core_only,reverse_guards=a.reverse_guards,oracle_direction=a.direction);r=quotient(data);m=save(data,r,a.output)
    print(json.dumps({k:m[k]for k in ('input_working_states','working_states','rows','external_port_count','universal_bisimulation_savings','forced_symbol_savings','sha256')},indent=2))
