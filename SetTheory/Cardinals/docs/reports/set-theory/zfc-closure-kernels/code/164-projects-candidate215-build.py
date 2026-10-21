#!/usr/bin/env python3
"""Deterministically rebuild the primary K215 composition using only stdlib.

Authenticates both unchanged public K216 archives. Reconstructs the source by
four closed interval splices and command permutation. Applies the explicit row
recipe and checks its fixed decoder assignment, both guarded CFG resolvers,
all internal decoder prefixes, and canonicalization. The full quantified
runtime and complete blank prefix are separate freshly replayed certificates.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import sys
import zipfile
from collections import defaultdict

HERE = Path(__file__).resolve().parent

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def dump(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=HERE/'rebuilt')
    ap.add_argument('--partial-archive',type=Path)
    ap.add_argument('--permuted-archive',type=Path)
    ap.add_argument('--secondary',action='store_true',help='Also reproduce the exploratory120 variant; no full runtime certificate is asserted for120')
    args=ap.parse_args()
    require(__debug__ and not sys.flags.optimize,'Run Python without -O')
    pins=json.loads((HERE/'SOURCE_PINS.json').read_bytes())
    archives={}
    for name,item in pins['archives'].items():
        override=args.partial_archive if name=='partial'else args.permuted_archive
        path=override if override is not None else HERE/item['relative_path']
        raw=path.read_bytes()
        require(sha(raw)==item['sha256'],'Predecessor archive hash: '+name)
        archives[name]=zipfile.ZipFile(io.BytesIO(raw))
    inputs={}
    for name,item in pins['inputs'].items():
        archive=archives[item['archive']]
        if 'nested_archive' in item:
            archive=zipfile.ZipFile(io.BytesIO(archive.read(item['nested_archive'])))
        raw=archive.read(item['member'])
        require(sha(raw)==item['sha256'],'Authenticated input hash: '+name)
        require(raw==(HERE/'inputs'/name).read_bytes(),'Unchanged extracted input: '+name)
        inputs[name]=raw
    for name,item in pins['vendor'].items():
        require(sha((HERE/'vendor'/name).read_bytes())==item['sha256'],'Vendor file hash: '+name)
    sys.path.insert(0,str(HERE/'vendor'))
    import source_language as s
    import source_splice as sp
    import build221 as b
    import audit_command_permutation as audit
    old=s.tree(json.loads(inputs['partial216.sites.json']))
    original=s.tree(json.loads(inputs['sites217.json']))
    t219=s.tree(json.loads(inputs['sites219.json']))
    def graphs(tree):
        rr=s.sites(tree)
        g=s.graph_intervals(rr)
        require(g==s.graph_arithmetic(rr)[0],'Independent guarded graph agreement')
        return g
    require(graphs(old)==graphs(original),'Partial-selector source is guarded-CFG equivalent to inherited K217')
    read_d=sp.serial(sp.closed_forest(t219,23,37))
    load_d=sp.serial(sp.closed_forest(t219,40,66))
    walk11,transfer3=read_d
    require([sp.size(walk11),sp.size(transfer3),sp.size(load_d)]==[11,3,26],'Read/load source factor widths')
    require(all(s.boundary(x)==(0,0,False)for x in(walk11,transfer3,load_d)),'Closed read/load reassociation')
    read_then_load=(walk11,(transfer3,load_d))
    frozen=sp.apply_closed_splices(old,{(23,37):None,(187,201):None,(228,254):read_then_load,(4659,4685):read_then_load})
    public_frozen=s.tree(json.loads(inputs['permuted-frozen202.json']))
    require(graphs(frozen)==graphs(public_frozen),'Composition preserves calibrated MP-only guarded CFG')
    base=b.read_table(inputs['partial216.native.tm'])
    require(len(base)==432,'Partial-selector216 state census')
    groups,_=b.decoder_map(base,old)
    old_states=defaultdict(set)
    for q,nn in groups.items():
        for n in nn:
            old_states[n].add(q)
    args.output.mkdir(parents=True,exist_ok=True)
    reports=[]
    for name in (('210','120')if args.secondary else('210',)):
        permutation=tuple(map(int,name))
        tree=audit.permute(frozen,permutation)
        rows=s.sites(tree)
        target=s.tree(json.loads(inputs[f'permuted{name}.sites.json']))
        require(graphs(tree)==graphs(target),'Exact calibrated guarded CFG, permutation'+name)
        require(s.metrics(tree)==dict(dag_nodes=202,leaf_occurrences=4751,maximum_depth=47,maximum_zero_run=6),'Composed source census')
        # The independent public source checker also resolves all guards, traces
        # the four selector classes, and checks each closed body's return route.
        require(audit.structured_graph(tree)==audit.counter_graph(audit.sites(tree)),'Third-party independent source resolver agreement')
        selectors,fields,packed=audit.selector_audit(tree,permutation)
        returns=audit.return_audit(tree,permutation)
        public_selectors,public_fields,public_packed=audit.selector_audit(target,permutation)
        require(fields==public_fields and packed==public_packed,'Inherited command wire format')
        require(selectors==public_selectors,'Exact selector partition')
        recipe=json.loads((HERE/'recipes'/f'table{name}.json').read_bytes())
        require(sha(inputs['partial216.native.tm'])==recipe['baseline_sha256'],'Exact recipe parent')
        table=dict(base)
        keys=set()
        for item in recipe['rows']:
            key=item['state'],item['read']
            require(key not in keys,'Duplicate row recipe key')
            keys.add(key)
            require(table.get(key)==(tuple(item['old'])if item['old']is not None else None),'Row recipe precondition '+str(key))
            if item['new']is None:
                del table[key]
            else:
                table[key]=tuple(item['new'])
        native=b.table_bytes(table)
        require(sha(native)==recipe['candidate_sha256'],'Exact native output hash')
        source=s.compact(rows)
        require(sha(source)==recipe['source_sha256'],'Exact source output hash')
        states={q for q,bit in table}
        require(len(states)==215 and len(table)==430,'215 total working states and430 rows')
        require(set(table)=={(q,bit)for q in states for bit in(0,1)},'Total binary table')
        require({z for w,d,z in table.values()}-states=={254},'Unique external halt')
        require(sorted({q for q,bit in base}-states)==[185]and not(states-{q for q,bit in base}),'Deletes exactly native185 from Partial216')
        require(sum(table.get(k)!=row for k,row in base.items()if k in table)==36,'36 changed retained rows')
        require(table[81,0]==(0,-1,111),'Inherited local81 repair is present')
        for q,bit in recipe['protected_rows']:
            require(table[q,bit]==base[q,bit],'Protected arithmetic/helper row retained')
        # Reconstruct the fixed correspondence, without a solver.
        live=set()
        def visit(n):
            if s.leaf(n)or n in live:
                return
            live.add(n)
            visit(n[0]);visit(n[1])
        visit(tree)
        fixed={n:min(old_states[n])for n in live if n in old_states and n!=tree}
        assignments={}
        for item in recipe['fixed_assignment']:
            n=s.subtree(tree,item['path'])
            require(n not in assignments and n not in fixed and not s.leaf(n),'Unique new internal node assignment')
            assignments[n]=item['q']
        require(set(assignments)==live-set(fixed),'Complete assignment of new internal nodes')
        require(len(assignments)==22 and len(set(assignments.values()))==22,'22 distinct new decoder nodes and states')
        require(len(fixed)==157 and len(set(fixed.values()))==143,'Inherited157 subtree roles in143 physical states')
        pool=set(groups)-set(fixed.values())-{0}
        require(set(assignments.values())<=pool and len(pool)==23,'Assignments use23-state retired/root pool')
        require(pool-set(assignments.values())=={185},'Only unused pool state is185')
        decoded,_=b.decoder_map(table,tree)
        for q,nn in decoded.items():
            for n in nn:
                allowed=old_states[n]if n in fixed else{assignments[n]}
                require(q in allowed,'Decoder binding agrees with inherited or fixed assignment')
        # Both old marker folds retain their literal provider rows.
        fold_keys=[(69,0),(69,1),(213,0),(213,1),(92,0),(90,0),
                   (164,0),(164,1),(201,0),(201,1),(195,0),(196,0)]
        require(all(table[k]==base[k]for k in fold_keys),'Both inherited marker fold/provider rows are unchanged')
        mapping={q:i for i,q in enumerate(sorted(states))}
        mapping[254]=215
        canonical={(mapping[q],bit):(w,d,mapping[z])for(q,bit),(w,d,z)in table.items()}
        canonical_raw=b.table_bytes(canonical)
        inv={v:k for k,v in mapping.items()}
        require({(inv[q],bit):(w,d,inv[z])for(q,bit),(w,d,z)in canonical.items()}==table,'Canonical table is exactly bijective renaming')
        retained_file=HERE/('k215.native.tm'if name=='210'else'secondary120/k215-120.native.tm')
        retained_source=HERE/('sites215.json'if name=='210'else'secondary120/sites120.json')
        retained_canonical=HERE/('k215.tm'if name=='210'else'secondary120/k215-120.tm')
        require(native==retained_file.read_bytes()and source==retained_source.read_bytes()and canonical_raw==retained_canonical.read_bytes(),'All delivered exact bytes reproduced')
        out=args.output if name=='210'else args.output/'secondary120'
        out.mkdir(parents=True,exist_ok=True)
        (out/'k215.native.tm').write_bytes(native)
        (out/'sites215.json').write_bytes(source)
        (out/'k215.tm').write_bytes(canonical_raw)
        dump(out/'canonicalization.json',dict(native_to_canonical=mapping,native_sha256=sha(native),canonical_sha256=sha(canonical_raw),working_states=215,halt=215))
        reports.append(dict(permutation=name,status='EXACT_SOURCE_TABLE_AND_PREFIX_RECONSTRUCTION_PASS',working_states=215,rows=430,
            native_sha256=sha(native),canonical_sha256=sha(canonical_raw),source_sha256=sha(source),source_metrics=s.metrics(tree),
            full_guarded_CFG_equal_to_calibrated_public_permutation=True,guarded_cases=sum(2 if op=='CD'else 1 for p,op,a in rows),
            selector_partition=selectors,command_fields=fields,command_return_routes=returns,new_decoder_nodes=22,retired_root_pool=23,
            retained_subtree_roles=157,retained_decoder_states=143,deleted_states=[185],changed_retained_rows=36,protected_rows=recipe['protected_rows'],
            both_inherited_marker_fold_rows_preserved=True,
            scope='Deterministic source, exact table and complete internal-prefix correspondence. Full quantified primitive runtime and blank initialization are separate freshly replayed certificates.'))
    result=dict(status='PASS_DETERMINISTIC_K215_COMPOSITION',predecessor_archives=pins['archives'],machines=reports)
    dump(args.output/'construction.json',result)
    print('PASS: primary K215 exact source,430-row table, canonicalization and internal-prefix correspondence rebuilt.')
    print(args.output/'construction.json')

if __name__=='__main__':
    main()
