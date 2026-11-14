#!/usr/bin/env python3
"""Independent exact source/local audit of the U210 -> U209 composition.

Uses explicit exceptions throughout, and remains effective under python -O.
Imports only the independent U210 audit's parsing/CFG/prefix utilities, not
any discovery builder or symbolic runtime. Whole-runtime and logical
calibration remain separate obligations.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from check_u210 import (require,read_table,census,inspect_source,prefix_bindings,
                       closed_factor,rejects)

OLD_FACTOR_PREFIXES=('00','010','0110','01110','011110','011111','10','11')
NEW_FACTOR_PREFIXES=('00','010','0110','0111','10','1100','1101','111')
REASSOCIATION_EDITS={(204,1):(1,1,146),(217,0):(0,1,220),(217,1):(1,1,214),
                     (214,0):(0,1,216),(214,1):(1,1,163),
                     (216,0):(0,1,90),(216,1):(1,1,211)}
RIGHT_ROTATIONS=((206,199),(205,206),(7,205))

def substitute_factors(rows,roots,old_prefixes,new_prefixes):
    answer=[]
    for path,op,arg in rows:
        result=path
        for root in roots:
            if path.startswith(root):
                local=path[len(root):]
                matches=[(a,b) for a,b in zip(old_prefixes,new_prefixes) if local.startswith(a)]
                require(len(matches)==1,'factor partition does not cover leaf uniquely')
                a,b=matches[0];result=root+b+local[len(a):];break
        answer.append([result,op,arg])
    return answer

def run_local(table,state,cells,steps):
    tape=dict(cells);head=0;trace=[]
    for _ in range(steps):
        require(state!=254,'internal halt')
        require(head in tape,'local path reads opaque exterior')
        bit=tape[head];w,d,target=table[state,bit]
        trace.append([state,head,bit,w,d,target]);tape[head]=w
        head+=d;state=target
    return (state,head,tape),trace

def exact_identity(old,new,old_state,new_state,cells,n,m,target,label):
    a,pa=run_local(old,old_state,cells,n);b,pb=run_local(new,new_state,cells,m)
    require(a==b and a==(target[0],target[1],cells),label+' endpoint/whole-tape mismatch')
    return {'label':label,'cells':cells,'old_steps':n,'new_steps':m,
            'old_path':pa,'new_path':pb,'endpoint':list(target),'whole_frame_unchanged':True}

def engine_repair(old,new):
    return [exact_identity(old,new,171,171,{-1:b,0:0},2+b,2+b,
                           (86,0) if b==0 else (164,1),'arithmetic_reentry_'+str(b))
            for b in (0,1)]

def fold_guards(old,new):
    require(sorted(k for k,v in old.items() if v[2]==216)==[(214,0)],'zero-tag inventory')
    require(old[214,0]==(0,1,216),'zero-tag row')
    require(sorted(k for k,v in old.items() if v[2]==180)==[(132,1),(199,1)],'one-tag inventory')
    require(all(old[k]==(1,1,180) for k in [(132,1),(199,1)]),'one-tag rows')
    require(old[216,0]==(0,1,90) and old[180,0]==(0,1,152),'distinct zero branches')
    require(old[216,1]==old[180,1]==(1,1,211),'common one branch')
    expected={(q,b):(w,d,216 if t==180 else t) for (q,b),(w,d,t) in old.items() if q!=180}
    expected[216,0]=(0,-1,211)
    require(new==expected,'complete fold quotient differs')
    return {'zero_tag':[[214,0]],'one_tag':[[132,1],[199,1]]}

def fold_paths(old,new):
    result=[]
    for state,tag,target,zero_steps in [(216,0,90,5),(180,1,152,3)]:
        for bit in (0,1):
            result.append(exact_identity(old,new,state,216,{-1:tag,0:bit},1,
                            1 if bit else zero_steps,(211 if bit else target,1),
                            f'fold_{state}_{bit}'))
    return result

def preserved_research_selector(table):
    """Check the original two logical decoder roles at the shared state220."""
    require(sorted(k for k,v in table.items() if v[2]==220)==[(185,1),(217,0)],
            'Research selector complete incoming inventory')
    require(table[185,1]==(1,1,220) and table[217,0]==(0,1,220),'Research selector tags')
    result=[]
    for tag,zero_target in [(0,157),(1,147)]:
        for bit in (0,1):
            cells={-1:tag,0:bit};steps=1 if bit else 3
            endpoint,trace=run_local(table,220,cells,steps)
            target=176 if bit else zero_target
            require(endpoint==(target,1,cells),'preserved Research helper endpoint')
            result.append({'tag':tag,'current':bit,'steps':steps,'endpoint':[target,1],
                           'path':trace,'whole_frame_unchanged':True})
    return result

def audit(parent_table,parent_source,prefold_path,candidate_path,source_path,dense_path=None):
    old=read_table(parent_table);census(old,210,254);table=old.copy()
    original=json.loads(Path(parent_source).read_text());rows=original
    info=inspect_source(rows);graph=info['graph'];word=[r[1:] for r in rows]
    binding,_=prefix_bindings(table,info['prefixes'])
    roots=sorted(p for p,q in binding.items() if q==174)
    require(len(roots)==1,'outer174 source occurrence census')
    counts=[[closed_factor(rows,p+s) for s in OLD_FACTOR_PREFIXES] for p in roots]
    require(counts==[[26,134,52,108,136,27,103,134]],'eight closed factor sizes')
    for k in REASSOCIATION_EDITS:
        require(table[k][:2]==(k[1],1),'reassociation changes nonpure row')
    table.update(REASSOCIATION_EDITS)
    rows=substitute_factors(rows,roots,OLD_FACTOR_PREFIXES,NEW_FACTOR_PREFIXES)
    after=inspect_source(rows);require(after['graph']==graph,'bulk reassociation CFG')
    require([r[1:] for r in rows]==word,'bulk reassociation primitive order')
    bound,steps=prefix_bindings(table,after['prefixes'])
    stages=[{'type':'eight_closed_factor_reassociation','outer':174,'paths':roots,
             'factor_sizes':counts,'old_factor_prefixes':OLD_FACTOR_PREFIXES,
             'new_factor_prefixes':NEW_FACTOR_PREFIXES,'metrics':after['metrics'],
             'internal_prefixes':len(bound),'maximum_prefix_steps':steps,
             'both_cfg_resolvers':True}]
    rotation_roots={p:sorted(path for path,state in bound.items() if state==p)
                    for p,q in RIGHT_ROTATIONS}
    def bind_one(word):
        return prefix_bindings(table,{word})[0][word]
    for p,q in RIGHT_ROTATIONS:
        info=inspect_source(rows)
        # The three outer paths are nested ancestors, and thus unaffected by
        # earlier rotations strictly below them. Check their literal bindings
        # directly; intermediate seven-zero layouts are not runtime claims.
        roots=rotation_roots[p]
        require(all(bind_one(path)==p for path in roots),'outer literal prefix binding')
        require(roots and all(not x.startswith(y) for x in roots for y in roots if x!=y),
                'right rotation outer occurrences')
        require(all(table[r,b][:2]==(b,1) for r in (p,q) for b in (0,1)),'pure right decoders')
        require(table[p,1][2]==q,'right rotation inner edge')
        require({k for k,v in table.items() if v[2]==q}=={(p,1)},'inner has another entry')
        sizes=[]
        for root in roots:
            require(bind_one(root+'1')==q,'inner prefix binding')
            sizes.append([closed_factor(rows,root+s) for s in ('0','10','11')])
        a,b,c=table[p,0][2],table[q,0][2],table[q,1][2]
        table.update({(p,0):(0,1,q),(p,1):(1,1,c),(q,0):(0,1,a),(q,1):(1,1,b)})
        rows=substitute_factors(rows,roots,('0','10','11'),('00','01','1'))
        after=inspect_source(rows);require(after['graph']==graph,'right rotation CFG')
        require([r[1:] for r in rows]==word,'right rotation primitive order')
        try:
            intermediate,steps=prefix_bindings(table,after['prefixes'])
            prefix_status={'status':'PASS','internal_prefixes':len(intermediate),
                           'maximum_prefix_steps':steps}
        except ValueError as error:
            prefix_status={'status':'NOT_A_RUNTIME_INTERMEDIATE',
                           'diagnostic':str(error)}
        stages.append({'type':'right_rotation','outer':p,'inner':q,'paths':roots,
                       'closed_factor_sizes':sizes,'metrics':after['metrics'],
                       'intermediate_prefix_check':prefix_status,
                       'both_cfg_resolvers':True})
    require(table[171,0]==(0,-1,7),'engine row before repair')
    table[171,0]=(0,-1,205)
    require(table==read_table(prefold_path),'complete prefold210 table')
    require(rows==json.loads(Path(source_path).read_text()),'complete transformed source')
    candidate=read_table(candidate_path);states=census(candidate,209,254)
    guards=fold_guards(table,candidate);fold=fold_paths(table,candidate)
    repair=engine_repair(old,table);selector=preserved_research_selector(candidate)
    # Existing 218-to157 detour implementation survives without row changes.
    for key in ((157,0),(157,1),(67,0),(148,0),(151,0),(186,1)):
        require(candidate[key]==old[key],'previous218 detour row changed')
    final=inspect_source(rows);require(final['graph']==graph,'final source CFG')
    require(final['metrics']['maximum_zero_run']<=6,'final zero-run exclusion')
    binding,steps=prefix_bindings(candidate,final['prefixes'])
    if dense_path is not None:
        dense=read_table(dense_path);census(dense,209,209)
        renaming={q:i for i,q in enumerate(states)};renaming[254]=209
        require(dense=={(renaming[q],b):(w,d,renaming[t]) for (q,b),(w,d,t) in candidate.items()},
                'dense table isomorphism')
    controls=[]
    for key,value,label in [((216,0),(0,1,211),'wrong selector direction'),
                            ((216,0),(1,-1,211),'wrong selector write'),
                            ((216,0),(0,-1,157),'wrong selector target'),
                            ((211,0),(0,1,184),'wrong zero-tag helper'),
                            ((211,1),(1,1,157),'wrong one-tag helper'),
                            ((184,0),(0,1,90),'wrong tag-one endpoint'),
                            ((151,0),(0,1,165),'wrong tag-zero endpoint')]:
        broken=dict(candidate);broken[key]=value
        controls.append(rejects(lambda t=broken:fold_paths(table,t),label))
    broken=dict(table);broken[171,0]=(0,-1,7)
    controls.append(rejects(lambda:engine_repair(old,broken),'missing171 entry repair'))
    broken=dict(table);broken[199,0]=(0,1,180)
    controls.append(rejects(lambda:fold_guards(broken,candidate),'extra wrong-tag180 entrance'))
    for key,value,label in [((204,0),(0,1,148),'damage liveResearch helper zero row'),
                            ((129,1),(1,1,214),'damage Research predecessor selector')]:
        broken=dict(candidate);broken[key]=value
        controls.append(rejects(lambda t=broken:preserved_research_selector(t),label))
    return {'status':'INDEPENDENT_U209_FINITE_SOURCE_PASS','working_states':209,
            'transition_rows':418,'source_primitives':len(rows),'source_edges':sum(len(x[2]) for x in graph),
            'source_cases':final['resolved'],'metrics':final['metrics'],'stages':stages,
            'fold_guards':guards,'fold_paths':fold,'arithmetic_entry_paths':repair,
            'preserved_research_selector_paths':selector,
            'final_internal_prefixes':len(binding),'final_maximum_prefix_steps':steps,
            'negative_controls_rejected':controls,
            'changed_retained_rows_from_u210':[{'state':q,'read':b,'before':old[q,b],'after':v}
                                             for (q,b),v in sorted(candidate.items()) if old[q,b]!=v],
            'changed_source_addresses_from_u210':sum(a[0]!=b[0] for a,b in zip(original,rows)),
            'scope':'Exact source/literal/local and arithmetic-entry checks only; '
                    'whole-runtime, startup and inherited consistency calibration are separate.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for arg in ('parent_table','parent_source','prefold','candidate','source'):parser.add_argument(arg,type=Path)
    parser.add_argument('--dense',type=Path);parser.add_argument('--output',type=Path);a=parser.parse_args()
    result=audit(a.parent_table,a.parent_source,a.prefold,a.candidate,a.source,a.dense)
    result['input_sha256']={name:hashlib.sha256(getattr(a,name).read_bytes()).hexdigest()
                           for name in ('parent_table','parent_source','prefold','candidate','source')}
    if a.dense:result['input_sha256']['dense']=hashlib.sha256(a.dense.read_bytes()).hexdigest()
    payload=json.dumps(result,indent=2)+'\n'
    if a.output:a.output.write_text(payload)
    print(json.dumps({k:v for k,v in result.items() if k not in ('stages','fold_paths','arithmetic_entry_paths',
          'preserved_research_selector_paths','changed_retained_rows_from_u210')},indent=2))

if __name__=='__main__':main()
