#!/usr/bin/env python3
"""Exact countdown-loop summaries as variable-length source frontiers.

The source-loop compiler retains a complete affine matrix on all nine initial
registers. It never treats a clear as a freely available reset. A target is
offered to the offset-only binary oracle only when its exact matrix reduces
to identity plus constants under singleton entry constraints. Every summary
has an explicit decreasing source counter, finite control cycle, exact exit,
and positive (possibly variable) source clock. No binary loop is assumed.
"""
from __future__ import annotations
import argparse
from collections import Counter,defaultdict
from functools import lru_cache
import hashlib,json,sys,time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'compiler_experiments'))
import reference_block_folds as base
c,phase,effects=base.c,base.phase,base.effects
ZERO=(0,)*10

def add(a,b,multiplier=1):return tuple(x+multiplier*y for x,y in zip(a,b))
def constant(k):return (0,)*9+(k,)
def limits(expr,bounds):
    low=expr[9];high=expr[9]
    for coefficient,(lo,hi) in zip(expr[:9],bounds):
        assert coefficient>=0
        low+=coefficient*lo
        if coefficient and hi is None:high=None
        elif high is not None:high+=coefficient*(hi or 0)
    return low,high

def offset_form(registers,bounds):
    """Exact equality to initial variables plus constants, on entry premises."""
    offsets=[]
    for r,expr in enumerate(registers):
        coefficients=list(expr[:9]);value=expr[9]
        for s,(lo,hi) in enumerate(bounds):
            if hi is not None and lo==hi:
                value+=coefficients[s]*lo;coefficients[s]=0
        lo,hi=bounds[r]
        if hi is not None and lo==hi:
            if any(coefficients):return None
            offsets.append(value-lo)
        else:
            if coefficients!=[int(s==r) for s in range(9)]:return None
            offsets.append(value)
    return tuple(offsets)

def dbm_projector():
    """Exact equalities from a checked source DBM, with entry guards imposed.

The DBM variables are0 and the nine LOGICAL source registers; affine rows use
the nine PHYSICAL initial registers. Only finite exact equalities are used.
The binary oracle retains its original coarser independent entry bounds.
"""
    path=ROOT/'proof_audit/relational_dbm_threshold2.json'
    raw=path.read_bytes();data=json.loads(raw)
    assert data['program_sha256']==phase.PROG_SHA
    assert data['source_commit']=='43026ff42f0939f09b9e95495248cfadcad38e38'
    assert data['status']=='PASS exact source-transfer postfix certificate'
    inf=data['infinity_sentinel']
    @lru_cache(None)
    def zone(site,bounds):
        class_id=data['site_class_ids'][site]
        assert class_id is not None
        values=data['invariant_classes'][class_id]
        d=[list(values[10*i:10*i+10]) for i in range(10)]
        # Coarse bounds already include the selected original CD guard.
        for logical,physical in enumerate(c.PHYS):
            v=logical+1;lo,hi=bounds[physical]
            d[0][v]=min(d[0][v],-lo)
            if hi is not None:d[v][0]=min(d[v][0],hi)
        for k in range(10):
            for i in range(10):
                if d[i][k]==inf:continue
                for j in range(10):
                    if d[k][j]!=inf:d[i][j]=min(d[i][j],d[i][k]+d[k][j])
        if any(d[i][i]<0 for i in range(10)):return None
        roots=[];potentials=[]
        for v in range(10):
            root=min(w for w in range(10) if d[v][w]!=inf and d[w][v]!=inf and d[v][w]+d[w][v]==0)
            roots.append(root);potentials.append(d[v][root])
        return tuple(roots),tuple(potentials)
    def convert(registers,bounds,site):
        description=zone(site,bounds)
        if description is None:return None
        roots,potentials=description;result=[]
        for target,expr in enumerate(registers):
            grouped=Counter();value=expr[9]
            for logical,physical in enumerate(c.PHYS):
                coefficient=expr[physical]-int(physical==target)
                variable=logical+1
                grouped[roots[variable]]+=coefficient
                value+=coefficient*potentials[variable]
            # Representative0 is the distinguished constant0. All other
            # representative variables remain free; their sums must cancel.
            if any(coefficient for root,coefficient in grouped.items() if root!=0):return None
            result.append(value)
        return tuple(result)
    return convert,zone,{'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(raw).hexdigest(),
                         'scope':dbm_projector.__doc__,'guard_closure':'Floyd-Warshall after imposing all coarse bounds including selected source guard',
                         'binary_oracle_bounds':'original coarse per-register bounds retained'}

def control_data():
    raw=(ROOT/'upstream/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==phase.PROG_SHA
    sites,cases,targets,first=phase.program_graph(raw)
    by_site=defaultdict(list)
    for index,case in enumerate(cases):by_site[case[0]].append(index)
    @lru_cache(None)
    def decode(pc):
        q,path=0,''
        while True:
            bit=pc[len(path)] if len(path)<len(pc) else '0';path+=bit
            op,*args=c.NODES[q][int(bit)].split()
            if op=='CN':q=int(args[0]);continue
            assert '1' not in pc[len(path):]
            return path,op,int(args[0]) if args else None
    path_index={p:i for i,(p,op,r) in enumerate(sites)}
    loops={};gap_rejected=[]
    for site,(path,op,r) in enumerate(sites):
        if op!='CD':continue
        zero,positive=by_site[site];cur=targets[positive]
        counts=[0]*9;body=[];gap_growth=int(c.inc(path) is None)
        while cur!=site and cur not in body:
            body.append(cur);pp,oo,rr=sites[cur]
            if oo=='CI':counts[rr]+=1;nxt=c.inc(pp)
            elif oo=='CB':nxt=c.inc(c.strip(pp,'0',rr))
            elif oo=='CC':nxt=c.strip(pp,'1',rr)
            else:break
            gap_growth+=nxt is None
            cur=targets[by_site[cur][0]]
        else:
            if cur!=site or counts[r]!=0:continue
            if gap_growth:
                gap_rejected.append(site);continue
            exit_pc=c.inc(c.strip(path,'0',1))
            loops[site]={'site':site,'path':path,'counter':r,'positive_case':positive,
                         'body_sites':body,'body_increments':counts,
                         'cycle_source_steps':len(body)+1,'exit_site':targets[zero],
                         'exit_pc':exit_pc or '', 'exit_gap_increment':int(exit_pc is None),
                         'cycle_gap_increment':0}
    return sites,cases,targets,first,decode,path_index,loops,gap_rejected

def configure(hop_limit,capture_cases=(),process_cases=None,use_dbm=False):
    original_frontiers,constraints,enabled,_=base.configure(64)
    sites,cases,targets,first,decode,path_index,loops,gap_rejected=control_data()
    frontiers=[];summary_stats=Counter();new_records=[];catalogue_use=Counter()
    capture_cases=set(capture_cases);raw_by_case={}
    if use_dbm:convert_dbm,zone,dbm_evidence=dbm_projector()
    else:convert_dbm=zone=None;dbm_evidence=None
    for index,(site,path,op,r,zero) in enumerate(cases):
        if not enabled[index]:frontiers.append(None);continue
        if process_cases is not None and index not in process_cases:
            frontiers.append(None);continue
        bounds=constraints[index]
        if use_dbm and zone(site,bounds) is None:
            enabled[index]=False;frontiers.append(None);summary_stats['infeasible_product_guard']+=1;continue
        registers=[tuple(int(s==r) for s in range(9))+(0,) for r in range(9)]
        # Retain every previously justified fixed-prefix target; the loop
        # frontiers form a union, never a replacement of that search space.
        old_frontier=original_frontiers[index]
        frames={frame:True for frame in old_frontier.frames}
        records=old_frontier.metadata.copy()
        clock=ZERO;gap=40;pc=path;seen=set();history=[]
        halt_steps=None
        if index in capture_cases:
            raw_by_case[index]={'case':index,'source_site':site,'source_case':[path,op,r,zero],
                                'physical_entry_bounds':bounds,'logical_to_physical':c.PHYS,
                                'targets':[],'source_halt_clock':None}
            for prior in old_frontier.metadata:
                rows=[tuple(int(s==r) for s in range(9))+(prior['primary_delta'][r],)
                      for r in range(9)]
                raw_by_case[index]['targets'].append({
                    'pc':prior['pc'],'gap_constant':prior['gap_constant'],
                    'register_affine_rows':rows,
                    'source_clock_expression':constant(prior['source_steps']),
                    'source_clock_lower_bound':prior['source_steps'],
                    'next_source_leaf':prior['next_source_leaf'],
                    'history':[{'fixed_source_prefix_steps':prior['source_steps']}],
                    'origin':'original_exact_fixed_prefix'})
        for hop in range(hop_limit):
            pp,kind,register=decode(pc);current_site=path_index[pp]
            if kind=='CH':
                if index in capture_cases:
                    raw_by_case[index]['source_halt_clock']={
                        'successful_source_steps_before_CH':clock,
                        'augmented_terminal_edge_steps':add(clock,constant(1))}
                clock=add(clock,constant(1));halt_steps=limits(clock,bounds)[0]
                assert halt_steps>=1
                summary_stats['halts']+=1;break
            loop=loops.get(current_site)
            if hop and kind=='CD' and loop is not None:
                physical=c.PHYS[register];count=registers[physical]
                assert limits(count,bounds)[0]>=0
                old=registers.copy();registers[physical]=ZERO
                for logical,multiplicity in enumerate(loop['body_increments']):
                    if multiplicity:
                        target=c.PHYS[logical]
                        registers[target]=add(old[target],count,multiplicity)
                clock=add(add(clock,count,loop['cycle_source_steps']),constant(1))
                gap+=loop['exit_gap_increment'];pc=loop['exit_pc'].rstrip('0')
                history.append({'loop_site':current_site,'counter_expression':count})
                catalogue_use[current_site]+=1;summary_stats['loop_summaries']+=1
                if limits(count,bounds)[1] is None:summary_stats['unbounded_loop_summaries']+=1
            else:
                positive=False
                if kind in ('CI','CD'):
                    physical=c.PHYS[register];lo,hi=limits(registers[physical],bounds)
                    assert lo>=0
                    if kind=='CI':registers[physical]=add(registers[physical],constant(1))
                    elif hi==0:positive=False
                    elif lo>=1:positive=True;registers[physical]=add(registers[physical],constant(-1))
                    else:summary_stats['unknown_non_simple_guard']+=1;break
                if kind=='CI' or kind=='CD' and positive:nxt=c.inc(pp)
                elif kind=='CD':nxt=c.inc(c.strip(pp,'0',1))
                elif kind=='CB':nxt=c.inc(c.strip(pp,'0',register))
                elif kind=='CC':nxt=c.strip(pp,'1',register)
                else:raise AssertionError(kind)
                if nxt is None:gap+=1;nxt=''
                pc=nxt.rstrip('0');clock=add(clock,constant(1))
                history.append({'instruction_site':current_site,'positive':positive if kind=='CD' else None})
            if index in capture_cases:
                raw_by_case[index]['targets'].append({
                    'pc':pc,'gap_constant':gap,'register_affine_rows':registers.copy(),
                    'source_clock_expression':clock,
                    'source_clock_lower_bound':limits(clock,bounds)[0],
                    'next_source_leaf':list(decode(pc)),'history':history.copy(),
                    'origin':'exact_prefix_with_countdown_summaries'})
            simple_delta=offset_form(registers,bounds)
            delta=convert_dbm(registers,bounds,site) if use_dbm else simple_delta
            if delta is not None and simple_delta is None:summary_stats['dbm_additional_offset_conversions']+=1
            if delta is not None and simple_delta is not None:assert delta==simple_delta
            if delta is not None:
                lower_clock=limits(clock,bounds)[0];assert lower_clock>=1
                target=c.strict.canon([('b',1)],[('b',int(b)) for b in pc]+[
                    ('r',0,1,gap-len(pc)),('b',1),('box',('plain',effects.encode(delta)))])
                record={'source_steps':lower_clock,'source_clock_expression':clock,
                        'pc':pc,'gap_constant':gap,'primary_delta':list(delta),
                        'next_source_leaf':list(decode(pc)),'history':history.copy()}
                if not hop:assert target==c.CASES[index][5]
                if target not in frames:
                    frames[target]=record;records.append(record)
                    if target not in original_frontiers[index].frames:
                        summary_stats['new_targets']+=1
                        new_records.append({'case':index,'record':record})
            else:summary_stats['non_offset_intermediate_matrices']+=1
            signature=(pc,gap,tuple(registers))
            if signature in seen:summary_stats['repeated_matrix_state']+=1;break
            seen.add(signature)
        else:summary_stats['hop_limit']+=1
        frontiers.append(base.Frontier(frames,records,halt_steps))
    same_targets=all(process_cases is not None and index not in process_cases or
                     new is None and old is None or
                     new is not None and old is not None and new.frames==old.frames
                     for index,(new,old) in enumerate(zip(frontiers,original_frontiers)))
    evidence={'scope':__doc__,'loop_count':len(loops),'gap_growth_rejected':gap_rejected,
              'loop_catalogue':loops,'summary_counts':dict(summary_stats),
              'catalogue_uses':dict(catalogue_use),'new_target_records':new_records,
              'target_sets_equal_previous_fixed_prefix_targets':same_targets,
              'processed_cases':'all' if process_cases is None else sorted(process_cases),
              'dbm_projection':dbm_evidence,
              'raw_matrix_frontiers':raw_by_case,
              'target_count_histogram':dict(Counter(len(f.frames) for f in frontiers if f is not None))}
    return frontiers,constraints,enabled,evidence

def raw_targets(case_indices,hop_limit=64):
    """Small external API: complete source matrix frontiers for selected cases.

Rows/clock use the nine PHYSICAL initial registers followed by a constant.
Every live target has at least one successful source step; the matrix and
gap are exact for every register vector within physical_entry_bounds. The
unmodified initial literal-prefix frontiers are retained in addition to
the variable-length loop frontiers. This routine runs no binary fold search.
"""
    wanted=set(case_indices)
    _,_,_,evidence=configure(hop_limit,capture_cases=wanted,process_cases=wanted)
    return {'scope':raw_targets.__doc__,'cases':evidence['raw_matrix_frontiers'],
            'summary_counts':evidence['summary_counts'],'hop_limit':hop_limit,
            'loop_catalogue_source':'control_data()[6]',
            'source_sha256':phase.PROG_SHA}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--hop-limit',type=int,default=64)
    p.add_argument('--fuel',type=int,default=1000)
    p.add_argument('--seconds',type=float,default=600)
    p.add_argument('--frontiers-only',action='store_true')
    p.add_argument('--capture-cases',type=int,nargs='*',default=[])
    p.add_argument('--dbm-projection',action='store_true')
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True);start=time.monotonic()
    frontiers,constraints,enabled,evidence=configure(a.hop_limit,capture_cases=a.capture_cases,use_dbm=a.dbm_projection)
    evidence['hop_limit']=a.hop_limit
    (a.output/'source_frontiers.json').write_text(json.dumps(evidence,indent=2)+'\n')
    print(json.dumps({k:v for k,v in evidence.items() if k not in ('scope','loop_catalogue','catalogue_uses','new_target_records','raw_matrix_frontiers')}),flush=True)
    if a.frontiers_only:return
    admitted=[i for i,yes in enumerate(enabled) if yes];usage=defaultdict(list)
    for i in admitted:
        tracked=base.Tracking(c.T)
        ok,cost,steps,reason=base.check_one(tracked,i,frontiers,constraints,a.fuel)
        assert ok,('baseline',i,reason)
        for q in {q for q,b in tracked.used}:usage[q].append((cost,i))
    for q in usage:usage[q].sort()
    states=sorted({q for q,b in c.T},key=int)
    protected_targets={c.T[k][2] for k in base.PROTECTED}
    eligible=[q for q in states if q not in protected_targets|{'96'} and all((q,b) not in base.PROTECTED for b in (0,1))]
    assert len(eligible)==221
    result={'scope':__doc__,'planned':55471,'completed':0,'checks':0,'survivors':[],
            'new_source_block_matches':[],'rejections':Counter(),'completed_all':False,
            'baseline_cases':len(admitted),'binary_rule_fuel':a.fuel,'hop_limit':a.hop_limit}
    result['dbm_projection']=a.dbm_projection
    stopped=False
    with (a.output/'journal.jsonl').open('w') as journal:
        for n,dead in enumerate(eligible):
            for replacement in states:
                if dead==replacement:continue
                if time.monotonic()-start>a.seconds:stopped=True;break
                table=c.fold(c.T,dead,replacement)
                assert all(table[k]==c.T[k] for k in base.PROTECTED)
                failure=None;long=[]
                for _,i in usage[dead]:
                    ok,cost,steps,reason=base.check_one(table,i,frontiers,constraints,a.fuel);result['checks']+=1
                    if not ok:failure=[i,reason];break
                    if steps is not None and steps>1:long.append([i,steps])
                if failure is None:
                    for i in admitted:
                        ok,cost,steps,reason=base.check_one(table,i,frontiers,constraints,a.fuel);result['checks']+=1
                        if not ok:failure=[i,reason];break
                        if steps is not None and steps>1:long.append([i,steps])
                result['completed']+=1
                record={'deleted':int(dead),'replacement':int(replacement),'failure':failure,'long_matches':long}
                journal.write(json.dumps(record)+'\n')
                if long:result['new_source_block_matches'].append(record)
                if failure is None:
                    result['survivors'].append(record);print('SURVIVOR',dead,replacement,flush=True)
                    text='#! start 64\n'+''.join(f'{q} {b} {w} {d} {t}\n' for(q,b),(w,d,t) in sorted(table.items(),key=lambda x:(int(x[0][0]),x[0][1])))
                    (a.output/f'candidate_{dead}_{replacement}.tm').write_text(text)
                else:
                    reason=failure[1];result['rejections'][reason.split("'",2)[1] if "'" in reason else reason]+=1
            if n%20==0:print('PROGRESS',n,dead,result['completed'],result['checks'],round(time.monotonic()-start,2),flush=True)
            if stopped:break
    result['completed_all']=not stopped;result['seconds']=time.monotonic()-start
    result['rejections']=dict(result['rejections'])
    result['journal_sha256']=hashlib.sha256((a.output/'journal.jsonl').read_bytes()).hexdigest()
    (a.output/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)
if __name__=='__main__':main()
