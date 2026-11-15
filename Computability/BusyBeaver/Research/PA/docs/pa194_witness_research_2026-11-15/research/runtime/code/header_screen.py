#!/usr/bin/env python3
"""Focused shorter-header feasibility audit; no state-minimality claim.

Read candidate literal/source certificates. Check whether any working control
is absent from all source contracts; replay the complete accepted startup;
transfer the known 301/88 Runtime193 patch and classify all blank starts.
The optional symbolic sweep checks the same literal contracts at a smaller
header, without introducing a startup or assuming a box oracle.
"""
from pathlib import Path
import argparse, collections, hashlib, json, sys, time

def table(path):
    result={}
    for line in path.read_text().splitlines():
        q,b,w,d,t=line.split()
        result[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(t))
    return result

def transfer(rows):
    out={key:(w,d,88 if t==301 else t) for key,(w,d,t) in rows.items() if key[0]!=301}
    out[88,0]=(0,-1,51)
    out[51,0]=(0,1,122)
    assert rows[16,1]==out[122,1]==(0,-1,1)
    return out

def canonical_frames(ones, head, sites, header_minimum):
    if {x for x in ones if x<head}!={head-1}:return []
    maxone=max(ones,default=head-2)
    found=[]
    for index in range(25,45):
        path=sites[index][0]
        if any((head+i in ones)!=(c=='1') for i,c in enumerate(path)):continue
        marker=next((x for x in range(head+len(path),maxone+1) if x in ones),None)
        if marker is None or marker-head<header_minimum:continue
        position=marker+1;values=[]
        while position<=maxone:
            if position in ones or position+1 not in ones:break
            position+=1;start=position
            while position in ones:position+=1
            values.append(position-start-1)
        else:
            if len(values)>=10 and all(values[i]==0 for i in (0,2,7)):
                found.append(dict(site=index,head=head,header=marker-head,physical_values=values))
    return found

def all_starts(rows,sites,header_minimum,limit):
    states=sorted({q for q,b in rows});records=[]
    for start in states:
        q=start;head=0;ones=set();trace=[];boundary_count=0;frames=[];maxspan=0;boundary_ones=0
        for step in range(limit+1):
            maxspan=max(maxspan,max(ones)-min(ones)+1 if ones else 0)
            if q==254:status='HALT';break
            if q==84:
                boundary_count+=1
                boundary_ones=max(boundary_ones,len(ones))
                frames.extend(canonical_frames(ones,head,sites,header_minimum))
                if frames:status='FRAME';break
            w,d,t=rows[q,int(head in ones)]
            if t==q and head not in ones and (not ones or d<0 and head<min(ones) or d>0 and head>max(ones)):
                status='RAY';break
            if step==limit:status='OPEN';break
            trace.append((q,head,int(head in ones),w,d,t))
            (ones.add if w else ones.discard)(head);head+=d;q=t
        records.append(dict(start=start,status=status,steps=step,q=q,head=head,ones=sorted(ones),boundary_visits=boundary_count,maximum_boundary_ones=boundary_ones,maximum_preterminal_support_span=maxspan,frames=frames,trace=trace))
    return records

def main():
    p=argparse.ArgumentParser();p.add_argument('candidate',type=Path);p.add_argument('--checker',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--literal-header',type=int);p.add_argument('--usage-witness',type=Path);p.add_argument('--limit',type=int,default=100000)
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions must be enabled.')
    rows=table(a.candidate/'machine.native.tm');sites=json.loads((a.candidate/'sites.json').read_text())
    sites=[[''.join(map(str,p)) if not isinstance(p,str) else p,op,arg] for p,op,arg in sites]
    minimum=max(len(p) for p,op,arg in sites)
    mapping={int(k):v for k,v in json.loads((a.checker/'legacy_mapping.json').read_text()).items()}
    for q in {q for q,b in rows}|{254}:mapping.setdefault(q,q+10000)
    inverse={v:k for k,v in mapping.items()}
    usage=None
    if a.usage_witness:
        sys.path.insert(0,str(a.checker));import symbolic_runtime as s
        witness=json.loads(a.usage_witness.read_text());s.HEADER_BASE=witness['header'];s.r.PHY=(6,2,0,4,3,7,8,5,1)
        names={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
        tab={(mapping[q],b):(w,d,mapping[t]) for (q,b),(w,d,t) in rows.items()}
        lemmas,_=s.prove_blocks(tab);used=set();steps=0
        for c in witness['cases']:
            path,op,arg=sites[c['site']];r=s.case(tab,lemmas,(path,names[op],arg),c['positive']);steps+=r['symbolic_steps']
            actual={inverse[q] for q,b in r['rows']};assert actual==set(c['native_controls']);used.update(actual)
        usage=dict(witness_sha256=hashlib.sha256(a.usage_witness.read_bytes()).hexdigest(),cases=len(witness['cases']),symbolic_steps=steps,header=witness['header'],status='PASS')
    else:
        certs=json.loads((a.candidate/'independent/contracts.json').read_text())
        used={inverse[q] for c in certs for q,b in c['rows']}
        for block in json.loads((a.candidate/'independent/list_lemmas.json').read_text()):
            used.update(inverse[event[1][0]] for event in block['trace'] if event[0]!='list')
    state_set={q for q,b in rows}
    result=dict(candidate=a.candidate.name,native_sha256=hashlib.sha256((a.candidate/'machine.native.tm').read_bytes()).hexdigest(),working_controls=len(state_set),maximum_source_depth=minimum,controls_seen_in_universal_source_certificates=len(used),controls_absent_from_all_source_certificates=sorted(state_set-used))
    if usage:result['source_control_usage_replay']=usage
    sys.path.insert(0,str(a.checker));import independent_runtime as ir
    instructions=json.loads((a.candidate/'instructions.json').read_text())
    closure_header=a.literal_header if a.literal_header is not None else minimum+2
    closure_count=maximum_computed_depth=0
    for index,(path,op,arg) in enumerate(sites):
        ins=instructions[index]
        for positive in ([False,True] if op=='dec' else [False]):
            if op=='halt':continue
            if op=='inc' or op=='dec' and positive:
                computed,overflow=ir.inc(path);target=ins[2] if op=='inc' else ins[3]
            elif op in ('dec','breakTo'):
                computed,overflow=ir.inc(ir.strip(path,'0',1 if op=='dec' else arg));target=ins[2] if op=='dec' else ins[1]
            else:
                assert op=='continueTo';computed=ir.strip(path,'1',arg);overflow=0;target=ins[1]
            actual=sites[target][0]
            assert not overflow and max(len(computed),len(actual))<=closure_header
            assert computed+'0'*(closure_header-len(computed))==actual+'0'*(closure_header-len(actual))
            closure_count+=1;maximum_computed_depth=max(maximum_computed_depth,len(computed))
    result['header_source_closure']=dict(header=closure_header,live_outcomes=closure_count,maximum_computed_depth=maximum_computed_depth,all_actual_successors_match_after_padding=True,all_overflows_zero=True)
    q=74;head=0;ones=set()
    for step in range(57922):
        assert q!=254
        w,d,q=rows[q,int(head in ones)];(ones.add if w else ones.discard)(head);head+=d
    assert (q,head)==(84,-2)
    expected={head-1,head+48}
    expected.update(head+i for i,b in enumerate(sites[25][0]) if b=='1')
    physical=[0]*9;physical[6]=2;position=head+49
    for value in physical+[1]*26:
        position+=1;expected.update(range(position,position+value+1));position+=value+1
    assert ones==expected
    result['accepted_startup']=dict(steps=57922,state=q,head=head,whole_tape_matches=True,frames=canonical_frames(ones,head,sites,minimum))
    core=transfer(rows);records=all_starts(core,sites,minimum,a.limit)
    assert len(core)==386
    result['Runtime193']=dict(patch=['redirect every target301 to88; remove301','88/0 = 0L51','51/0 = 0R122'],working_controls=193,blank_starts=len(records),counts=dict(collections.Counter(x['status'] for x in records)),maximum_trace_steps=max(x['steps'] for x in records),boundary_visits=sum(x['boundary_visits'] for x in records),maximum_boundary_ones=max(x['maximum_boundary_ones'] for x in records),maximum_preterminal_support_span=max(x['maximum_preterminal_support_span'] for x in records),canonical_frame_minimum_ones=12,header_minimum=minimum,frame_scope='Complete canonical tape at sites 25..44, header at least maximum source depth, at least 10 unary blocks, physical proof slots0,2,7 zero. Independently, every canonical frame at any source site and header has at least 12 ones; the boundary count therefore excludes even those broader frames.',trace_limit=a.limit)
    (a.output/'runtime193_blank_traces.json').write_text(json.dumps(records,separators=(',',':'))+'\n')
    (a.output/'runtime193.native.tm').write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {t}\n' for (q,b),(w,d,t) in sorted(core.items())))
    if a.literal_header is not None:
        sys.path.insert(0,str(a.checker));import symbolic_runtime as s
        s.HEADER_BASE=a.literal_header
        s.r.PHY=(6,2,0,4,3,7,8,5,1)
        names={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
        outcomes=[]
        for tag,tr in [('accepted194',rows),('Runtime193',core)]:
            tab={(mapping[q],b):(w,d,mapping[t]) for (q,b),(w,d,t) in tr.items()}
            elapsed=time.monotonic();lemmas,blocks=s.prove_blocks(tab);seen=set();count=0;steps=0
            try:
                for i in sorted(range(len(sites)),key=lambda i:-len(sites[i][0])):
                    path,op,arg=sites[i]
                    for positive in ([False,True] if op=='dec' else [False]):
                        c=s.case(tab,lemmas,(path,names[op],arg),positive)
                        count+=1;steps+=c['symbolic_steps'];seen.update(inverse[q] for q,b in c['rows'])
                    if count%1000==0:print(tag,'checked',count,flush=True)
                outcome=dict(table=tag,header=a.literal_header,status='PASS',outcomes=count,symbolic_steps=steps,source_controls=len(seen),seconds=time.monotonic()-elapsed)
            except Exception as e:
                outcome=dict(table=tag,header=a.literal_header,status='NOT_CERTIFIED',outcomes_before_failure=count,symbolic_steps=steps,site=i,path=path,operation=op,positive=positive,error=repr(e),seconds=time.monotonic()-elapsed)
            outcomes.append(outcome);print(json.dumps(outcome),flush=True)
        result['smaller_header_symbolic_checks']=outcomes
    result['scope']='Focused feasibility screen only. Header is a tape-layout parameter, not an unrolled control count. Exhaustive classification applies only to these 193 fixed rows with each blank start; no arbitrary bootstrap rewrite is excluded.'
    (a.output/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
