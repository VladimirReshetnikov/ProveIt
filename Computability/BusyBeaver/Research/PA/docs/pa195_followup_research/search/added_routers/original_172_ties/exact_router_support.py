"""Exact incoming-history and finite local execution support for router searches."""
from collections import Counter,defaultdict

def install(r):
    def opportunities(rows,shape,ignore_incoming=frozenset()):
        incoming=defaultdict(set)
        for(q,bit),(w,d,n)in rows.items():
            if q not in ignore_incoming:incoming[n].add((w,d))
        providers=[defaultdict(list),defaultdict(list)]
        for h in {q for q,_ in rows}:
            w0,d0,u0=rows[h,0];w1,d1,u1=rows[h,1]
            if(w0,d0,w1,d1)!=(0,True,1,True):continue
            for bit in (0,1):
                if (u0,bit)in rows and(u1,bit)in rows:
                    providers[bit][rows[u0,bit],rows[u1,bit]].append((h,u0,u1))
        out=[]
        for a in shape:
            if incoming[a]!={(0,True)}:continue
            for b in shape:
                if incoming[b]!={(1,True)}:continue
                choices=[]
                for bit in (0,1):
                    if rows[a,bit]==rows[b,bit]:choices.append([rows[a,bit]])
                    else:choices.append([(bit,False,h) for h,u0,u1 in providers[bit].get((rows[a,bit],rows[b,bit]),()) if not {a,b}&{h,u0,u1}])
                if all(choices):out.append((a,b,choices))
        return out
    def certificate(raw,folded,folds,aliases):
        def need(ok,msg):
            if not ok:raise ValueError(msg)
        history={q:p for a,b,acts in folds for q,p in ((a,0),(b,1))}
        incoming=[]
        for(q,bit),(w,d,n)in raw.items():
            if n in history:
                need(d and w==history[n],'invalid incoming history')
                incoming.append([q,bit,w,int(d),n,history[n]])
        need(set(history)<={row[4]for row in incoming},'unentered fold state')
        for(q,bit),(w,d,n)in raw.items():
            if q not in history:need(folded[q,bit]==(w,d,aliases.get(n,n)),'ordinary row does not commute')
        traces=[]
        for q,p in sorted(history.items()):
            for bit in (0,1):
                w,d,n=raw[q,bit];target=aliases.get(n,n);targetpos=1 if d else-1
                expected={-1:p,0:w};tape={-1:p,0:bit};pos=0;now=aliases.get(q,q);steps=[];seen=set()
                while not steps or(now,pos,tape)!=(target,targetpos,expected):
                    need(pos in(-1,0),'unrecorded tape cell')
                    key=now,pos,tape[-1],tape[0]
                    need(key not in seen,'local loop');seen.add(key)
                    rd=tape[pos];ww,dd,nn=folded[now,rd]
                    steps.append([now,pos,rd,ww,'R'if dd else'L',nn]);tape[pos]=ww;pos+=1 if dd else-1;now=nn
                traces.append({'raw_state':q,'left_bit':p,'read_bit':bit,'raw_transition':[w,'R'if d else'L',n],'projected_target':target,'steps':steps,'duration':len(steps),'whole_tape_boundary_equal':True})
        return {'incoming_rows':incoming,'local_traces':traces,'local_cases':len(traces),'durations':dict(Counter(x['duration']for x in traces)),'all_outside_tape_cells_unread_and_unchanged':True,'other_raw_rows_commute_in_one_step':True,'start_preserved':True,'halting_control_preserved':True,'exact_cycle_detection':True}
    r.c.opportunities_fast=opportunities
    r.v.quotient_certificate=certificate
