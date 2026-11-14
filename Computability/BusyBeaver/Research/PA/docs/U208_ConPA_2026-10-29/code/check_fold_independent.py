#!/usr/bin/env python3
"""Independent literal audit of the 211-to-172 deletion.

No builder, source parser, symbolic-runtime engine, or saved verdict is used.
The two predecessor invariants are inferred by enumerating all bounded
incoming histories and solving their bit constraints, including the initial
state boundary. This is finite executable mathematical evidence.
"""
import argparse, collections, hashlib, json
from pathlib import Path

def need(ok, msg):
    if not ok:
        raise ValueError(msg)

def read(path):
    table={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q,b,w,d,r=line.split();q,b,w,r=map(int,(q,b,w,r))
        need((q,b)not in table,'duplicate row')
        need(b in(0,1)and w in(0,1)and d in('L','R'),'malformed transition')
        table[q,b]=(w,1 if d=='R'else-1,r)
    states={q for q,b in table}
    need(set(table)=={(q,b)for q in states for b in(0,1)},'partial table')
    need(254 not in states and 0 in states,'initial/halting convention')
    need(all(r in states or r==254 for w,d,r in table.values()),'unknown target')
    return table,states

def histories(table,end,depth):
    incoming=collections.defaultdict(list)
    for(q,b),(w,d,r)in table.items():
        incoming[r].append((q,b,w,d,r))
    def go(q,n):
        if not n:
            yield []
        else:
            for edge in incoming[q]:
                for prefix in go(edge[0],n-1):
                    yield prefix+[edge]
    return list(go(end,depth))

def solve_history(edges,current_constraints):
    # A cell expression is a bit constant or its initial independent symbol.
    h=-sum(e[3]for e in edges);tape={};constraints={}
    def expr(x):
        return tape.get(x,('initial',x))
    def constrain(e,b):
        if isinstance(e,int):
            return e==b
        if e in constraints:
            return constraints[e]==b
        constraints[e]=b
        return True
    for q,b,w,d,r in edges:
        if not constrain(expr(h),b):return None
        tape[h]=w;h+=d
    need(h==0,'history normalization')
    for x,b in current_constraints.items():
        if not constrain(expr(x),b):return None
    def value(x):
        e=expr(x)
        return e if isinstance(e,int)else constraints.get(e,'UNCONSTRAINED')
    return value

def infer(table,end,depth,current,required):
    # Every visit from start either has a full history or is in this finite
    # startup boundary. We rule out the latter using a graph overapproximation.
    reachable={0}
    for n in range(depth):
        need(end not in reachable,f'possible early entry before history: {end}/{n}')
        reachable={table[q,b][2]for q in reachable if q!=254 for b in(0,1)}
    paths=histories(table,end,depth);valid=[];inconsistent=0
    for edges in paths:
        values=solve_history(edges,current)
        if values is None:
            inconsistent+=1;continue
        facts={str(x):values(x)for x in required}
        need(all(values(x)==b for x,b in required.items()),'predecessor invariant not implied')
        valid.append({'history':edges,'deduced':facts})
    need(valid,'vacuous invariant audit')
    return {'state':end,'depth':depth,'current_constraints':current,'required_final_bits':required,
      'total_histories':len(paths),'inconsistent_histories':inconsistent,'consistent_histories':valid,
      'initial_boundary_ruled_out':True}

def run(table,q,cells,steps):
    tape=dict(cells);head=0;trace=[]
    for i in range(steps):
        need(head in tape,'read of arbitrary exterior')
        need(q!=254,'interior halt')
        b=tape[head];w,d,r=table[q,b]
        trace.append([q,head,b,w,d,r]);tape[head]=w;head+=d;q=r
    return (q,head,tape),trace

def main():
    p=argparse.ArgumentParser();p.add_argument('parent',type=Path);p.add_argument('child',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    old,ss=read(a.parent);new,tt=read(a.child)
    need(tt==ss-{211},'wrong deleted-state set')
    rho=lambda q:172 if q==211 else q
    changed=[]
    for(q,b),(w,d,r)in old.items():
        if q==211:continue
        if new[q,b]!=(w,d,rho(r)):changed.append((q,b))
    need(changed==[(172,0)],'unexpected nonquotient changes')
    need(new[172,0][:2]==(0,-1),'new selector write/move')
    p211=infer(old,211,3,{0:0},{-1:1})
    p172=infer(old,172,2,{}, {-2:1,-1:0})
    local=[]
    for q,b,cells,n in [(211,0,{-1:1,0:0},3),(211,1,{0:1},1),
                        (172,0,{-2:1,-1:0,0:0},7),(172,1,{0:1},1)]:
        left,ltrace=run(old,q,cells,1);right,rtrace=run(new,rho(q),cells,n)
        need(right==(rho(left[0]),left[1],left[2]),'local block mismatch')
        need(right[2]==cells,'modified local tape')
        local.append({'old_state':q,'read':b,'known_cells':cells,'old_trace':ltrace,'child_trace':rtrace,'old_steps':1,'child_steps':n,'endpoint_state':right[0],'endpoint_head':right[1]})
    reached={0};todo=[0]
    for q in todo:
        for bit in(0,1):
            r=new[q,bit][2]
            if r!=254 and r not in reached:reached.add(r);todo.append(r)
    need(reached==tt,'unreachable counted states')
    result={'status':'INDEPENDENT_HISTORY_AND_BLOCK_AUDIT_PASS','parent_states':len(ss),'child_states':len(tt),
      'parent_sha256':hashlib.sha256(a.parent.read_bytes()).hexdigest(),'child_sha256':hashlib.sha256(a.child.read_bytes()).hexdigest(),
      'inferred_invariants':[p211,p172],'quotient':{'211':172},'exceptional_row':{'state':172,'read':0,'action':new[172,0]},
      'ordinary_exact_quotient_rows':len(old)-4,'local_cases':local,'maximum_local_cells':3,
      'step_relation':'Tchild = Tparent + 2*N(parent211/read0) + 6*N(parent172/read0)',
      'scope':'Every common initial tape in state0; positive block simulation. No source-reassociation claim; no consistency assumption or proof-assistant endpoint.'}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k not in('inferred_invariants','local_cases')},indent=2))
if __name__=='__main__':main()
