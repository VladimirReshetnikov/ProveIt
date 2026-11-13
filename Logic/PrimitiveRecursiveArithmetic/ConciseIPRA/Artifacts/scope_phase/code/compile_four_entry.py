"""Untrusted canonical fixture compiler for the entry-reserved four-field checker."""
from compile_direct_three import scan_old, MISSING

def translate(document):
    tree=scan_old(document)
    records=[]
    floor=0
    first=True
    stats={'nodes':0,'early_terminals':0}
    def rename(a,env):
        if type(a) is list:return [rename(b,env) for b in a]
        return env[a] if a<0 else a
    def build(node,g,goal,env):
        nonlocal floor,first
        stats['nodes']+=1
        assert goal==rename(node.goal,env)
        m,s,u,t=node.packet
        s,u,t,m=record=rename([s,u,t,m],env)
        if m==0:record[3]=m=[]
        records.append(record)
        def op(a,t=MISSING,d=0,validate=False):
            if type(a) is list and (not validate or len(a) in (1,2+d%2)):
                return [op(b,t,d+5-len(a),validate) for b in a]
            if floor<=a<d and (not validate or d&(a%2)):
                return a or 1
            return (d%2)*op(t,d=3,validate=validate)
        checked=op(goal,validate=first)
        first=False
        floor-=1
        frame=[[s and [s] or 1,u,t],op(t,record[:3],3) if s else u]
        if checked in (floor,*g,frame):
            if not node.terminal:stats['early_terminals']+=1
            return
        if node.terminal:raise ValueError(('lost terminal',node.terminal,goal,frame))
        a=goal
        h=m*3 or (a:=op(*a,t,2))
        if m:
            build(node.major,g,m,env)
        else:
            records.append([0,1,1,[]])
            stats['nodes']+=1
            floor-=1
        eigen=floor
        hypothesis=op(h,eigen if m or len(a)==2==u else 0)
        endpoint=(m,a)==([s,u] if s else [t]*3,op(t,u))
        assert endpoint==node.match
        nextgoal=op(op(t,s) if endpoint else a,[eigen])
        build(node.continuation,g+[hypothesis],nextgoal,{**env,node.floor-1:eigen})
    build(tree,[[]],tree.goal,{})
    return list(reversed(records))+[tree.goal],stats

if __name__=='__main__':
    import json,sys
    from pathlib import Path
    src,dst=sys.argv[1:]
    out,stats=translate(json.loads(Path(src).read_text()))
    Path(dst).write_text(json.dumps(out,separators=(',',':'))+'\n')
    print(json.dumps(stats))
