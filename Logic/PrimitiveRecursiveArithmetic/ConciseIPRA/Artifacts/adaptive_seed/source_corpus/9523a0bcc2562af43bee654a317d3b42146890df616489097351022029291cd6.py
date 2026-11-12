"""Untrusted producer for successor-seeded scalar iteration.

The arithmetic kernel accepts direct successor computation only when the
predecessor is an array. Every other instance is compiled through a boxed
counter. The measured checker imports neither this module nor its producer
helper. The scalar compiler deliberately has no counter variable in updates.
Ordinary zero is raw 0. Only the auxiliary box uses raw [] as its predecessor;
this avoids a mismatch with the kernel's DI base opening at scalar zero.
"""
import json
from pathlib import Path
import produce_counter as p

class ScalarEmitter(p.Emitter):
    def __init__(self,focused=True):
        super().__init__(focused)
        self.boxed_steps=0
    def n(self,a,env=(),hole=None):
        if a[0]=='zl':return []
        if a[0]=='r':
            _,n,b,u,v,h=a
            # A scalar update has one state, duplicated by the raw encoding.
            return [self.n(n,(None,None)+env,hole),self.n(b,(None,None)+env,hole),self.n(h,(v,v)+env,hole)]
        return super().n(a,env,hole)
    def go(self,node,g=()):
        if node['kind']=='comp':
            goal=node['goal']
            if goal[0]=='e' and goal[1][0]=='r':
                _,counter,a,u,v,h=goal[1]
                if counter[0]=='s':
                    n=counter[1]
                    if not isinstance(self.n(n),list):
                        # B_n=R(S0,0;w.n)=n. The predecessor of this box is
                        # literally raw [], hence its own computation is legal.
                        box_axiom=p.succ_ax(n=('zl',),h=n)
                        box=box_axiom['goal'][1]
                        major=box_axiom
                        minor=p.succ_ax(box,a,h,u,v)
                        x=p.fresh('counter')
                        body=p.E(p.R(p.S(p.V(x)),a,u,v,h),p.sub(h,v,p.R(p.V(x),a,u,v,h)))
                        expanded=p.tr(major,minor,x,body)
                        assert expanded['goal']==goal
                        self.boxed_steps+=1
                        return self.go(expanded,g)
        return super().go(node,g)

def fixtures():
    fs=p.fixtures()
    del fs['R_successor_counter']
    fs['R_successor_constant_zero']=p.succ_ax(p.S(p.Z),p.S(p.Z),p.Z)
    # A genuinely used y-dependent base tests DI's scalar-zero opening
    # against the QE source opening. All ordinary zeros remain scalar 0.
    progress=fs['DI_progress_uses_hypothesis']
    goal=progress['goal'];_,x,y,body=goal
    z,a=p.fresh(),p.fresh()
    base=p.sub(body,y,p.Z)
    clause=p.Q(y,body)
    specialized=p.qe(clause,p.S(p.V(z)),p.hyp(base))
    fs['DI_case_uses_y_dependent_base']=p.di(goal,p.S(p.Z),0,z,p.de(progress,a,specialized))
    a=p.fresh()
    fs['QE_y_dependent_zero_source']=p.de(progress,a,p.qe(clause,p.S(p.Z),p.comp(base)))
    return fs

def write(directory):
    directory=Path(directory);directory.mkdir(parents=True,exist_ok=True)
    report=[]
    for focused in (True,False):
        cases=[]
        for name,node in fixtures().items():
            emitter=ScalarEmitter(focused)
            packet=emitter.run(node)
            cases.append(dict(name=name,accept=True,packet=packet,counts=emitter.counts,allocations=-emitter.k,administrative=emitter.admin,boxed_steps=emitter.boxed_steps))
        filename='scalar_focused.json' if focused else 'scalar_unfocused.json'
        (directory/filename).write_text(json.dumps(dict(cases=cases),indent=2)+'\n')
        report.append(dict(file=filename,cases=len(cases)))
    return report

if __name__=='__main__':
    import sys
    print(json.dumps(write(sys.argv[1] if len(sys.argv)>1 else Path(__file__).resolve().parent.parent/'fixtures'),indent=2))
