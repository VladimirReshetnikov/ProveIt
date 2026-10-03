"""Independent finite checks. Writes only next to this audit script; not a general exporter."""
import sys, json, random, itertools, hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT))
import scheduler_reference as s
import example_emitter as e

def require(ok,detail):
    if not ok: raise RuntimeError(detail)

def gate_schema(g,x):
    """Fixed 2n raw slots, complete competitor scans, rank-matched simultaneous output."""
    x=tuple(sorted(x)); records=[]
    for label,shape in enumerate(g.shapes):
        for first in x:
            u=first-shape[0]
            raw=all(any(z==u+p for z in x) for p in shape) and sum(u-g.B<=z<=u+g.B for z in x)==len(shape)
            records.append((label,u,raw))
    raw_keys=[u for label,u,raw in records if raw]
    require(len(raw_keys)==len(set(raw_keys)),('duplicate raw key',g.name,x))
    active=[]; rejected_competitor=0; multi_context=0
    for label,u,raw in records:
        isolated=sum(u-g.L<=z<=u+g.L for z in x)==len(g.shapes[label])
        competitor=any(other_raw and v!=u and abs(v-u)<=g.M for other_label,v,other_raw in records)
        guard=True
        if g.guard is not None:
            classes=[]
            for side in (-1,1):
                hits=[side*(z-u)-g.guard.Z for z in x if 0<=side*(z-u)-g.guard.Z<=g.guard.J]
                if len(hits)>1:guard=False;multi_context+=int(raw)
                classes.append(hits[0] if len(hits)==1 else (g.guard.J+1 if not hits else 0))
            guard=guard and g.guard.table[classes[0]][classes[1]]
        if raw and isolated and competitor:rejected_competitor+=1
        if raw and isolated and not competitor and guard:active.append((label,u))
    out=[]
    for z in x:
        terms=[new-old for label,u in active for old,new in zip(g.shapes[label],g.shapes[1-label]) if z==u+old]
        require(len(terms)<=1,('overlap',g.name,x,active,z))
        out.append(z+sum(terms))
    require(len(out)==len(set(out)),('mass collision',g.name,x,active))
    return frozenset(out),dict(raw=len(raw_keys),active=len(active),competitors=rejected_competitor,multi_context=multi_context)

def source(controls,branches,J=0):
    return dict(schema='reversible-two-counter-v1',controls=controls,start=controls[0],halt=controls[-1],class_cut=J,branches=branches)
def branch(name,src,dst,side,delta,guard=None):
    return dict(name=name,source=src,target=dst,side=side,delta=delta,guard=guard or dict(op='true'))
def atom(op,c,k):return dict(op=op,counter=c,value=k)
SOURCES=[
 ('no_branches',source(['h'],[])),
 ('direct_only',source(['q','h'],[branch('d','q','h',1,0)])),
 ('left_decrement',source(['q','h'],[branch('l','q','h',-1,-1,atom('gt',0,0))])),
 ('right_guarded_increment',source(['q','h'],[branch('r','q','h',1,1,atom('eq',1,0))],1)),
 ('mixed_original_order',source(['q','d','h'],[branch('direct_first','q','h',1,0,atom('eq',0,0)),branch('moving_second','q','d',-1,-1,atom('gt',0,0))],2)),
 ('large_context',source(['q','h'],[branch('r','q','h',1,1,atom('eq',1,15))],17)),
 ('multiple_incidence',source(['q','a','b','c','h'],[
    branch('direct0','q','a',1,0,atom('eq',0,0)),branch('moving1','q','b',-1,-1,atom('eq',0,1)),
    branch('direct2','q','c',1,0,atom('eq',0,2)),branch('moving3','q','h',1,1,atom('eq',0,3))],4))]

def main():
    rng=random.Random(9281003)
    stats=dict(sources=0,cases=0,factor_schema_matches=0,candidate_completeness_cases=0,scheduler_checks=0,underbudget_checks=0,
               multi_active_factors=0,competitor_rejections=0,multi_context_rejections=0,primitive_divisions=0,polynomial_cases=0)
    source_stats=[]
    for name,src in SOURCES:
        a=s.lazy.compile_lazy_source(src); gates=[a.gate_at(i) for i in range(a.factors)]
        cases={frozenset(),frozenset({-10**100})}
        for n in range(5):cases.update(frozenset(v) for v in itertools.combinations(range(-2,4),n))
        selected=list(range(a.factors)) if a.factors<5 else sorted(set([0,a.factors-1]+[rng.randrange(a.factors) for _ in range(26)]))
        for gi in selected:
            g=gates[gi]
            for label in (0,1):
                shift=rng.choice([-10**70,-21,0,53,10**80]);base={shift+p for p in g.shapes[label]};cases.add(frozenset(base))
                sep=4*(a.Z+a.J+g.M+a.B3)+10
                cases.add(frozenset(base|{p+sep for p in base}))
                if g.guard is not None:
                    for c0,c1 in [(0,0),(a.J+1,a.J+1),(a.J,0),(0,a.J)]:
                        ctx=set(base)
                        if c0<=a.J:ctx.add(shift-a.Z-c0)
                        if c1<=a.J:ctx.add(shift+a.Z+c1)
                        cases.add(frozenset(ctx))
                    cases.add(frozenset(base|{shift-a.Z,shift-a.Z-min(1,a.J),shift+a.Z,shift+a.Z+min(1,a.J)}))
        # Nearby disjoint free pairs may fail only the all-raw competitor rule.
        for g in gates:
            if len(g.shapes[0])==2:
                base=set(g.shapes[0]);sep=g.L+max(g.shapes[0])+2
                if sep<=g.M:cases.add(frozenset(base|{p+sep for p in base}))
                break
        # Check literal product counts, independently unfolded schema output, and candidate soundness.
        events=0
        for ci,x in enumerate(sorted(cases,key=lambda z:(len(z),tuple(sorted(z))))):
            enabled={i for yes,i in s.slots(a,x) if yes}
            require(enabled==set(a.candidate_indices(x)),('candidate set',name,x))
            for i,g in enumerate(gates):
                y,gs=gate_schema(g,x)
                expected=g.apply(set(x),verify=True)
                require(y==expected,('factor schema mismatch',name,i,x,y,expected))
                if gs['raw']:require(i in enabled,('omitted raw factor',name,i,x))
                stats['factor_schema_matches']+=1;stats['multi_active_factors']+=gs['active']>1
                stats['competitor_rejections']+=gs['competitors'];stats['multi_context_rejections']+=gs['multi_context']
            stats['candidate_completeness_cases']+=1
            if ci%5==0 or len(x)<=1:
                T=ci%3;y=x;k=0
                for _ in range(T):
                    for g in gates:
                        z=g.apply(set(y));k+=z!=y;y=z
                for K in (k,k+2):
                    ok,z,rec=s.run(a,x,T,K)
                    require(ok and z==y,('scheduler',name,x,T,K,y,z))
                    require(sum(r['kind']=='change' for r in rec)==k,('event count',name))
                    require(sum(r['kind']=='complete' for r in rec)==T,('completion count',name))
                    require(all(r['kind']=='idle' and r['cursor']==0 for r in rec[T+k:]),('idle',name))
                    stats['scheduler_checks']+=1
                if k:
                    ok,z,rec=s.run(a,x,T,k-1);require(not ok,('underbudget',name,x,T,k));stats['underbudget_checks']+=1
                events+=k
            stats['cases']+=1
        source_stats.append(dict(name=name,m=a.m,p=a.p,a=a.a,J=a.J,F=a.factors,cases=len(cases),events=events))
        stats['sources']+=1
    # Exhaust the canonical signed constant-division equations, not just intended assignments.
    for d in range(1,9):
        for v in range(-24,25):
            sols=[]
            for qp in range(26):
                for qm in range(26):
                    if qp*qm:continue
                    r=v-d*(qp-qm);h=d-1-r
                    if r>=0 and h>=0:sols.append((qp,qm,r,h))
            q,r=divmod(v,d);expected=(max(q,0),max(-q,0),r,d-1-r)
            require(sols==[expected],('division fiber',v,d,sols));stats['primitive_divisions']+=1
    # The emitter's circuit syntax must not vary with sampled coordinate values.
    for T,K in [(0,0),(0,3),(1,0),(1,2),(2,4),(3,7)]:
        base=None
        for h,gap in [(-10**100,1),(-23,5),(0,6),(10**100,7),(-7,8),(19,29)]:
            c,rec,out=e.build(h,gap,T,K)
            syntax=[e.dump_poly(p) for p in c.rows]
            if base is None:base=syntax
            else:require(syntax==base,('input-dependent circuit syntax',T,K,h,gap))
            A,I,D,G,Q=[c.counts[x] for x in ['A','I','D','G','Q']];led=c.ledger()
            require(led['witnesses']==2*A+2*I+4*D+G,'V ledger')
            require(led['residuals']==2*A+2*I+3*D+G+Q,'E ledger')
            require(led['residual_monomials']<=9*A+10*I+9*D+4*G+4*Q,'term ledger')
            require(led['ordered_sos_term_bound']<=65*A+68*I+35*D+16*G+16*Q,'square ledger')
            require(led['max_residual_degree']<=2,'degree')
            # At least one row constrains each auxiliary and no later-index dependency is needed.
            touched=set(i for p in c.rows for mon in p for i in mon)
            require(set(range(c.input_count,len(c.values)))<=touched,'unconstrained auxiliary')
            stats['polynomial_cases']+=1
    # Multi-coordinate canonical-sign adversary, independently of +1-single-coordinate tests.
    c,rec,out=e.build(-10,5,1,2)
    z=list(c.values);checked=0
    for i,name in enumerate(c.names):
        if i>=c.input_count and '+:' in name and i+1<len(z) and '-:' in c.names[i+1]:
            trial=list(z);trial[i]+=3;trial[i+1]+=3
            require(c.score(trial)>0,('noncanonical natural sign pair accepted',i));checked+=1
    stats['paired_sign_mutations']=checked
    result=dict(status='passed',stats=stats,sources=source_stats,
        caveat='Finite independent schema checks and primitive fiber checks, not a general coefficient exporter or a proof of universal uniqueness.')
    out=Path(__file__).with_name('independent-receipt.json');out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
