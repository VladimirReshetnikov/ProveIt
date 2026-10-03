#!/usr/bin/env python3
"""Portable finite wiring checks for the reviewed incoming 1977e6ea6 archives.

verify(all_files) takes already archive-hash-checked member dictionaries:
{ZIP_filename: {relative_member_name: bytes}}. Five executed source members
are independently pinned below. Nothing is read from a checkout or temporary
directory, and the private source-module names are restored even on failure.

This is a review/scout replay, not a hardened rewritten compiler API. It
compares the three separately authored rule evaluators and checks reductions
of actual emitted residuals, including signed off-zero corrections and the
natural-domain boundary. Its counts do not assert a universal operation bound.
"""
from contextlib import contextmanager
import hashlib
import itertools as it
import random
import sys
import types


# The order is the _checks argument order: orbit, local arithmetic, local graph,
# sorted-memory arithmetic, and independent flat-port graph implementations.
SOURCE_MEMBERS = (
    ("ng", "no_ghost_wires.zip", "no_ghost_wires/code/loop_exact.py",
     "e455337508df75d1d8fc9b25bf9ce813e48a2339ac00aaa438a0021c9d2d199f"),
    ("to", "Topology_Is_Not_Free_Interaction_Nets.zip",
     "Interaction_Net_Diophantine/code/certificates.py",
     "8dcb775f30efbf06d3fef6e2c142384afcd7bbe9dba1e80fbe7f1fe4d3702154"),
    ("nt", "Topology_Is_Not_Free_Interaction_Nets.zip",
     "Interaction_Net_Diophantine/code/nets.py",
     "e563ed729a5547dfcd78280e4365728e40345be91f64083e59f1a4ce33ef0659"),
    ("ex", "Exact_Wiring_Diophantine_Report.zip",
     "Exact_Wiring_Diophantine/code/diophantine_memory.py",
     "45a7fbb5bd1f5496c0b14a4fcdde5da5794364ba85c426b3f3753b235f361923"),
    ("ew", "Exact_Wiring_Diophantine_Report.zip",
     "Exact_Wiring_Diophantine/code/wiring.py",
     "3d9e106b202fb624bb65713cbb8d76224b11f1e533d8ce33a56df6306202e9e0"),
)
SCOPE = (
    "Independent finite semantic and literal-source reduction scout; "
    "no fixed universal operation claim"
)


@contextmanager
def _source_modules(all_files):
    if type(all_files) is not dict:
        raise ValueError("Expected archive member dictionaries.")
    checked = []
    # Verify every executed source before executing even the first source.
    for alias, archive, member, digest in SOURCE_MEMBERS:
        files = all_files.get(archive)
        if type(files) is not dict:
            raise ValueError(f"Missing member dictionary: {archive}")
        raw = files.get(member)
        if type(raw) is not bytes or hashlib.sha256(raw).hexdigest() != digest:
            raise ValueError(f"Source hash or byte-type mismatch: {archive}/{member}")
        checked.append((alias, archive, member, raw))
    missing = object()
    saved = {}
    modules = []
    try:
        for alias, archive, member, raw in checked:
            name = f"_incoming_wiring_1977e6ea6_{alias}"
            saved[name] = sys.modules.get(name, missing)
            module = types.ModuleType(name)
            module.__file__ = f"{archive}/{member}"
            sys.modules[name] = module
            exec(compile(raw, module.__file__, "exec"), module.__dict__)
            modules.append(module)
        yield modules
    finally:
        for name, previous in saved.items():
            if previous is missing:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = previous


def verify(all_files):
    """Replay all independent checks and return their original counts and scope."""
    if not __debug__:
        raise RuntimeError("Checks require assertions; do not use Python -O.")
    with _source_modules(all_files) as modules:
        counts = _checks(*modules)
    return {"status": "PASS", "scope": SCOPE, "counts": counts}


def _checks(ng, to, nt, ex, ew):
    rng=random.Random(1977)
    counts={}
    def allzero(rows,v):return all(p.evaluate(v)==0 for p in rows)
    def orbit_rows(s):
        rows=dict(s.residuals); out=[]; n=0
        for name,p in s.residuals:
            if '.bit[' in name:n+=1;continue
            if '.minimum[' in name:
                reset=rows[name.replace('.minimum[','.reset[')]
                q=p+reset
                assert q.degree()==1
                assert (p-q+reset).terms=={}
                out.append(q)
            else:out.append(p)
        assert len(out)==len(s.residuals)-n
        return out,n
    # Three separately authored all-rule interpreters; fixed one-step allocations made explicit.
    ct=0; formal_rows=0; source_forms=0; false_endpoints=0
    for ta,tb in it.product('EDG',repeat=2):
        for f in (0,2,4):
            cells={0:ta,1:tb};free=tuple(sorted((-j-1,0) for j in range(f)))
            points=[p for p in ng.ports(cells,free) if p not in ((0,0),(1,0))]
            for edges in ew.matchings(points):
                wires=tuple(sorted((((0,0),(1,0)),)+edges)); n=ng.Net(cells,wires,3,free); n.validate()
                result,_,_=ng.step(n,(0,1))
                ntin=nt.Net({c:t.lower() for c,t in cells.items()},n.partner(),3,2)
                ntout=nt.rewrite_components(ntin,0,1)
                assert {c:t.upper() for c,t in ntout.cells.items()}==result.cells
                assert ntout.mate==result.partner() and ntout.loops==result.loops
                layout=ew.Layout(2,1,f); fmap={p:layout.free_ports[j] for j,p in enumerate(free)}
                def enc(p):return fmap[p] if p[0]<0 else ew.port(*p)
                eti={'E':'epsilon','D':'delta','G':'gamma'}
                ei=ew.Net({c:eti[t] for c,t in cells.items()},{enc(a):enc(b) for a,b in n.partner().items()},3,layout.free_ports)
                eo=ew.rewrite(ei,0,1,0,layout)
                mixed={ta,tb}=={'D','G'}
                def dest(p):
                    c,j=p
                    if mixed and c>=2:c={2:4,3:5,4:2,5:3}[c]
                    return enc((c,j))
                assert eo.mate=={dest(a):dest(b) for a,b in result.partner().items()}
                expected_cells={({2:4,3:5,4:2,5:3}[c] if mixed and c>=2 else c):eti[t] for c,t in result.cells.items()}
                assert eo.cells==expected_cells and eo.loops==result.loops
                ct+=1
                # Compile each literal context's fixed schedule and transform its ACTUAL rows.
                compiled=ng.compile_schedule(cells,free,((0,1),));v=compiled.witness(n,result)
                out,k=orbit_rows(compiled.system);formal_rows+=k;source_forms+=1
                assert allzero(out,v) and len(out)==len(compiled.system.residuals)-sum(map(len,compiled.temporary_vertices))
                bad=v.copy();bad['out.loops']+=1;assert not allzero(out,bad);false_endpoints+=1
    counts['all_three_rule_comparisons']=ct
    counts['literal_no_ghost_source_forms']=source_forms
    counts['orbit_removed_rows_and_linear_identities']=formal_rows
    counts['wrong_loop_endpoints_rejected']=false_endpoints
    # Full two-step receipt's actual source; exact off-zero correction, not polynomial equality.
    a,b=ng.obstruction_examples();c=ng.compile_schedule(a.cells,(),((0,1),(2,3)));v=c.witness(a,ng.Net({},(),2));new,n=orbit_rows(c.system)
    assert (len(c.system.residuals),len(new),len(c.system.variables),len(c.system.parameters),n)==(169,147,126,68,22)
    rows=dict(c.system.residuals)
    for trial in range(40):
        q={x:rng.randrange(-3,4) for x in v}
        oldsum=sum(p.evaluate(q)**2 for p in rows.values()); newsum=sum(p.evaluate(q)**2 for p in new);correction=0
        for name,p in rows.items():
            if '.bit[' in name:correction+=p.evaluate(q)**2
            if '.minimum[' in name:
                reset=rows[name.replace('.minimum[','.reset[')].evaluate(q); linear=p.evaluate(q)+reset
                correction+=reset*reset-2*linear*reset
        assert oldsum-newsum==correction
    counts['signed_full_orbit_SOS_corrections']=40
    # Local N theorem and explicit full fixed-point signed exception.
    local=0
    for e,d,h,s in it.product(range(7),repeat=4):
        # minimum determines r for fixed i=5
        r=5-(1-e)*(h+1);old=[e*(e-1),r+(1-e)*(h+1)-5,e*h,d-(1-e)*(s+1)]
        reduced=[r+h+1-e-5,e*h,d-(1-e)*(s+1)]
        if r>=0: assert all(x==0 for x in old)==all(x==0 for x in reduced);local+=1
    counts['natural_orbit_local_equivalences']=local
    # n=1 fixed-point, d=s=-2,e=-1,h=0,r=-1; zero reduced orbit certificate over Z.
    signed={'r':-1,'d':-2,'e':-1,'h':0,'s':-2}
    assert signed['r']+signed['h']+1-signed['e']-1==0
    assert signed['d']-(1-signed['e'])*(signed['s']+1)==0
    assert signed['e']*signed['h']==0 and signed['e']*(signed['e']-1)==2
    counts['signed_fixed_point_exception']=signed
    # Local topology source transfer: delete bits and eliminate only two J h fields.
    localforms=[];cases=0;corrections=0
    for J in to.PERFECT:
        s=to.loop_system(J); out=[]
        edges=to.EDGES;removed_h={'h'+to.ename(*e) for e in J}
        for idx,p in enumerate(s.residuals):
            if idx<6:continue
            if 10<=idx<22:
                edge=edges[(idx-10)//2]
                if edge in J:
                    if idx%2==1:continue
                    i,j=edge;p=to.Poly.var('g'+to.ename(i,j))-to.Poly.var(f'e{i}')*to.Poly.var(f'e{j}')
            out.append(p)
        assert len(out)==15 and all(p.degree()<=2 for p in out)
        for vals in it.product(range(3),repeat=6):
            ext=[1-sum(v for e,v in zip(edges,vals) if i in e) for i in range(4)]
            if min(ext)<0:continue
            assert all(v in (0,1) for v in vals)
            M={e for e,v in zip(edges,vals) if v};v=to.loop_witness(M,J)
            assert s.accepts(v) and allzero(out,v)
            for h in removed_h:assert v[h]==v['g'+h[1:]]
            for x in s.aux:
                if x in removed_h:continue
                bad=v.copy();bad[x]+=1;assert not allzero(out,bad)
            cases+=1
        for _ in range(20):
            v={x:rng.randrange(-2,3) for x in s.sources+s.aux}
            for h in removed_h:v[h]=v['g'+h[1:]]
            assert sum(p.evaluate(v)**2 for p in s.residuals)-sum(p.evaluate(v)**2 for p in out)==sum(p.evaluate(v)**2 for p in s.residuals[:6]);corrections+=1
        localforms.append({'gluing':sorted(J),'old_rows':23,'new_rows':15,'old_aux':17,'new_aux':15,'source':6,'degree':4})
    counts['local_topology_natural_source_assignments_checked']=3*3**6
    counts['local_topology_valid_zero_maps']=cases
    counts['local_topology_signed_SOS_corrections']=corrections
    counts['local_topology_forms']=localforms
    # Actual exact memory compiler rows plus range-dependent same-address proof.
    mcases=0;mrows=0;example=None
    for A in (1,2,3):
        for m in (0,1,2,5):
            for V in (2,4,8):
                initial=[rng.randrange(V) for _ in range(A)];cur=initial[:];events=[]
                for _ in range(m):
                    address=rng.randrange(A);value=rng.randrange(V);events.append((address,cur[address],value));cur[address]=value
                c,meta=ex.build_memory(initial,events,cur,V);out=[];P=ex.Poly
                labels=dict(zip(c.labels,c.residuals));index=dict(zip(c.names,range(len(c.names))))
                for name,p in zip(c.labels,c.residuals):
                    if name.startswith('same_boolean.'):continue
                    if name.startswith('address_relation.'):
                        j=name.split('.')[-1]; reset=labels['unused_gap_zero.'+j];linear=p-reset
                        assert linear.degree==1 and (p-linear-reset).terms=={}
                        p=linear;mrows+=1
                    out.append(p)
                assert allzero(out,c.values) and len(out)==len(c.residuals)-(meta['records']-1)
                for _ in range(2):
                    v=[rng.randrange(-3,4) for _ in c.values];corr=0
                    for name,p in labels.items():
                        if name.startswith('same_boolean.'):corr+=p.evaluate(v)**2
                        if name.startswith('address_relation.'):
                            reset=labels['unused_gap_zero.'+name.split('.')[-1]].evaluate(v);linear=p.evaluate(v)-reset
                            corr+=reset**2+2*linear*reset
                    assert sum(p.evaluate(v)**2 for p in c.residuals)-sum(p.evaluate(v)**2 for p in out)==corr
                mcases+=1
                if (A,m,V)==(3,5,8):example={'rows_before':len(c.residuals),'rows_after':len(out),'witnesses':c.roles.count('witness'),'parameters':c.roles.count('parameter')}
    counts['exact_memory_source_forms']=mcases;counts['exact_memory_linear_identities']=mrows;counts['exact_memory_example']=example
    # Adjacent-key proof exhaustively, including bit values >=2 and zero time windows.
    checks=0
    for H in range(2,6):
        for a,an in it.product(range(4),repeat=2):
            for t,tn in it.product(range(H),repeat=2):
                if H*a+t>=H*an+tn:continue
                assert an>=a
                for z,d in it.product(range(5),repeat=2):
                    old=(an-a-(1-z)*(d+1),z*d,z*(z-1));new=(an-a-d-1+z,z*d)
                    assert all(v==0 for v in old)==all(v==0 for v in new);checks+=1
    counts['natural_sorted_memory_equivalences']=checks
    # Guard boundary limitations: recorded, not confused with exact-domain theorem bugs.
    c,_=ex.build_memory([0],[],[0],2)
    assert c.failures(c.values+[0])==[]
    assert not to.loop_system().accepts({})
    # Natural arithmetic APIs reject floats, booleans, negative coordinates.
    guards=0
    for bad in (False,0.0,-1):
        c,_=ex.build_memory([0],[],[0],2);q=c.values[:];q[0]=bad;assert c.failures(q);guards+=1
        s=to.loop_system();q=to.loop_witness(set());q[s.aux[0]]=bad;assert not s.accepts(q);guards+=1
        c=ng.compile_schedule({0:'E',1:'E'},(),((0,1),))
        n=ng.Net({0:'E',1:'E'},(((0,0),(1,0)),));q=c.witness(n,ng.Net({},()));q[c.system.variables[0] if c.system.variables else c.system.parameters[0]]=bad
        try:c.system.failed(q)
        except ValueError:guards+=1
        else:raise AssertionError('bad scalar accepted')
    counts['scalar_guard_rejections']=guards
    counts['boundary_notes']=['Exact Wiring Circuit.failures accepts unused trailing natural coordinates; no exact-assignment-shape guard. Internal compiled finite polynomial and all declared coordinates remain correct.']
    return counts
