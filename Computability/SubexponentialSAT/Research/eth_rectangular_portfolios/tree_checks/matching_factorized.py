"""Exact factorized matching-potential kernel, authored in iteration 3.

No archive module is imported. The mathematical state factors the per-matching
conditional product as s_j*x_{j,a}*B_{j,a,b}; all left vertices precede all right
vertices. Missing B entries are exactly one. Arithmetic operation count is
O(MQ+VQ), excluding matching coloring and charged powering/bit costs.
"""
from fractions import Fraction as F

ONE=F(1)

def prepare(edges,Q,eta):
    if type(Q) is not int or Q<1 or type(eta) is not int or eta<1:
        raise ValueError('Q and eta must be positive integers')
    groups=[];left=[];right=[]
    for edge in edges:
        u,v=edge
        for j in range(len(groups)):
            if u not in left[j] and v not in right[j]:
                groups[j].append(edge);left[j].add(u);right[j].add(v);break
        else:
            groups.append([edge]);left.append({u});right.append({v})
    tau=(8*len(groups)*Q*Q-1).bit_length() if groups else 0
    h=[((eta+1)*len(g)+eta*Q*Q-1)//(eta*Q*Q)+2*eta*tau for g in groups]
    incident={}
    for j,g in enumerate(groups):
        for u,v in g:
            incident.setdefault(('L',u),[]).append((j,('R',v)))
            incident.setdefault(('R',v),[]).append((j,('L',u)))
    return groups,tau,h,incident

def solve(edges,Q=2,eta=4,method='factorized',all_candidates=False):
    """Choose sparse, factorized, dense, or literal product oracle, with exact ties."""
    edges=list(edges);groups,tau,h,incident=prepare(edges,Q,eta)
    if method=='sparse':return _sparse_prepared(edges,Q,eta,groups,tau,h,incident,all_candidates)
    t=1+F(1,eta);c=1+F(1,eta*Q);d=1+F(1,eta*Q*Q)
    scales=[t**(-hj)*d**len(g) for g,hj in zip(groups,h)]
    current=sum((Q*Q*s for s in scales),F(0));initial=current
    assignment={};trace=[];candidates=[]
    if method=='factorized':
        xs=[[ONE]*Q for _ in groups]
        rows=[[F(Q)]*Q for _ in groups]
        total=[F(Q*Q) for _ in groups]
        cells=[{} for _ in groups]
    elif method=='dense':
        tables=[[[s]*Q for _ in range(Q)] for s in scales]
        dense_rows=[[Q*s]*Q for s in scales]
    elif method!='oracle':raise ValueError(method)
    for vertex in sorted(incident):
        isleft=vertex[0]=='L'
        if method=='oracle':
            values=[]
            for candidate in range(Q):
                assignment[vertex]=candidate
                potential=F(0)
                for j,g in enumerate(groups):
                    for a in range(Q):
                        for b in range(Q):
                            z=t**(-h[j])
                            for u,v in g:
                                lu=assignment.get(('L',u));rv=assignment.get(('R',v))
                                pa=F(1,Q) if lu is None else F(lu==a)
                                pb=F(1,Q) if rv is None else F(rv==b)
                                z*=1+pa*pb/eta
                            potential+=z
                values.append(potential)
            del assignment[vertex]
        else:
            base=current;scores=[F(0)]*Q
            for j,other in incident[vertex]:
                if method=='factorized':
                    if isleft:
                        old= scales[j];new=old/d
                        base+=(new-old)*total[j];scales[j]=new
                        z=new*(c-1)
                        for a in range(Q):scores[a]+=z*xs[j][a]*rows[j][a]
                    else:
                        a=assignment[other];oldx=xs[j][a];newx=oldx/c
                        delta=(newx-oldx)*rows[j][a]
                        base+=scales[j]*delta;total[j]+=delta;xs[j][a]=newx
                        z=scales[j]*newx*(t-1)
                        for b in range(Q):scores[b]+=z*cells[j].get((a,b),ONE)
                else:
                    tab=tables[j]
                    if isleft:
                        for a in range(Q):
                            old=dense_rows[j][a]
                            tab[a]=[v/d for v in tab[a]]
                            new=old/d;dense_rows[j][a]=new
                            base+=new-old;scores[a]+=(c-1)*new
                    else:
                        a=assignment[other]
                        old=dense_rows[j][a];tab[a]=[v/c for v in tab[a]]
                        new=old/c;dense_rows[j][a]=new;base+=new-old
                        for b in range(Q):scores[b]+=(t-1)*tab[a][b]
            values=[base+score for score in scores]
        if sum(values,F(0))!=Q*current:raise ArithmeticError('averaging identity')
        chosen=min(range(Q),key=lambda a:(values[a],a))
        if values[chosen]>current:raise ArithmeticError('monotonicity')
        if method!='oracle':
            for j,other in incident[vertex]:
                if method=='factorized':
                    if isleft:
                        delta=(c-1)*xs[j][chosen]
                        total[j]+=delta*rows[j][chosen];xs[j][chosen]*=c
                    else:
                        a=assignment[other];v=cells[j].get((a,chosen),ONE)
                        delta=(t-1)*v
                        rows[j][a]+=delta;total[j]+=xs[j][a]*delta
                        cells[j][a,chosen]=t*v
                else:
                    if isleft:
                        tables[j][chosen]=[c*v for v in tables[j][chosen]]
                        dense_rows[j][chosen]*=c
                    else:
                        a=assignment[other];oldcell=tables[j][a][chosen]
                        tables[j][a][chosen]*=t;dense_rows[j][a]+=(t-1)*oldcell
        assignment[vertex]=chosen;current=values[chosen];trace.append(current)
        if all_candidates:candidates.append(values)
    if method=='factorized':
        checked=sum((s*z for s,z in zip(scales,total)),F(0))
        cells_used=sum(map(len,cells))
        if cells_used>min(len(edges),len(groups)*Q*Q):raise ArithmeticError('sparse storage')
    elif method=='dense':
        checked=sum((v for tab in tables for row in tab for v in row),F(0))
    else:checked=current
    if checked!=current:raise ArithmeticError('final total')
    loads=[[0]*Q for _ in range(Q)]
    for u,v in edges:loads[assignment['L',u]][assignment['R',v]]+=1
    result={'assignment':assignment,'loads':loads,'groups':groups,'tau':tau,'thresholds':h,
            'initial':initial,'final':current,'trace':trace}
    if all_candidates:result['candidates']=candidates
    return result


def _sparse_prepared(edges,Q,eta,groups,tau,h,incident,all_candidates):
    """Nonnegative support-delta scorer; dictionaries have default value one.

    The selected-potential trace is recovered from exact conditional averaging,
    not from a maintained dense row sum. Requested full candidate lists still
    cost O(VQ); the ordinary interface requests only the selected trace.
    """
    t=1+F(1,eta);c=1+F(1,eta*Q);d=1+F(1,eta*Q*Q)
    scales=[t**(-hj)*d**len(g) for g,hj in zip(groups,h)]
    current=sum((Q*Q*s for s in scales),F(0));initial=current
    xs=[{} for _ in groups];cells=[{} for _ in groups]
    assignment={};trace=[];candidates=[]
    for vertex in sorted(incident):
        isleft=vertex[0]=='L';scores={}
        for j,other in incident[vertex]:
            if isleft:
                scales[j]/=d
                weight=scales[j]*(c-1)*Q
                entries=xs[j].items()
            else:
                a=assignment[other]
                old=xs[j].get(a,ONE);new=old/c
                if new<1:raise ArithmeticError('negative remaining count')
                if new==1:xs[j].pop(a,None)
                else:xs[j][a]=new
                weight=scales[j]*new*(t-1)
                entries=cells[j].get(a,{}).items()
            for label,value in entries:
                delta=weight*(value-1)
                if delta<=0:raise ArithmeticError('nonpositive stored support')
                scores[label]=scores.get(label,F(0))+delta
        total=sum(scores.values(),F(0));mean=total/Q
        if len(scores)<Q:
            chosen=0
            while chosen in scores:chosen+=1
            delta=F(0)
        else:
            chosen=min(scores,key=lambda label:(scores[label],label))
            delta=scores[chosen]
        next_value=current+delta-mean
        if next_value>current:raise ArithmeticError('potential increased')
        if all_candidates:
            values=[current+scores.get(a,F(0))-mean for a in range(Q)]
            if sum(values,F(0))!=Q*current:raise ArithmeticError('averaging identity')
            if values[chosen]!=next_value:raise ArithmeticError('chosen candidate')
            candidates.append(values)
        for j,other in incident[vertex]:
            if isleft:xs[j][chosen]=xs[j].get(chosen,ONE)*c
            else:
                a=assignment[other];row=cells[j].setdefault(a,{})
                row[chosen]=row.get(chosen,ONE)*t
        assignment[vertex]=chosen;current=next_value;trace.append(current)
    # At completion all remaining-left counters are zero: x is identically one.
    if any(xs):raise ArithmeticError('unconsumed endpoint count')
    stored=sum(len(row) for mat in cells for row in mat.values())
    if stored>len(edges):raise ArithmeticError('sparse cell count')
    checked=sum((scales[j]*(Q*Q+sum((v-1 for row in mat.values() for v in row.values()),F(0)))
                 for j,mat in enumerate(cells)),F(0))
    if checked!=current:raise ArithmeticError('final sparse product total')
    loads=[[0]*Q for _ in range(Q)]
    for u,v in edges:loads[assignment['L',u]][assignment['R',v]]+=1
    result={'assignment':assignment,'loads':loads,'groups':groups,'tau':tau,'thresholds':h,
            'initial':initial,'final':current,'trace':trace}
    if all_candidates:result['candidates']=candidates
    return result
