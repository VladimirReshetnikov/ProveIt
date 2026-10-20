#!/usr/bin/env python3
"""Sixteen independent formula-field orientations with exact postfix emission.

All AX constructors reuse the original arithmetic macro.  Their operands
are emitted in reversed order exactly for selected constructors.  GEN swaps
the two parameter pushes.  Reversed implication changes only the closed
pairing loop of the MP builder, because MP's antecedent is already in top.
"""
from functools import cache
import collections,itertools,json
import additive_binder as z
from h_fusion import splice

OUT=z.ROOT/'research_calculus/generated/orientation_postfix'
F=z.flat(z.TREE);IMP=z.q(90);NEG=z.q(184);INC=('CI',1)

@cache
def atoms(t):
    assert z.s.boundary(t)==(0,0,False)
    if z.s.leaf(t)or any(z.s.boundary(c)!=(0,0,False)for c in t):return(t,)
    return atoms(t[0])+atoms(t[1])

def closed_forest(lo,hi):
    out=[]
    def visit(t,i=0):
        j=i+len(z.flat(t))
        if j<=lo or i>=hi:return
        if lo<=i and j<=hi:
            assert z.s.boundary(t)==(0,0,False),(i,j,z.s.boundary(t))
            out.append(t);return
        assert not z.s.leaf(t)
        visit(t[0],i);visit(t[1],i+len(z.flat(t[0])))
    visit(z.TREE);assert sum(len(z.flat(t))for t in out)==hi-lo
    return out

U=z.serial(closed_forest(161,194))
M={'a':z.q(98),'b':z.q(12),'c':z.q(166),'u':U,1:NEG[0],
   'I':IMP,'R':(IMP,INC),'Q':(IMP,(INC,INC)),
   'E':(IMP,((INC,INC),INC))}
I=lambda a,b:('I',a,b)
R=lambda a,b:('R',a,b)
Q=lambda a,b:('Q',a,b)
E=lambda a,b:('E',a,b)
N=lambda a:I(a,1)
X=lambda a,b:N(Q(a,N(b)))
a,b,c,u='a','b','c','u'
r=R(b,c);sub=Q(c,I(R(c,a),R(c,b)))
w=Q(b,I(c,N(Q(b,I(c,N(r))))))
uu=Q(a,I(sub,w));h=Q(b,I(r,N(Q(a,I(c,N(uu))))))
v=I(R(a,b),Q(c,R(a,b)))
BUNDLE=N(I(v,Q(c,I(h,N(w)))))
FORMULAS=[
    I(I(I(c,u),a),I(I(a,c),I(b,c))),
    I(E(c,a),I(E(c,b),Q(R(a,b),E(a,b)))),
    I(X(a,Q(a,c)),c),
    I(E(c,a),I(R(c,b),R(a,b))),
    I(Q(a,Q(b,c)),Q(b,Q(a,c))),
    I(E(a,b),I(R(c,a),R(c,b))),
    I(Q(a,I(b,c)),I(Q(a,b),Q(a,c))),
    X(a,E(a,b)),BUNDLE]

def postfix(t,mask):
    if not isinstance(t,tuple):return[t]
    op,a,b=t
    if op in mask:a,b=b,a
    return postfix(a,mask)+postfix(b,mask)+[op]

def symbolic(word,mask):
    st=[]
    for k in word:
        if k not in ['I','R','Q','E']:st.append(k);continue
        b=st.pop();a=st.pop()
        if k in mask:a,b=b,a
        st.append((k,a,b))
    assert len(st)==1
    return st[0]

ORIGINAL_WORD=sum((postfix(t,set())for t in FORMULAS),[])
ORIGINAL_ATOMS=sum((atoms(M[m])for m in ORIGINAL_WORD),())
assert sum((z.flat(t)for t in ORIGINAL_ATOMS),())==F[135:4563]

def compose(newatoms):
    iatom=0;oldatoms=[]
    def visit(t,i=0):
        nonlocal iatom
        j=i+len(z.flat(t))
        if j<=135 or i>=4563:return t
        if 135<=i and j<=4563 and z.s.boundary(t)==(0,0,False):
            if z.s.leaf(t)or any(z.s.boundary(c)!=(0,0,False)for c in t):
                oldatoms.append(t);q=newatoms[iatom];iatom+=1;return q
        assert not z.s.leaf(t)
        return(visit(t[0],i),visit(t[1],i+len(z.flat(t[0]))))
    result=visit(z.TREE)
    assert tuple(oldatoms)==ORIGINAL_ATOMS
    assert iatom==len(newatoms)==len(ORIGINAL_ATOMS)
    return result

def extra_commands(tree,mask):
    rows=z.s.sites(tree)
    assert len(rows)==len(z.ROWS)
    if 'Q'in mask:
        # GEN was push(a), push(h), Q; exchange the two same-shape pushes.
        for i in range(40,92):
            if rows[i][1]in('CI','CD')and rows[i][2]in(4,5):rows[i][2]=9-rows[i][2]
    if 'I'in mask:
        # MP pair core, after pop(left)->scratch6, before scale7->top1.
        assert F[4689:4699]==z.flat(IMP[1][0])
        for i in range(4689,4699):
            if rows[i][1]in('CI','CD')and rows[i][2]in(1,6):rows[i][2]=7-rows[i][2]
    return z.s.tree(rows)

def make(mask):
    words=[postfix(t,mask)for t in FORMULAS]
    assert all(symbolic(word,mask)==t for word,t in zip(words,FORMULAS))
    newatoms=sum((atoms(M[m])for w in words for m in w),())
    assert collections.Counter(newatoms)==collections.Counter(ORIGINAL_ATOMS)
    tree=extra_commands(compose(newatoms),mask)
    ref=extra_commands(splice(z.TREE,135,4563,z.serial(newatoms)),mask)
    rows=z.s.sites(tree);rr=z.s.sites(ref)
    assert z.flat(tree)==z.flat(ref)
    g=z.s.graph_arithmetic(rows)[0]
    assert g==z.s.graph_intervals(rows)==z.s.graph_arithmetic(rr)[0]==z.s.graph_intervals(rr)
    if not mask:assert tree==z.TREE
    return tree,words

def test_reversed_pair():
    loop=IMP[1][0]
    def swap(t):
        if z.s.leaf(t):
            op,n=t
            return(op,7-n)if op in('CI','CD')and n in(1,6)else t
        return(swap(t[0]),swap(t[1]))
    core=(IMP[0],(swap(loop),IMP[1][1]))
    pair=lambda a,b:(a+b)*(a+b+1)//2+b
    count=0
    for a in range(4):
        for b in range(4):
            for older in range(3):
                regs=[17,b,pair(a,older),8,6,9,0,0,4]
                got,_=z.runmacro(core,regs)
                want=regs.copy();want[1]=4*pair(b,a);want[2]=older
                assert got==want,(a,b,older,got,want)
                count+=1
    return count

def main():
    OUT.mkdir(parents=True,exist_ok=True);tests=test_reversed_pair();res=[]
    for bits in itertools.product([False,True],repeat=4):
        mask={op for op,yes in zip(['I','Q','E','R'],bits)if yes}
        name=''.join(op if op in mask else '-'for op in ['I','Q','E','R'])
        tree,words=make(mask);rows=z.s.sites(tree);d=OUT/name;d.mkdir(exist_ok=True)
        (d/'sites.json').write_bytes(z.s.compact(rows))
        result=dict(name=name,reversed_constructors=sorted(mask),source_metrics=z.s.metrics(tree),
                    semantics='Exact symbolic AX postfix decoding, closed-atom CFG equivalence; GEN operands swapped when Q reversed; MP pair loop swapped when I reversed.',
                    MP_reversed_pair_finite_cases=tests,AX_closed_atom_count=len(ORIGINAL_ATOMS),AX_postfix=words)
        try:
            table,m=z.compile_tree(z.T,z.TREE,tree);result['compiler']=m
            (d/'candidate.tm').write_bytes(z.b.table_bytes(table))
        except Exception as e:result['compile_error']=repr(e)
        (d/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');res.append(result)
        print(json.dumps({k:v for k,v in result.items()if k!='AX_postfix'}),flush=True)
    (OUT/'summary.json').write_text(json.dumps(res,indent=2)+'\n')

if __name__=='__main__':main()
