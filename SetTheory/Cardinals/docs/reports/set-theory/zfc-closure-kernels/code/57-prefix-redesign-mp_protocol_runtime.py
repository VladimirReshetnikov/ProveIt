#!/usr/bin/env python3
"""Delete the redundant successful-MP zero push in the optimized decoder.

The whole register program changes only at the closed success par1 subroutine:
push171;copy167 becomes copy167. Counts concern an emitted literal table, with
the source arithmetic site guards checked under unchanged box contracts.
"""
from pathlib import Path
import hashlib,json,re,sys,tempfile,time
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'source/Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0,str(BASE))
import candidate252_independent_audit as audit
import breakthrough_register_permutation as a
from permutation252_fold_search import Tracking


def tree(raw):
    body=raw.split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    return re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',body)


def subtree(nodes,path):
    q=0
    for bit in path:
        op,n=nodes[q][int(bit)].split();assert op=='CN';q=int(n)
    return q


def sites(nodes):
    out=[]
    def visit(q,path):
        for bit,edge in enumerate(nodes[q]):
            op,*args=edge.split();p=path+str(bit)
            if op=='CN':visit(int(args[0]),p)
            else:
                r=int(args[0]) if args else None
                out.append((p,op,a.PHYS[r] if op in ('CI','CD') else r))
    visit(0,'');return out


def generate():
    scratch=Path(tempfile.mkdtemp(prefix='zfc-mp-runtime-'))
    a.prepare(audit.ROOT,scratch)
    raw=(BASE/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes()
    original=audit.read_table(raw)
    table={(str(q),bit):(w,d,str(t)) for (q,bit),(w,d,t) in original.items()}
    assert a.certify(table,audit.PERM)['passed']
    ns=tree((audit.ROOT/'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v').read_text())
    prefix='111111'
    outer,inner=subtree(ns,prefix),subtree(ns,prefix+'1')
    ns[outer]=ns[inner]
    a.sites=sites(ns)
    assert table['204',1]==(1,'R','113')
    table['204',1]=(1,'R','132')
    return table,ns


def guards():
    out=[]
    for p,op,r in a.sites:
        for zero in ((True,False) if op=='CD' else (None,)):
            physical=audit.PERM[r] if op in ('CI','CD') else r
            branch=(physical,zero) if op=='CD' else None
            if op=='CI' or op=='CD' and not zero:succ=a.inc(p)
            elif op=='CD':succ=a.inc(a.strip(p,'0',1))
            elif op=='CB':succ=a.inc(a.strip(p,'0',r))
            elif op=='CC':succ=a.strip(p,'1',r)
            else:succ=''
            effect=('inc',physical) if op=='CI' else ('dec',physical) if op=='CD' and not zero else None
            right=([('r',0,1,41),('b',1),('box',('plain',effect))] if succ is None else
                   [('b',int(b)) for b in succ]+[('r',0,1,40-len(succ)),('b',1),('box',('plain',effect))])
            out.append((p,op,branch,a.strict.canon([('b',1)],right)))
    return out


def certify(table,cases):
    for i,(p,op,branch,target) in enumerate(cases):
        try:
            rules,literal=a.strict.run(table,p,branch,target,halt=op=='CH',fuel=1000)
            assert literal>0
        except (AssertionError,KeyError) as e:
            return dict(passed=False,cases_passed=i,failure=str(e),path=p,op=op)
    return dict(passed=True,cases_passed=len(cases))


def main():
    table,ns=generate()
    result=dict(scope=__doc__,working_states=len(table)//2,source_sites=len(a.sites),
                source_cases=sum(2 if op=='CD' else 1 for _,op,_ in a.sites),
                change={'state':204,'read':1,'before':[1,'R',113],'after':[1,'R',132]})
    result['affine']=certify(table,guards())
    print(json.dumps(result,indent=2),flush=True)
    out=HERE/'mp_runtime';out.mkdir(exist_ok=True)
    (out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    (out/'modified-tree.json').write_text(json.dumps(ns,indent=2)+'\n')
    (out/'modified252.tm').write_bytes(a.encoded(table))


if __name__=='__main__':main()
