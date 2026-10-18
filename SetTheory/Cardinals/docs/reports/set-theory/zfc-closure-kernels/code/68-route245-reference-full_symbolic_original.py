#!/usr/bin/env python3
"""Whole-frame symbolic replay with interval-specialized primary registers.

Every nonconstant primary has its own quantified natural variable. The gap
has a separate variable, and the nonempty spare suffix has an arbitrary first
value followed by an arbitrary finite block list. Register boxes are expanded.
Only checked one-block/list induction rules accelerate traversal of the tail.
"""
from pathlib import Path
from collections import Counter
import argparse, importlib.util, json, sys, time

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'reference/context246'
sys.path.insert(0,str(BASE/'code'))
import rebuild_machines as rebuild
import review_affine_source as paths
import abstract_program as abstract

spec=importlib.util.spec_from_file_location('whole_frame_inductions',BASE/'code/check_macro_inductions.py')
m=importlib.util.module_from_spec(spec);sys.modules[spec.name]=m;spec.loader.exec_module(m)
E, Run, Blocks, Blank, Conf = m.E, m.Run, m.Blocks, m.Blank, m.Conf

def make_file(values):
    return [atom for v in values for atom in m.B(v)] + m.B(E.var('spare_first')) + [Blocks('B','spare_tail'),Blank()]

def normalize(c):
    c.left=m.norm(c.left,c.state==48 and c.side=='L')
    c.right=m.norm(c.right)

def step(c, cost, motion, trace):
    normalize(c)
    answer=m.apply_list_induction(c,cost,motion,trace)
    if answer is not None: return answer
    source=c.right if c.side=='R' else c.left
    target=c.left if c.side=='R' else c.right
    if not source: raise AssertionError('unrepresented exterior')
    if isinstance(source[0],Blank): source.insert(0,m.bit(0))
    atom=source[0]
    assert isinstance(atom,Run),(c.state,c.side,atom,'opaque list reached without a checked traversal lemma')
    w,d,q=m.TABLE[c.state,atom.bit]
    old=c.state
    if d==c.side and q==c.state:
        source.pop(0);target.insert(0,Run(w,atom.length))
        cost+=atom.length;motion+=atom.length*(1 if d=='R' else -1)
        trace.append(dict(rule='unary-induction',state=old,read=atom.bit,row=[w,d,q],repetitions=str(atom.length)))
    else:
        assert atom.length.c>=1,(old,c.side,atom,'unjustified branch')
        source[0]=Run(atom.bit,atom.length+-1)
        if d==c.side: target.insert(0,m.bit(w))
        else: source.insert(0,m.bit(w));c.side=d
        c.state=q;cost+=1;motion+=1 if d=='R' else -1
        trace.append(dict(rule='literal',state=old,read=atom.bit,row=[w,d,q]))
    normalize(c)
    return cost,motion

def case(pc,op,r,zero,intervals):
    logical=[E(lo) if lo==hi and hi<9 else E(lo)+E.var('r'+str(i)) for i,(lo,hi) in enumerate(intervals)]
    if op=='CD': logical[r]=E() if zero else E(max(1,intervals[r][0]))+E.var('r'+str(r))
    values=[None]*9
    for i,j in enumerate(rebuild.PHYSICAL): values[j]=logical[i]
    extra=0;overflow=False;output=values.copy();add_spare=False
    if op=='CI': successor,overflow=paths.full_inc(pc);output[rebuild.PHYSICAL[r]]+=1;add_spare=True
    elif op=='CD' and not zero: successor,overflow=paths.full_inc(pc);output[rebuild.PHYSICAL[r]]+=-1;extra=1
    elif op=='CD':successor,overflow=paths.full_inc(paths.full_strip(pc,'0',1))
    elif op=='CB':successor,overflow=paths.full_inc(paths.full_strip(pc,'0',r))
    elif op=='CC':successor=paths.full_strip(pc,'1',r)
    else: successor=''
    start_right=[m.bit(int(b)) for b in pc]+[Run(0,E.var('gap')+(40-len(pc))),m.bit(1)]+make_file(values)
    c=Conf(96,'R',[m.bit(1),Blank()],start_right)
    out_file=make_file(output)
    if add_spare: out_file=out_file[:-1]+m.B(E(1))+[Blank()]
    target=Conf(96,'R',[m.bit(1),Blank()],[m.bit(int(b)) for b in successor]+[Run(0,E.var('gap')+(40+extra+int(overflow)-len(successor))),m.bit(1)]+out_file)
    normalize(c);normalize(target)
    cost=E();motion=E();trace=[]
    for _ in range(3000):
        if trace and ((op=='CH' and c.state==254) or (op!='CH' and c.key()==target.key())):
            assert cost.nonnegative() and cost.c>=1,'positive progress is required'
            if op!='CH': assert motion==E(-int(overflow)),('unexpected head displacement',pc,motion)
            return dict(rules=len(trace),cost=str(cost),time_lower_bound=cost.c,motion=str(motion),trace=trace)
        cost,motion=step(c,cost,motion,trace)
    raise AssertionError(('symbolic fuel exhausted',pc,op,r,zero,c.key(),target.key()))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int);ap.add_argument('--table',type=Path);ap.add_argument('--all-values',action='store_true');ap.add_argument('--sites',type=Path,help='Alternative physical-index sites; requires --all-values and a separately checked program equivalence.');ap.add_argument('--output',type=Path);args=ap.parse_args()
    assert __debug__
    assert args.limit is None or args.limit>0
    if args.table:m.TABLE=rebuild.read_table(args.table)[0]
    m.prove_blocks();m.prove_word_identity()
    sites=rebuild.program_sites()
    invariant_path=ROOT/'results/interval-invariants.json'
    certificate=json.loads(invariant_path.read_text())
    from hashlib import sha256
    source_hash=sha256((BASE/'sources/Prog254.v').read_bytes()).hexdigest()
    assert certificate['source_sha256']==source_hash
    vals,closure_edges=abstract.validate_invariants(sites,certificate['invariants'])
    if args.sites:
        assert args.all_values,'Changed source addresses require their own invariant or universal all-values replay.'
        loaded=json.loads(args.sites.read_text())
        assert isinstance(loaded,list) and len(loaded)==6460
        inverse={v:i for i,v in enumerate(rebuild.PHYSICAL)}
        sites=[]
        trie={}
        for p,op,r in loaded:
            assert isinstance(p,str) and 1<=len(p)<=34 and set(p)<=set('01')
            assert op in ('CI','CD','CB','CC','CH')
            assert (r is None) if op=='CH' else (type(r) is int and r>=0)
            if op in ('CI','CD'):assert r in inverse
            t=trie
            for b in p:
                assert 'leaf' not in t,'A source address prefixes another.'
                t=t.setdefault(b,{})
            assert not t,'Duplicate address or nonleaf endpoint.'
            t['leaf']=True
            sites.append((p,op,inverse[r] if op in ('CI','CD') else r))
        def full(t):
            assert set(t)=={'leaf'} or set(t)=={'0','1'}
            if 'leaf' not in t:full(t['0']);full(t['1'])
        full(trie)
    if args.all_values:vals=[[[0,9]]*9 for _ in sites]
    counts=Counter();rows=set();cases=[];began=time.monotonic()
    for i,(p,op,r) in enumerate(sites):
        v=vals[i]
        if v is None:continue
        for zero in ((True,False) if op=='CD' else (None,)):
            if op=='CD' and ((zero and v[r][0]>0) or (not zero and v[r][1]==0)):continue
            result=case(p,op,r,zero,v)
            for t in result['trace']:
                if 'state' in t: rows.add((t['state'],t['read']))
            counts['cases']+=1;counts['symbolic_rules']+=result['rules']
            cases.append(dict(index=i,pc=p,op=op,r=r,zero=zero,**{k:x for k,x in result.items() if k!='trace'}))
            if args.limit and counts['cases']>=args.limit:break
        if args.limit and counts['cases']>=args.limit:break
    table_path=args.table or BASE/'machine/zfc_prefix246_old.tm'
    expected_cases=sum(0 if v is None else (int(v[r][0]==0)+int(v[r][1]>0) if op=='CD' else 1) for (p,op,r),v in zip(sites,vals))
    complete=counts['cases']==expected_cases
    if args.limit is None:assert complete
    out=dict(status='PASS' if complete else 'PASS_LIMITED',complete=complete,expected_cases=expected_cases,scope='symbolic arbitrary gap, independent primary naturals at admitted lower bounds, nonempty arbitrary spare suffix',
        source_sha256=source_hash,table_sha256=sha256(table_path.read_bytes()).hexdigest(),
        alternative_sites_sha256=sha256(args.sites.read_bytes()).hexdigest() if args.sites else None,
        invariant_sha256=sha256(invariant_path.read_bytes()).hexdigest(),
        invariant_closure_edges=closure_edges,positive_progress_checked=True,minimum_steps=min(x['time_lower_bound'] for x in cases),
        counts=dict(counts),seconds=time.monotonic()-began,rows=sorted(rows),cases=cases)
    filename='full-symbolic-results'+('-all-values' if args.all_values else '')+('-'+args.table.stem if args.table else '')+('-limit'+str(args.limit) if args.limit else '')+'.json'
    destination=args.output or ROOT/'results'/filename
    destination.parent.mkdir(parents=True,exist_ok=True)
    destination.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('cases','rows')},indent=2));print('rows',len(rows))

if __name__=='__main__':main()
