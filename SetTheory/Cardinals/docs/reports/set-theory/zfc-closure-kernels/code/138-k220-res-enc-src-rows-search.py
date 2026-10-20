#!/usr/bin/env python3
"""Exact closed logical-row binding and parameter-permutation exploration.

The full native axiom images are unchanged under each bijective permutation
of the universally enumerated a,b,c parameters.  This search preserves every
primitive instruction position and every guard destination.  It reports
compiler counts only; a resulting decoder table still needs runtime proof.
"""
from pathlib import Path
from functools import cache
import json, sys, itertools, argparse

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from context import OUT
from recompile import s, b, compile_tree, P
HERE = OUT / 'rows'
HERE.mkdir(parents=True, exist_ok=True)

T = b.read_table((P.parent / 'machine/k221.native.tm').read_bytes())
ROWS = json.loads((P.parent / 'machine/sites221.json').read_text())
TREE = s.tree(ROWS)
GRAPH = s.graph_arithmetic(ROWS)[0]
groups, _ = b.decoder_map(T, TREE)
q = lambda k: b.sole(groups, k)
inc = ('CI', 1)
imp = q(90)
neg = q(184)
MACRO = {166:q(98),121:q(12),168:q(166),177:neg[0],119:imp,
         180:(imp,(inc,inc)),181:(imp,inc),182:(imp,((inc,inc),inc)),
         218:neg}
MACRO[183] = (neg,(MACRO[180],neg))

@cache
def flat(n):
    return (n,) if s.leaf(n) else flat(n[0])+flat(n[1])

WORDS = {
    'G': [168,166,182,168,121,182,166,121,181,166,121,182,180,119,119],
    'rho6': [166,166,168,180,183,168,119],
    'rho5': [168,166,182,168,121,181,166,121,181,119,119],
    'rho4': [166,121,168,180,180,121,166,168,180,180,119],
    'rho3': [166,121,182,168,166,181,168,121,181,119,119],
    'rho2': [166,121,168,119,180,166,121,180,166,168,180,119,119],
    'rho1': [166,166,121,182,183],
}
INTERVALS = {'rho8':(135,486),'G':(486,895),'rho6':(895,1178),
             'rho5':(1178,1474),'rho4':(1474,1773),'rho3':(1773,2069),
             'rho2':(2069,2419),'rho1':(2419,2650)}

I=lambda a,b:('I',a,b)
R=lambda a,b:('R',a,b)
Q=lambda a,b:('Q',a,b)
E=lambda a,b:('E',a,b)
N=lambda a:I(a,1)
X=lambda a,b:N(Q(a,N(b)))
a,bb,c,u='a','b','c','u'
FORMULAS = {
    'rho8':I(I(I(c,u),a),I(I(a,c),I(bb,c))),
    'G':I(E(c,a),I(E(c,bb),Q(R(a,bb),E(a,bb)))),
    'rho6':I(X(a,Q(a,c)),c),
    'rho5':I(E(c,a),I(R(c,bb),R(a,bb))),
    'rho4':I(Q(a,Q(bb,c)),Q(bb,Q(a,c))),
    'rho3':I(E(a,bb),I(R(c,a),R(c,bb))),
    'rho2':I(Q(a,I(bb,c)),I(Q(a,bb),Q(a,c))),
    'rho1':X(a,E(a,bb)),
}

def execute(word):
    stack=[]
    for m in word:
        if m in (166,121,168,177):stack.append({166:a,121:bb,168:c,177:1}[m])
        elif m==218:stack.append(N(stack.pop()))
        else:
            y=stack.pop();x=stack.pop()
            stack.append({119:I,180:Q,181:R,182:E,183:X}[m](x,y))
    assert len(stack)==1
    return stack[0]

def seq(xs):
    ans=xs[-1]
    for n in reversed(xs[:-1]):ans=n,ans
    return ans

def bind():
    receipt={}
    for name,word in WORDS.items():
        lo,hi=INTERVALS[name]
        src=seq([MACRO[m] for m in word])
        assert s.boundary(src)==(0,0,False)
        assert flat(src)==tuple(tuple(r[1:])for r in ROWS[lo:hi]),name
        assert execute(word)==FORMULAS[name],name
        receipt[name]={'interval':[lo,hi],'postfix_macros':word,'formula':FORMULAS[name],
                       'closed_macro_composition':True,'exact_flat_binding':True}
    # rho8's u is read once from the proof-data enumeration stream, then moved
    # to the current top.  Only the surrounding closed pushes/implications are
    # modified in the register-permutation experiment below.  This opaque
    # middle segment has no reference to any permuted parameter register.
    chunks=[(135,161,168),(194,221,119),(221,247,166),(247,274,119),
            (274,300,166),(300,326,168),(326,353,119),(353,379,121),
            (379,405,168),(405,432,119),(432,459,119),(459,486,119)]
    for lo,hi,m in chunks:
        assert flat(MACRO[m])==tuple(tuple(r[1:])for r in ROWS[lo:hi])
    assert all(not(op in ('CI','CD')and arg in(3,4,5))for _,op,arg in ROWS[161:194])
    receipt['rho8']={'interval':[135,486],'formula':FORMULAS['rho8'],
                     'exact_bound_macro_chunks':chunks,'unchanged_u_reader':[161,194],
                     'u_reader_parameter_registers_disjoint':True}
    (HERE/'binding.json').write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt

def changed(perms):
    rr=[r.copy()for r in ROWS]
    for name,vals in perms.items():
        mp=dict(zip((3,4,5),vals));lo,hi=INTERVALS[name]
        for i in range(lo,hi):
            if rr[i][1]in('CI','CD')and rr[i][2]in mp:
                rr[i][2]=mp[rr[i][2]]
    gg=s.graph_arithmetic(rr)[0]
    assert [x[1]for x in gg]==[x[1]for x in GRAPH]
    assert gg==s.graph_intervals(rr)
    return rr,s.tree(rr)

def check_variant(perms,save=True):
    rr,tt=changed(perms)
    result={'permutations':perms,'source_metrics':s.metrics(tt)}
    nm='__'.join(k+'_'+''.join(map(str,v))for k,v in perms.items())
    try:
        U,m=compile_tree(T,TREE,tt)
        result['compiler']=m
    except Exception as e:
        result['error']=repr(e)
        U=None
    if save:
        pd=HERE/nm;pd.mkdir(exist_ok=True)
        (pd/'sites.json').write_bytes(s.compact(rr))
        if U:(pd/'candidate.tm').write_bytes(b.table_bytes(U))
        (pd/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--pairs',action='store_true');args=ap.parse_args()
    bind()
    summary=[]
    for name in INTERVALS:
        for vals in itertools.permutations((3,4,5)):
            result=check_variant({name:vals});summary.append(result)
            print(json.dumps(result),flush=True)
    (HERE/'individual_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    if args.pairs:
        pairsummary=[]
        for one,two in itertools.combinations(INTERVALS,2):
            for v1,v2 in itertools.product(itertools.permutations((3,4,5)),repeat=2):
                if v1==(3,4,5)or v2==(3,4,5):continue
                result=check_variant({one:v1,two:v2},save=False);pairsummary.append(result)
                if result.get('compiler',{}).get('working_states',999)<=221:
                    check_variant({one:v1,two:v2},save=True);print(json.dumps(result),flush=True)
        (HERE/'pair_summary.json').write_text(json.dumps(pairsummary,indent=2)+'\n')

if __name__=='__main__':main()
