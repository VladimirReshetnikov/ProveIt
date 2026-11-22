"""Encode the archived rational balls, support directions and dyadic trees for Lean.
Run from any directory with --code and --data pointing to the replayed bundle.
The generated Lean checker proves every support-direction and integer inequality.
"""
import argparse
import csv
import json
from fractions import Fraction as F
from pathlib import Path
import sys

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--code',type=Path,default=Path(__file__).parent)
    ap.add_argument('--data',type=Path,default=Path(__file__).parents[1]/'data')
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args()
    sys.path.insert(0,str(args.code.resolve()))
    import verify as v
    import geometry as g
    args.out.mkdir(exist_ok=True,parents=True)
    trees=json.loads((args.data/'trees.json').read_text())
    rows=list(csv.DictReader((args.data/'distances.csv').open(newline='')))
    balls={}
    claims={}
    root_trees=json.loads((args.data/'root_trees.json').read_text())
    def ball(b):
        if b not in balls:
            balls[b]='b'+str(len(balls))
        return balls[b]
    def gate_ball(c,t):
        name=ball(v.boundary(c,t))
        claims[(c,str(t))]=name
        return name
    def term(x,y,h):
        return f'⟨{x},{y},{h}⟩'
    def literal_list(xs):
        return '['+','.join(xs)+']'
    def wordcase(word,st,en,guess,tree):
        it=iter(tree)
        gates='' if word=='direct' else word
        def walk(spans):
            tag=next(it)
            mids=tuple((l+r)/2 for l,r in spans)
            if tag=='i':
                return '(.inside)'
            if tag=='/':
                j=max(range(len(gates)),key=lambda j:spans[j][1]-spans[j][0])
                l,r=spans[j]; m=mids[j]
                nm=gate_ball(gates[j],m)
                prefix,suffix=spans[:j],spans[j+1:]
                first=walk(prefix+((l,m),)+suffix)
                second=walk(prefix+((m,r),)+suffix)
                return '(.split '+nm+' '+first+' '+second+')'
            assert tag in ('w','m')
            ts=mids if tag=='m' else tuple(min(r,max(l,t)) for (l,r),t in zip(spans,guess,strict=True))
            ds=v.directions(v.witness(st,en,gates,ts))
            coeffs=[term(x,y,v.normhi(u-x,z-y)) for (u,z),(x,y) in zip(ds,ds[1:])]
            return '(.leaf '+literal_list(coeffs)+')'
        code=walk(((F(0),F(1)),)*len(gates))
        assert next(it,None) is None
        start=literal_list(['⟨'+gate_ball(c,F(0))+','+gate_ball(c,F(1))+','+
                            ('true' if c in 'AB' else 'false')+',0,0⟩' for c in gates])
        return code,start
    groups={}
    for row in rows:
        p,q=row['from'],row['to']
        st,en=(v.center(g.point_box(a)) for a in (p,q))
        claims[(p,'')]=ball(st); claims[(q,'')]=ball(en)
        case=p+'_'+q
        guess=tuple(map(F,row['upper_gate_parameters'].split()))
        word=row['upper_route']
        upper=v.int_value(row['upper']); low=v.int_value(row['lower'])
        terms=[]
        for w,t in sorted(trees[p+'-'+q].items()):
            floor=low if w==word else v.int_value(row['other_routes_lower'])
            tree,initial=wordcase(w,st,en,guess,t)
            terms.append(f'theorem {case}_{w} : verifyTree {ball(st)} {ball(en)} {floor}\n  {tree}\n  {initial} = true := by decide +kernel\n')
        if p+'-'+q in root_trees:
            tree,initial=wordcase(word,st,en,guess,root_trees[p+'-'+q])
            indices=[(4096*t).__floor__() for t in guess]
            region=literal_list([f'({i-1},{i+2},4096)' for i in indices])
            terms.append(f'theorem {case}_isolation : verifyWith {ball(st)} {ball(en)} {upper+1} {region}\n  {tree}\n  {initial} = true := by decide +kernel\n')
        for c,t in zip('' if word=='direct' else word,guess,strict=True):
            gate_ball(c,t)
        stops=v.witness(st,en,'' if word=='direct' else word,guess)
        bounds=literal_list([str(v.normhi(x[0]-y[0],x[1]-y[1])) for x,y in zip(stops,stops[1:])])
        terms.append(f'theorem {case}_upper : upperOK {ball(st)} {literal_list(map(ball,stops[1:]))} {bounds} {upper} = true := by decide +kernel\n')
        groups[case]=terms
    header='import ReplayCore\nnamespace Oloid.Replay.Data\n'
    (args.out/'ReplayBalls.lean').write_text(header+'\n'.join(f'def {name} : Ball := {term(*coords)}' for coords,name in balls.items())+'\nend Oloid.Replay.Data\n')
    with (args.out/'analytic_inputs.csv').open('w',newline='') as stream:
        cw=csv.writer(stream,lineterminator='\n')
        cw.writerow(['point_or_gate','fraction_if_gate','ball_in_Lean'])
        for (c,t),name in sorted(claims.items()):
            cw.writerow([c,t,name])
    names=[]
    for no,(case,terms) in enumerate(groups.items(),1):
        name=f'ReplayPair{no:02d}';names.append(name)
        (args.out/(name+'.lean')).write_text('import ReplayBalls\nset_option maxHeartbeats 0\nset_option maxRecDepth 200000\nnamespace Oloid.Replay.Data\n'+'\n'.join(terms)+'end Oloid.Replay.Data\n')
    (args.out/'AllReplay.lean').write_text(''.join('import '+name+'\n' for name in names))
    print(len(rows),'pairs;',sum(map(len,groups.values())),'theorems;',len(balls),'input balls.')
if __name__=='__main__':
    main()
