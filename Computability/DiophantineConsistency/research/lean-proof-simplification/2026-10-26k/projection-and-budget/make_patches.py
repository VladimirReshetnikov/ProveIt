#!/usr/bin/env python3
"""Generate proof-only candidates against the pinned input; never edit the repo."""
from pathlib import Path
import argparse, difflib, hashlib, json

BASE = '6175dff9a15491497c7a3c1bda4f6a62a6349c74'
REL = Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency')
HERE = Path(__file__).resolve().parent

def patch_file(before, after, rel):
    return ''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
        fromfile='a/'+str(rel), tofile='b/'+str(rel)))

def replace_proof(text, name, new, start_token='    constructor', end_token=')'):
    start = text.index('def '+name)
    a = text.index(start_token, start)
    next_decl = text.find('\n\n', a)
    # Each targeted declaration ends at the first following blank line.
    block = text[a:next_decl]
    assert block.endswith(end_token), (name, block[-70:])
    return text[:a]+new+text[next_decl:]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True)
    args=ap.parse_args();repo=args.repo
    out=HERE/'patched-modules';out.mkdir(exist_ok=True)
    (HERE/'patches').mkdir(exist_ok=True)
    metrics=[];pair_diff=''
    for file, left, right in [
        ('PairingRepresentation','unpairLeftCoordinate','unpairRightCoordinate'),
        ('QuadraticNatPairing','leftRepresentation','rightRepresentation'),
        ('RegisterNatPairing','leftRelation','rightRelation'),
        ('QuadraticTreeCodeGraphs','treeLeftRepresentation','treeRightRepresentation')]:
        old=(repo/REL/(file+'.lean')).read_text();new=old
        new='import DiophantineConsistency.PairingProjection\n'+new
        for name, side in [(left,'right'),(right,'left')]:
            # side names indicate the existential component, not the retained projection.
            if file=='PairingRepresentation':
                body=(f'  simp only [Fin.exists_fin_succ_pi, Fin.exists_fin_zero_pi, Fin.cons_zero]\n'
                      f'  exact PairingProjection.exists_{side}_iff Nat.pairEquiv (v (some 0)) (v none)')
                new=replace_proof(new,name,body,start_token='  constructor',end_token='Nat.pair_unpair]')
            elif file=='QuadraticNatPairing':
                components='(v 0) b' if side=='right' else 'b (v 0)'
                body=(f'    simp only [Fin.exists_fin_succ_pi, Fin.exists_fin_zero_pi]\n'
                      f'    change (∃ b t s m, Certificate (v 1) {components} t s m) ↔ _\n'
                      f'    simp only [exists_certificate_iff]\n'
                      f'    exact PairingProjection.exists_{side}_iff Nat.pairEquiv (v 1) (v 0))')
                new=replace_proof(new,name,body)
            elif file=='RegisterNatPairing':
                components='(v 0) b' if side=='right' else 'b (v 0)'
                body=(f'    symm\n'
                      f'    simp only [Fin.exists_fin_succ_pi, Fin.exists_fin_zero_pi]\n'
                      f'    change (∃ b s, certificateLeft (v 1) {components} s =\n'
                      f'      certificateRight (v 1) {components} s) ↔ _\n'
                      f'    simp only [exists_certificate_iff]\n'
                      f'    exact PairingProjection.exists_{side}_iff Nat.pairEquiv (v 1) (v 0)')
                new=replace_proof(new,name,body,end_token='Nat.unpair_pair]')
            else:
                components='(v 0) b' if side=='right' else 'b (v 0)'
                projection='1' if side=='right' else '2'
                body=(f'    simp only [Fin.exists_fin_succ_pi, Fin.exists_fin_zero_pi]\n'
                      f'    change (∃ p b t s m, p = (v 1).pred ∧\n'
                      f'      QuadraticNatPairing.Certificate p {components} t s m) ↔\n'
                      f'      v 0 = (Nat.unpair (v 1).pred).{projection}\n'
                      f'    simp only [exists_and_left, exists_eq_left, QuadraticNatPairing.exists_certificate_iff]\n'
                      f'    exact PairingProjection.exists_{side}_iff Nat.pairEquiv (v 1).pred (v 0))')
                new=replace_proof(new,name,body)
        dest=out/REL/(file+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(new)
        pair_diff+=patch_file(old,new,REL/(file+'.lean'))
        metrics.append(dict(file=file+'.lean',before=len(old.splitlines()),after=len(new.splitlines()),
            sha256_before=hashlib.sha256(old.encode()).hexdigest()))
    helper=(HERE/'lean/DiophantineConsistency/PairingProjection.lean').read_text()
    pair_diff+=patch_file('',helper,REL/'PairingProjection.lean')
    metrics.append(dict(file='PairingProjection.lean',before=0,after=len(helper.splitlines())))
    (HERE/'patches/pairing-projections.patch').write_text(pair_diff)

    # Collapse three arithmetic budgeting arguments without changing representation constructors.
    old=(repo/REL/'GraphSizeBounds.lean').read_text();new=old
    new='import DiophantineConsistency.AffineBudget\n'+new
    target_specs=[('namespace Rep','thin_compose','compose_depth_le','2 * n + 2','n',
                   'BoundedForallSize.predicate_compose_count'),
                  ('namespace GraphRep','thin_composeDirect','composeDirect_depth_le','2 * n + 2','n',
                   'composeDirect_witnessCount'),
                  ('namespace GraphRep','thin_compose','compose_depth_le','2 * n + 4','n + 1',
                   'compose_witnessCount')]
    for ns,name,rule,overhead,credits,count in target_specs:
        i=new.index('theorem '+name+' ',new.index(ns))
        a=new.index('  let w :=',i)
        b=new.find('\n\n',a)
        replacement=(f'  exact AffineBudget.compose\n'
                     f'    (fun i => (s i).witnessCount) (fun i => (s i).depth) hC hr hs\n'
                     f'    (fun _ hh hr hs => {rule} r s hh hr hs)\n'
                     f'    (by omega : {overhead} ≤ 6 * ({credits}))\n'
                     f'    (by rw [{count}]; omega)')
        new=new[:a]+replacement+new[b:]
    dest=out/REL/'GraphSizeBounds.lean';dest.write_text(new)
    helper=(HERE/'lean/DiophantineConsistency/AffineBudget.lean').read_text()
    diff=patch_file(old,new,REL/'GraphSizeBounds.lean')+patch_file('',helper,REL/'AffineBudget.lean')
    (HERE/'patches/affine-budgets.patch').write_text(diff)
    budget_metrics=[dict(file='GraphSizeBounds.lean',before=len(old.splitlines()),after=len(new.splitlines())),
                    dict(file='AffineBudget.lean',before=0,after=len(helper.splitlines()))]
    (HERE/'metrics.json').write_text(json.dumps(dict(base=BASE,pairing=metrics,budget=budget_metrics),indent=2)+'\n')

if __name__=='__main__':main()
