from pathlib import Path
from hashlib import sha256
import json, re, sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D = Path('research/ordinary13-pell-period-six-replacements-composition-draft')
selection = json.loads((D/'selection.json').read_text())
for name, spec in selection.items():
    p = Path(spec['path']); data = p.read_bytes()
    assert sha256(data).hexdigest() == spec['sha256'], p
    assert re.findall(r'^import\s+(\S+)',data.decode(),re.M) == spec['imports'], name
for n in ('PellPeriodCReplacement', 'PellPeriodHReplacement', 'PellPeriodXYReplacements', 'PellPeriodFullWB', 'PellPeriodFinalBodyEval', 'PellPeriodFinalReplacements'):
    assert 'DiophantineConsistency.'+n in selection
root = 'DiophantineConsistency.PellPeriodSixReplacementsComposition'
frontier = {}; visiting = set(); done = set(); order = []
def visit(n):
    if n in done: return
    assert n not in visiting, n
    visiting.add(n)
    for dep in selection[n]['imports']:
        if dep in selection: visit(dep)
        else:
            if dep.startswith('DiophantineConsistency.'):
                suffix=dep.removeprefix('DiophantineConsistency.').replace('.','/')
                path=Path('Lean/DiophantineConsistency')/(suffix+'.lean')
                assert path.is_file(), dep
                frontier[dep]={'kind':'project-source', 'path':str(path), 'sha256':sha256(path.read_bytes()).hexdigest()}
            else: frontier[dep]={'kind':'external-unexamined'}
    visiting.remove(n); done.add(n); order.append(n)
visit(root)
assert done == set(selection), sorted(set(selection)-done)
s=Path(selection[root]['path']).read_text()
for t in ['(evalBody : BodyEvaluationBridge)', '(hcS : Hierarchy 𝚺 1 bodyC)', '(hhS : Hierarchy 𝚺 1 bodyH)', '(hxS : Hierarchy 𝚺 1 bodyX)', '(hyS : Hierarchy 𝚺 1 bodyY)', '(hrS : Hierarchy 𝚺 1 bodyR)', '(htS : Hierarchy 𝚺 1 finalBody)', '(cReplacement evalBody) (hReplacement evalBody)', '(xReplacement evalBody) (yReplacement evalBody)', '(rReplacement evalBody) (tReplacement evalBody)', 'period_wb_of_body_bridge (M := M) bodyEvaluationBridge hcS hhS hxS hyS hrS htS']:
    assert t in s, t
prior=Path(selection['DiophantineConsistency.PellPeriodFullWB']['path']).read_text()
for t in ['(hc : Replacement bodyC boundC) (hh : Replacement bodyH boundH)', '(hx : Replacement bodyX boundX) (hy : Replacement bodyY boundY)', '(hr : Replacement bodyR boundR) (ht : Replacement finalBody boundT)', 'WB M periodDef.val']:
    assert t in prior,t
print(json.dumps({'selection_sha256':sha256((D/'selection.json').read_bytes()).hexdigest(), 'selected_draft_count':len(done), 'topological_order':order, 'direct_frontier':dict(sorted(frontier.items())), 'all_six_hierarchy_facts_assumed':True, 'elaborated':False, 'lean_executed':False},sort_keys=True,indent=2))
