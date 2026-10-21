"""Independent bounded source/API metadata receipt; no Lean invocation."""
from pathlib import Path
import hashlib, json, re

base = Path('/tmp/k215-enumperm-simplification')
out = Path(__file__).parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def clean(s):
    result, pos, depth = [], 0, 0
    while pos < len(s):
        if s[pos:pos+2] == '/-': depth += 1; pos += 2
        elif depth and s[pos:pos+2] == '-/': depth -= 1; pos += 2
        elif depth: pos += 1
        elif s[pos:pos+2] == '--':
            end = s.find('\n', pos); pos = len(s) if end == -1 else end
        else: result.append(s[pos]); pos += 1
    assert depth == 0
    return ''.join(result)

def declarations(s):
    s = clean(s)
    matches = list(re.finditer(r'(?m)^(theorem|def|abbrev|structure|inductive) ([\w.\']+)', s))
    rows = {}
    for i, match in enumerate(matches):
        text = s[match.start():matches[i+1].start() if i+1<len(matches) else len(s)]
        text = re.split(r'(?m)^end |^#print ', text)[0]
        rows[match[2]] = (match[1], re.sub(r'\s+', '', text))
    return rows

old = declarations((base/'EnumPerm.before.lean').read_text())
new = declarations((base/'EnumPerm.final.lean').read_text())
changed = []
for name, (kind, text) in old.items():
    assert name in new and kind == new[name][0], name
    if kind == 'theorem':
        assert text.split(':=',1)[0] == new[name][1].split(':=',1)[0], name
        if text != new[name][1]: changed.append(name)
    else: assert text == new[name][1], name
assert set(new)-set(old) == {'step_sound','Contract.continue','cexec_ax_pop'}
final = (base/'EnumPerm.final.lean').read_text().strip()
compiled = (base/'run5/EnumPerm.lean').read_text()
assert compiled.split('#print axioms',1)[0].strip() == final
record = json.loads((base/'run5/result.json').read_text())
assert record['status']=='PASS' and record['exit_code']==0 and not record['timed_out']
assert record['source_sha256']==sha(base/'run5/EnumPerm.lean')
assert record['log_sha256']==sha(base/'run5/compiler.log')
assert (base/'run5/compiler.log').read_bytes() == (base/'run6/compiler.log').read_bytes()
log = (base/'run5/compiler.log').read_text()
assert log.count('depends on axioms: [propext, Classical.choice, Quot.sound]') == 3
assert 'warning:' not in log and 'sorryAx' not in log
files=['EnumPerm.before.lean','EnumPerm.final.lean','source.diff','run5/EnumPerm.lean',
       'run5/result.json','run5/compiler.log','run6/compiler.log']
result={'status':'SOURCE_API_PEER_CLEAN','reviewer':'review_upstream_reflection',
 'files':{str(base/name):sha(base/name) for name in files},
 'findings':[], 'existing_declarations':len(old), 'changed_proofs':changed,
 'argument':[
  'step_sound unifies the four command branches without weakening Inv or the falsity conclusion; successful MP uses the same two invariant proofs.',
  'Contract.continue explicitly propagates either an early halt or the claimed continuation result; gen_contract and both MP block contracts retain their early-halt branches.',
  'cexec_ax_pop uses all nine non-falsity AX entries, then loads the old current code on the tenth pop without testing it; arbitrary prior cache and continuation are preserved.',
  'The MP proof still handles A=1 and B=1 as early halts and retains the two-zero stack cleanup. The zero counter and raw pairing alias behavior are unchanged.'
 ],
 'actual_acknowledgment':'Read the saved run5 source/log/result and matching run6 axiom log. No compiler rerun and no independent transitive-provider or final endpoint audit.',
 'scope':'Full three new helper proofs and seven changed proofs read in their command/invariant/compiler context; all prior statements and executable definitions independently compared.'}
(out/'review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
