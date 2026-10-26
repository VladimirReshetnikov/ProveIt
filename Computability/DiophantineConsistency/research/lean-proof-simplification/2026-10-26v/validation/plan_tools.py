#!/usr/bin/env python3
"""Validate an explicit ordered replay plan. Text checks are not Lean checking."""
import argparse, json, re
from pathlib import Path
from static_audit import mask_noncode, PATTERNS
PIN='22e020937caa81d0cb72a4f63071d6c0bcc1eba9'

def inspect_plan(plan, bundle):
    errors=[]; seen={}; outputs=set(); all_expected=set(); records=[]
    if plan.get('commit') != PIN: errors.append('Wrong pinned commit')
    if not plan.get('probes'): errors.append('Empty probe list; refusing vacuous success')
    for p in plan.get('probes',[]):
        source=p.get('source',''); module=p.get('module',''); group=p.get('group','')
        if not re.fullmatch(r'[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*',module): errors.append('Bad module: '+module)
        if not re.fullmatch(r'[A-Za-z_]\w*',group): errors.append('Bad group: '+group)
        if source in seen: errors.append('Duplicate source: '+source)
        output=(group,module)
        if output in outputs: errors.append('Duplicate output module: '+repr(output))
        outputs.add(output)
        for dep in p.get('requires_probes',[]):
            if dep not in seen: errors.append(f'{source}: prerequisite not earlier: {dep}')
            elif seen[dep]['group'] != group: errors.append(f'{source}: prerequisite is in a different isolated output world: {dep}')
        path=(bundle/source).resolve()
        if not path.is_relative_to(bundle.resolve()) or not path.is_file():
            errors.append('Missing or escaping source: '+source); continue
        code=mask_noncode(path.read_text())
        names=re.findall(r'^#print\s+axioms\s+(\S+)\s*$',code,re.M)
        expected=p.get('expected',[])
        if not expected: errors.append(source+': empty expected endpoints')
        if len(set(expected)) != len(expected): errors.append(source+': duplicate expected endpoints')
        if len(set(names)) != len(names): errors.append(source+': duplicate #print axioms targets')
        if set(names) != set(expected): errors.append(source+': source #print targets differ from explicit plan')
        for name in expected:
            if not re.fullmatch(r'DiophantineConsistency(?:\.[A-Za-z_]\w*\'?)+',name): errors.append(source+': not fully qualified: '+name)
            if name in all_expected: errors.append('Duplicate endpoint across probes: '+name)
        all_expected.update(expected)
        # Private copied compatibility helpers need not be separately printed.
        public=re.findall(r'^(?:theorem|lemma)\s+(\w+)',code,re.M)
        missing=set(public)-{n.rsplit('.',1)[-1] for n in expected}
        if missing: errors.append(source+': public theorem(s) without selected audit: '+', '.join(sorted(missing)))
        for kind,pat in PATTERNS.items():
            if re.search(pat,code): errors.append(source+': forbidden lexical token class: '+kind)
        imports=[name for line in re.findall(r'^import\s+([^\n]+)',code,re.M) for name in line.split()]
        records.append(dict(source=source,module=module,group=group,imports=imports,expected=expected,requires_probes=p.get('requires_probes',[])))
        seen[source]=p
    return {'status':'PASS_SOURCE_PLAN_ONLY' if not errors else 'FAIL','errors':errors,'probes':records,'expected_endpoint_count':len(all_expected)}

def main():
    ap=argparse.ArgumentParser(description=__doc__); ap.add_argument('--bundle',type=Path,default=Path(__file__).resolve().parents[1]); ap.add_argument('--tsv',action='store_true');ap.add_argument('--expected',type=Path);ap.add_argument('--prerequisites',type=Path)
    a=ap.parse_args(); r=inspect_plan(json.loads((a.bundle/'validation/replay_plan.json').read_text()),a.bundle)
    if r['errors']: print(json.dumps(r,indent=2));raise SystemExit(1)
    if a.expected: a.expected.write_text('\n'.join(n for p in r['probes'] for n in p['expected'])+'\n')
    if a.prerequisites: a.prerequisites.write_text('\n'.join(sorted({n for p in r['probes'] for n in p['imports']}))+'\n')
    if a.tsv:
        for p in r['probes']: print('\t'.join((p['source'],p['module'],p['group'])))
    else: print(json.dumps(r,indent=2))
if __name__=='__main__': main()
