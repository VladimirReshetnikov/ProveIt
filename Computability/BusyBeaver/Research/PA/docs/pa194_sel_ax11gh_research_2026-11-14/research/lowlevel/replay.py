#!/usr/bin/env python3
"""Replay the recorded finite synthesis searches using only bundled inputs."""
from pathlib import Path
import argparse, hashlib, json, subprocess, tempfile

ROOT=Path(__file__).resolve().parent

def counts(text):
    line=next(x for x in reversed(text.splitlines()) if x.startswith('DONE '))
    s=line.split()
    return {s[i]:float(s[i+1]) if s[i]=='seconds' else int(s[i+1])
            for i in range(1,len(s),2)}

def run(argv):
    p=subprocess.run(list(map(str,argv)),text=True,capture_output=True)
    if p.returncode:
        raise RuntimeError(f'{argv[0]} failed ({p.returncode}):\n{p.stderr}\n{p.stdout}')
    return p

def compare(actual, expected):
    a={k:v for k,v in actual.items() if k!='seconds'}
    e={k:v for k,v in expected.items() if k!='seconds'}
    if a!=e:raise AssertionError({'actual':a,'expected':e})

def replay(out, selected, grammar):
    out.mkdir(parents=True,exist_ok=True)
    data=json.loads((ROOT/'receipts/search_results.json').read_text())
    provenance=json.loads((ROOT/'PROVENANCE.json').read_text())
    assert hashlib.sha256((ROOT/'inputs/pa194.native.tm').read_bytes()).hexdigest()==provenance['primary_native_sha256']
    compiled={}
    def binary(name):
        if name not in compiled:
            target=out/name
            run(['g++','-O3','-std=c++17',ROOT/'code'/(name+'.cpp'),'-o',target])
            compiled[name]=target
        return compiled[name]
    def save(name,p):
        name=name.replace('/','_')
        (out/(name+'.stdout')).write_text(p.stdout)
        (out/(name+'.stderr')).write_text(p.stderr)
    # This positive control requires genuine two-old-step / two-new-step matching.
    p=run([binary('stuttering_merge'),ROOT/'inputs/stutter_positive.tm',1,8,
           ROOT/'inputs/stutter_positive_patterns.tsv',10,4])
    positive=json.loads((ROOT/'receipts/stutter_positive.json').read_text())
    assert positive['required_witness'] in [json.loads(x) for x in p.stdout.splitlines()]
    compare(counts(p.stderr),positive['counts']);save('positive_control',p)
    print('PASS positive two-step control',flush=True)
    done=[]
    for item in data['complete_enumerations']:
        if item['id'] not in selected:continue
        table=ROOT/item['table'];kind=item['kind']
        if kind=='shared':
            argv=[binary('shared_selector_search'),table,ROOT/'inputs/selector_pairs.txt',
                  item['radius'],item['new_bound'],out/'unexpected_shared_hits']
        elif kind=='stuttering':
            argv=[binary('stuttering_merge'),table,item['radius'],item['new_bound'],
                  '/dev/null',74,item['old_bound']]
        else:
            argv=[binary('joint_return_merge'),table,item['radius'],item['new_bound']]
        p=run(argv);actual=counts(p.stderr)
        compare(actual,item['counts']);assert not p.stdout.strip()
        save(item['id'],p);done.append(item['id'])
        print('PASS',item['id'],json.dumps(actual,sort_keys=True),flush=True)
    if grammar:
        for item in data['completed_grammar_searches']:
            if item['kind']=='baseline':
                program='search_occurrence';template='primary.txt'
            else:
                program='search_adaptive_perm'
                template=item['id'].removesuffix('_perm')+'_templates_expanded.txt'
            # An explicit iteration budget replays the same proposal prefix,
            # independent of the wall-clock speed of the current computer.
            p=run([binary(program),ROOT/'inputs/grammar'/template,
                   ROOT/'inputs/grammar/leaf_attrs.txt',out/item['id'],999999,
                   item['random_seed'],item['iterations']])
            actual=counts(p.stdout)
            expected={k:item[k] for k in ('iterations','accepted','hits','best','seconds')}
            compare(actual,expected);save(item['id'],p)
            print('PASS',item['id'],json.dumps(actual,sort_keys=True),flush=True)
    return done

def main():
    if not __debug__:raise SystemExit('Run without Python -O.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--all',action='store_true',help='Replay every completed finite enumeration.')
    ap.add_argument('--job',action='append',default=[],help='Replay one named enumeration; repeat as needed.')
    ap.add_argument('--grammar',action='store_true',help='Also replay all36,325,019 recorded grammar proposals.')
    ap.add_argument('--list',action='store_true',help='List enumeration names and exit.')
    ap.add_argument('--output',type=Path,help='Keep replay outputs here; otherwise use a temporary directory.')
    a=ap.parse_args();data=json.loads((ROOT/'receipts/search_results.json').read_text())
    ids=[x['id'] for x in data['complete_enumerations']]
    if a.list:
        print('\n'.join(ids));return
    selected=set(ids if a.all else a.job or ['joint_primary_k3','stutter_primary_k3_o4','shared_general_k4'])
    if selected-set(ids):raise SystemExit('Unknown job(s): '+', '.join(sorted(selected-set(ids))))
    if a.output:replay(a.output.resolve(),selected,a.grammar)
    else:
        with tempfile.TemporaryDirectory(prefix='pa194-lowlevel-replay-') as td:
            replay(Path(td),selected,a.grammar)

if __name__=='__main__':main()
