#!/usr/bin/env python3
"""Replay 8,391 symbolic decoder cases for the prepared-tape 252-state runtime.

The published symbolic executor is used with its unchanged register-box
contracts. This is a finite executable certificate check, not a Coq proof
or a statement about blank initialization. No blank-run acceleration is used.
"""
from pathlib import Path
import collections
import importlib.util
import json
import sys

ROOT = Path(__file__).resolve().parent
TMTOOLS = ROOT / 'vendor/upstream/ZF/m254/tools/tm'
BASELINE = ROOT / 'vendor/upstream/ZF/m254/machine/zfc_254.tm'

def main():
    source = (TMTOOLS / 'symexec.py').read_text()
    marker = 'paths = json.load'
    assert source.count(marker) == 1
    prefix = source.split(marker, 1)[0]
    old_argv = sys.argv
    sys.path.insert(0, str(TMTOOLS))
    sys.argv = ['symexec.py', str(BASELINE), str(ROOT/'bootstrap'), '40']
    a = {}
    try:
        exec(compile(prefix, str(TMTOOLS/'symexec.py'), 'exec'), a)
    finally:
        sys.argv = old_argv
    spec = importlib.util.spec_from_file_location(
        'public253', ROOT/'vendor/upstream/ZF/m253/tools/generate_candidate.py')
    g = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(g)
    table = g.patched_rows(BASELINE)
    table[49, 1] = (0, 'R', 64)
    table = {key: value for key, value in table.items() if key[0] != 5}
    literal = {}
    for line in (ROOT/'candidate252-runtime.tm').read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,p=line.split()
            literal[int(q),int(b)] = (int(w),d,int(p))
    assert literal == table and len(table) == 504
    a['T'] = {(str(q),b):(w,d,str(p)) for (q,b),(w,d,p) in table.items()}
    paths = json.loads((ROOT/'bootstrap/paths.json').read_text())
    phys = [6,7,0,2,1,8,4,3,5]
    results = collections.Counter()
    failures = []
    for i,(word,op) in enumerate(paths):
        kind,*arg = op.split()
        value = int(arg[0]) if arg else None
        for branch in (['z','p'] if kind == 'CD' else ['-']):
            if kind == 'CI' or (kind == 'CD' and branch == 'p'):
                nextword = a['inc'](word)
            elif kind == 'CD':
                nextword = a['inc'](a['strip']('0',1,word))
            elif kind == 'CC':
                nextword = a['strip']('1',value,word)
            elif kind == 'CB':
                nextword = a['inc'](a['strip']('0',value,word))
            else:
                nextword = ''
            effect = ('inc' if kind == 'CI' else
                      ('dec0' if branch == 'z' else 'dec') if kind == 'CD' else None)
            effects = () if effect is None else ((effect,phys[value]),)
            if nextword is None:
                expected = a['canon']([('b',1)],[('r',0,1,41),('b',1),
                                                     ('box',('plain',)+effects)])
                tag = 'overflow'
            else:
                expected = a['canon']([('b',1)],a['tape_R'](nextword,0,effects))
                tag = 'normal'
            try:
                out = a['run']('96',[('b',1)],a['tape_R'](word,0,()),branch,expected)
                tag = 'halt' if kind == 'CH' and out[0] == 'halt' else out[0]+' '+tag
                results[tag] += 1
            except Exception as exc:
                results['FAIL '+str(exc)] += 1
                if len(failures)<10:
                    failures.append([i,word,op,branch,str(exc)])
    result = {'results':dict(results),'first_failures':failures}
    assert result == {'results':{'ok normal':8387,'halt':1,'ok overflow':3},
                      'first_failures':[]}
    (ROOT/'runtime252_site_check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
