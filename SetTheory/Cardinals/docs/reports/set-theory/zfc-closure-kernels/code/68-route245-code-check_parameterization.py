#!/usr/bin/env python3
"""Check that generalized-width symbolic sources change only declared text.

Exact text equality verifies all literal, unary, list, guard, and oracle rules.
Path relocation and the matched source/target padding are the only adaptations.
"""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]


def check():
    if not __debug__:
        raise RuntimeError('Assertions are required; do not use -O.')
    original=ROOT/'reference/context246/sources/prior/prefix_affine.py'
    adapted=ROOT/'code/parametric_prefix_affine.py'
    source=original.read_text()
    assert source.count('40-len(pc)')==1
    expected=source.replace('from collections import Counter\n',
        'from collections import Counter\n\n# Parameterized frame width; all symbolic inference rules below are unchanged.\n# Source: inherited context246/sources/prior/prefix_affine.py.\nPADDING = 40\n')
    expected=expected.replace('40-len(pc)','PADDING-len(pc)')
    expected=expected.replace("    q='96';onleft=False;left=[('b',1)]",
        "    assert type(PADDING) is int and PADDING >= len(pc)\n    q='96';onleft=False;left=[('b',1)]")
    assert adapted.read_text()==expected
    full_original=ROOT/'reference/full_symbolic_original.py'
    full_adapted=ROOT/'code/full_symbolic_parametric.py'
    full=full_original.read_text()
    assert full.count('40-len(pc)')==full.count('40+extra+int(overflow)-len(successor)')==full.count('len(p)<=34')==1
    full=full.replace('ROOT = Path(__file__).resolve().parents[1]',
        'ROOT = Path(__file__).resolve().parents[1]\n# Only the uniform source/target frame padding and its input guard differ.\nPADDING = 64')
    full=full.replace("BASE = ROOT / 'reference/context246'", "BASE = ROOT / 'reference/context246'\nsys.path.insert(0,str(ROOT/'code'))")
    full=full.replace('40-len(pc)','PADDING-len(pc)').replace('40+extra+int(overflow)-len(successor)','PADDING+extra+int(overflow)-len(successor)').replace('len(p)<=34','len(p)<=PADDING')
    full=full.replace("out=dict(status='PASS' if complete else 'PASS_LIMITED',", "out=dict(frame_padding=PADDING,status='PASS' if complete else 'PASS_LIMITED',")
    assert full_adapted.read_text()==full
    original_driver=ROOT/'reference/context246/code/review_affine_source.py'
    driver=original_driver.read_text()
    a=driver.index('def check_sites(')
    b=driver.index('\n\n',driver.index('max_rules=max_rules, rule_counts=dict(rule_counts))',a))
    f=driver[a:b]
    f=f.replace('def check_sites(affine, table, sites):','def check_sites(affine, table, sites, padding):\n    assert type(padding) is int and padding >= max(len(p) for p,op,r in sites)\n    assert affine.PADDING == padding')
    assert f.count('40')==2
    f=f.replace('<= 40','<= padding').replace('constant_gap = 40 +','constant_gap = padding +')
    f=f.replace('return dict(cases=full_path_cases,','return dict(padding=padding, cases=full_path_cases,')
    adapted_driver=ROOT/'code/parametric_affine_driver.py'
    assert adapted_driver.read_text().split('def check_sites(',1)[1]==f.split('def check_sites(',1)[1]+'\n'
    files=[original,adapted,full_original,full_adapted,original_driver,adapted_driver]
    return dict(status='PASS_EXACT_TEXT_EQUALITY',
        adaptations=['Matched source/target frame padding','Input path nonnegativity/depth guard','Portable import path','Padding field in output metadata'],
        inference_rules_changed=False,
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files})


if __name__=='__main__':
    print(json.dumps(check(),indent=2))
