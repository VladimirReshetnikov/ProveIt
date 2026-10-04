#!/usr/bin/env python3
"""Independent read-only Report54 ledger, degree, pin, and PDF review receipts.

This newly authored checker reads the submitted JSON as inert data. It never
imports, runs, or edits any submitted scientific, audit, or release program.
It corroborates the manuscript review; it does not replace the prior independent
equation-by-equation reconstruction of the mathematical specification.
"""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json
import re
import sys

ROOT = Path('/workspace/shared/unrestricted-stabilization-report54-release-20261004')
SCIENCE = Path('/workspace/shared/sandpile-unrestricted-stabilization-20261004')
AUDIT = Path('/workspace/shared/sandpile-unrestricted-stabilization-adversarial-audit-20261004')
HARDNESS = Path('/workspace/shared/sandpile-global-hardness-interface-20261004')
OUT = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

def inventory(roots):
    return {str(p): digest(p) for root in roots for p in sorted(root.rglob('*')) if p.is_file()}

def add(a, b, sign=1):
    out = a.copy()
    for term, coefficient in b.items():
        value = out.get(term, 0) + sign * coefficient
        if value:
            out[term] = value
        elif term in out:
            del out[term]
    return out

def mul(a, b):
    out = {}
    for ta, ca in a.items():
        for tb, cb in b.items():
            term = tuple(sorted(ta + tb))
            value = out.get(term, 0) + ca * cb
            if value:
                out[term] = value
            elif term in out:
                del out[term]
    return out

def degree(poly):
    return max(map(len, poly), default=-1)

def terms_json(poly):
    return [{'variables': list(t), 'coefficient': c} for t,c in sorted(poly.items())]

def main():
    before = inventory([SCIENCE, AUDIT, HARDNESS])
    pins = {
        'article/Report54.tex': '38e0085c8c3e259e8af79819abf720095e7dcecef8b1229263236e83e2b7d219',
        'article/Report54.pdf': 'a214d1ca65baafe0c7ab720fb18ca1790ec17f42e7720064541a47ded6456949',
        'science/evidence/polynomial-dag.json': '8622585bcafaf9b3aee84e12f229beb17a33d27d6f1bf0b6cb6bc956ee4ac759',
        'science/PROOF.md': '1d426f591b2f9cdbf552fcc151515a7c402bb7c4b06a127bae8ab35de88e4579',
        'science/build_stabilization.py': '47c2e5c63ea6eceef26c4bd117ca8a195eb5180e00482f9d9384a7705788fb2c',
        'dependencies/pell-source.lean': '993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a',
        'dependencies/report35-loader.md': '1791518f521a147b014ca7636910b7775df64fcfe799b6fcb5a0261de4f99d34',
        'dependencies/report35-composition.md': '6e5a053e7f599a17ee77c49e3092e041c7ea3e0de62156095fe9ece5e761d60e',
    }
    for rel, expected in pins.items():
        require(digest(ROOT / rel) == expected, 'Pin mismatch: ' + rel)
    data = json.loads((ROOT / 'science/evidence/polynomial-dag.json').read_text())
    gates = data['gates']
    eqs = data['equalities']
    body = data['body_gate_count']
    witnesses = data['witnesses']
    require(len(set(witnesses)) == len(witnesses) == 3262, 'Witness ledger')
    require(len(eqs) == 1897 and len(gates) == 14571 and body == 8881, 'Arity or gate ledger')
    require(len({row[2] for row in eqs}) == len(eqs), 'Duplicate residual label')
    allowed = {'input:' + data['input']} | {'witness:' + name for name in witnesses}
    polys = []
    def poly(ref):
        if ref.startswith('gate:'):
            return polys[int(ref.split(':')[1])]
        if ref.startswith('constant:'):
            n = int(ref.split(':')[1])
            return {(): n} if n else {}
        require(ref in allowed, 'Unknown leaf: ' + ref)
        return {(ref.split(':', 1)[1],): 1}
    for index, row in enumerate(gates):
        require(len(row) == 3 and row[0] in ('+', '-', '*'), 'Invalid binary gate')
        for ref in row[1:]:
            if ref.startswith('gate:'):
                require(0 <= int(ref.split(':')[1]) < index, 'Bad gate reference')
            elif ref.startswith('constant:'):
                int(ref.split(':')[1])
            else:
                require(ref in allowed, 'Undeclared leaf')
        if index < body:
            left, right = poly(row[1]), poly(row[2])
            polys.append(mul(left,right) if row[0] == '*' else add(left,right,1 if row[0] == '+' else -1))
    residuals = {}
    final = {}
    expected_tail = []
    square_refs = []
    for left, right, name in eqs:
        residual = add(poly(left), poly(right), -1)
        residuals[name] = residual
        final = add(final, mul(residual, residual))
        subref = 'gate:' + str(body + len(expected_tail))
        expected_tail.append(['-', left, right])
        square_refs.append('gate:' + str(body + len(expected_tail)))
        expected_tail.append(['*', subref, subref])
    accumulator = square_refs[0]
    for square in square_refs[1:]:
        expected_tail.append(['+', accumulator, square])
        accumulator = 'gate:' + str(body + len(expected_tail) - 1)
    require(gates[body:] == expected_tail and data['output'] == accumulator, 'Exact SOS tail mismatch')
    reached = set()
    pending = [data['output']]
    while pending:
        ref = pending.pop()
        if ref in reached:
            continue
        reached.add(ref)
        if ref.startswith('gate:'):
            pending.extend(gates[int(ref.split(':')[1])][1:])
    require(all('gate:' + str(i) in reached for i in range(len(gates))), 'Dead gate')
    require(allowed <= reached, 'Unused witness or input')
    degree9 = {k: terms_json({t:c for t,c in v.items() if len(t) == 9}) for k,v in residuals.items() if degree(v) == 9}
    expected_monomial = tuple(sorted(['box.tx','box.ty','box.tz','descriptor.d','descriptor.e','descriptor.f','descriptor.p','descriptor.q','descriptor.r']))
    expected_high = [{'variables':list(expected_monomial),'coefficient':-4}]
    require(set(degree9) == {'patch.shift.eq8','patch.shift.eq9','patch.shift.eq11'}, 'Degree-nine labels')
    require(all(v == expected_high for v in degree9.values()), 'Degree-nine coefficients')
    require(max(map(degree,residuals.values())) == 9 and degree(final) == 18, 'Exact degree')
    leading = {t:c for t,c in final.items() if len(t) == 18}
    require(leading == {tuple(sorted(expected_monomial*2)):48}, 'Leading degree-18 form')
    totals = dict(sorted(Counter(row[0] for row in gates).items()))
    bodycounts = dict(sorted(Counter(row[0] for row in gates[:body]).items()))
    soscounts = dict(sorted(Counter(row[0] for row in gates[body:]).items()))
    require(totals == {'*':5734,'+':4997,'-':3840}, 'Total ledger')
    require(bodycounts == {'*':3837,'+':3101,'-':1943}, 'Body ledger')
    require(soscounts == {'*':1897,'+':1896,'-':1897}, 'SOS ledger')
    macrocounts = dict(sorted(Counter(m['kind'] for m in data['macros']).items()))
    require(macrocounts == {'and':6,'geometric':5,'power':117,'spread':6,'stable':2,'subset':28}, 'Macro ledger')
    require(len(data['ports']) == 33, 'Port ledger')
    tex = (ROOT / 'article/Report54.tex').read_text()
    definitions = set(re.findall(r'\\label\{([^}]+)\}',tex))
    used = set(re.findall(r'\\(?:eq)?ref\{([^}]+)\}',tex))
    bib = set(re.findall(r'\\bibitem\{([^}]+)\}',tex))
    cited = {k for group in re.findall(r'\\cite\{([^}]+)\}',tex) for k in group.split(',')}
    require(used <= definitions, 'Undefined manuscript label')
    require(cited <= bib, 'Undefined manuscript citation')
    require(before == inventory([SCIENCE,AUDIT,HARDNESS]), 'Frozen input bytes changed')
    result = {
        'status':'PASS', 'method':'New direct sparse normalization of inert DAG; exact SOS topology and ledger; source pin and TeX reference checks',
        'submitted_programs_executed':False, 'upstream_programs_executed':False,
        'frozen_source_files_preserved':len(before), 'source_and_pdf_pins':pins,
        'witnesses':len(witnesses),'residuals':len(eqs),'gates':len(gates),'body_gates':body,
        'total_counts':totals,'body_counts':bodycounts,'sos_counts':soscounts,
        'macro_counts':macrocounts,'macro_records':len(data['macros']),'ports':len(data['ports']),
        'dead_gates':0,'dead_witnesses':0,'input_live':True,
        'residual_degrees':dict(sorted(Counter(degree(v) for v in residuals.values()).items())),
        'degree_nine_residuals':degree9,'exact_final_degree':degree(final),
        'fully_collected_final_monomials':len(final),'degree_eighteen_homogeneous_part':terms_json(leading),
        'tex_reference_labels':len(used),'tex_citation_keys':len(cited),
        'undefined_tex_references':0,'undefined_tex_citations':0,
        'limits':'Manual manuscript proof review plus direct graph calculation. This does not reprove Pell, rebuild every residual from a second specification, simulate U15, or audit loader hardware.'
    }
    output = Path(sys.argv[1]) if len(sys.argv)>1 else OUT / 'exact-ledger-receipt.json'
    output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True,indent=2))

if __name__ == '__main__':
    main()
