#!/usr/bin/env python3
"""Read-only lexical audit of the proposed canonical-frame replacement.

Counts are source regions affected, never measured net deletions.  Identifier
references are lexical and may miss automation or include overloaded names.
"""
from pathlib import Path
import argparse, hashlib, json, re, subprocess

def strip_comments(text):
    out = []
    depth = 0
    string = False
    line_comment = False
    i = 0
    while i < len(text):
        c = text[i]
        pair = text[i:i+2]
        if line_comment:
            if c == '\n':
                line_comment = False
                out.append(c)
            else:
                out.append(' ')
            i += 1
        elif depth:
            if pair == '/-':
                depth += 1
                out.extend('  ')
                i += 2
            elif pair == '-/':
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if c == '\n' else ' ')
                i += 1
        elif string:
            out.append(c)
            if c == '\\' and i + 1 < len(text):
                out.append(text[i+1]); i += 2
            else:
                if c == '"': string = False
                i += 1
        elif pair == '--':
            line_comment = True; out.extend('  '); i += 2
        elif pair == '/-':
            depth = 1; out.extend('  '); i += 2
        else:
            if c == '"': string = True
            out.append(c); i += 1
    if depth:
        raise ValueError('Unclosed block comment')
    return ''.join(out)

def counts(lines, stripped, first, last):
    return {'first_line': first, 'last_line': last,
            'physical_lines': last-first+1,
            'nonempty_lines': sum(bool(x.strip()) for x in lines[first-1:last]),
            'noncomment_nonempty_lines': sum(bool(x.strip()) for x in stripped[first-1:last])}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('repo', type=Path)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    root = args.repo / 'Analysis/GeneralizedRiemannHypothesis/Lean/grh/src'
    relative = 'New/Spanning/RemainingTerms/OneRealPlace.lean'
    target = root / relative
    raw = target.read_text()
    lines = raw.splitlines()
    stripped = strip_comments(raw).splitlines()
    files = sorted(root.rglob('*.lean'))
    code = {str(p.relative_to(root)): strip_comments(p.read_text()) for p in files}
    code_lines = {path: txt.splitlines() for path, txt in code.items()}
    decls = []
    decl_rx = re.compile(r'^(?:(?:noncomputable|private|protected)\s+)*(lemma|theorem|def|abbrev|structure)\s+(\S+)')
    for line_number, line in enumerate(stripped, 1):
        m = decl_rx.match(line)
        if not m: continue
        kind, name = m.groups()
        leaf = name.split('.')[-1]
        token = re.compile(r'(?<![\w\'])' + re.escape(leaf) + r'(?![\w\'])')
        hits = []
        for path, txt in code_lines.items():
            if path == relative: continue
            for ln, text in enumerate(txt, 1):
                if token.search(text): hits.append({'file': path, 'line': ln, 'code': text.strip()})
        decls.append({'kind': kind, 'declared_name': name, 'leaf': leaf, 'line': line_number,
                      'external_lexical_occurrences': hits})
    regions = {
        'triangular_structure_construction_and_bounds': (449, 602),
        'coordinates_and_ostrowski_bridge_rewrite': (604, 705),
        'last_column_and_majorant_rewrite': (802, 1006),
        'unchanged_common_vector_and_subframe_minor': (707, 793),
    }
    helper = 'Lib/General/LinearAlgebra/HermitianMatrices.lean'
    hraw = (root/helper).read_text()
    hlines = hraw.splitlines()
    hstrip = strip_comments(hraw).splitlines()
    # These include the lemma's two-line docstring and all of its body.
    helper_count = counts(hlines, hstrip, 71, 99)
    helper_count['name'] = 'New.exists_lowerTriangular_conjTranspose_mul_mul_eq_one'
    helper_count['file'] = helper
    helper_token = 'exists_lowerTriangular_conjTranspose_mul_mul_eq_one'
    helper_count['external_lexical_occurrences'] = [
        {'file': p, 'line': i, 'code': l.strip()}
        for p, txt in code_lines.items() if p != helper
        for i, l in enumerate(txt,1) if helper_token in l
    ]
    affected_names = [name for name in regions if not name.startswith('unchanged')]
    region_counts = {name: counts(lines,stripped,*span) for name,span in regions.items()}
    affected_totals = {key: sum(region_counts[name][key] for name in affected_names)
                       for key in ['physical_lines','nonempty_lines','noncomment_nonempty_lines']}
    affected_totals['declaration_count'] = sum(
        any(regions[name][0] <= d['line'] <= regions[name][1] for name in affected_names)
        for d in decls)
    implementation_regions = {
        'triangular_structure_construction_and_bounds': (449, 602),
        'coordinates_and_ostrowski_bridge_rewrite': (604, 705),
        'last_column_estimates': (802, 916),
        'public_majorant_proof_body_only': (941, 1006),
    }
    implementation_counts = {name: counts(lines,stripped,*span)
                             for name,span in implementation_regions.items()}
    implementation_totals = {key: sum(c[key] for c in implementation_counts.values())
                            for key in ['physical_lines','nonempty_lines','noncomment_nonempty_lines']}
    result = {
        'commit': subprocess.check_output(['git','-C',str(args.repo),'rev-parse','HEAD'],text=True).strip(),
        'source_files_scanned': len(files),
        'target': relative,
        'target_sha256': hashlib.sha256(raw.encode()).hexdigest(),
        'whole_file': counts(lines,stripped,1,len(lines)),
        'regions': region_counts,
        'gross_affected_region_totals': affected_totals,
        'implementation_only_regions': implementation_counts,
        'implementation_only_totals': implementation_totals,
        'direct_importers': [p for p,txt in code.items() if re.search(
            r'^import\s+New\.Spanning\.RemainingTerms\.OneRealPlace\s*$', txt, re.M)],
        'declarations': decls,
        'gram_schmidt_helper': helper_count,
        'caveat': 'Lexical occurrences, not an elaborated Lean dependency graph. Region counts are gross affected source, not net reduction.'
    }
    rendered = json.dumps(result,ensure_ascii=False,indent=2)+'\n'
    if args.output: args.output.write_text(rendered)
    else: print(rendered)

if __name__ == '__main__': main()
