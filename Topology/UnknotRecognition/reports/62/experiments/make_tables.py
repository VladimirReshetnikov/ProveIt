#!/usr/bin/env python3
"""Generate article tables directly from completed benchmark records."""
import json
import re
import bootstrap


def main():
    data = json.loads((bootstrap.ROOT / 'results' / 'benchmark.json').read_text())
    rows = []
    names = {
        'static-coincident-12': 'Coincident, static',
        'static-nested-12': 'Nested, static',
        'static-disjoint-12': 'Disjoint, static',
        'periodic-disjoint-12': 'Disjoint, period 17',
        'reflection-disjoint-12': 'Disjoint, reflection',
        'static-overlap-8': 'Overlapping, static',
        'full-support-3': 'Full support, $r=3$',
        'full-support-4': 'Full support, $r=4$',
    }
    for row in data['summary']:
        if not row['paired_dense']:
            continue
        m = row['medians_seconds']
        rows.append(f"{names[row['name']]} & {row['r']} & {row['support']} & "
                    f"{row['query_counts']['dense']}/{row['query_counts']['sparse']} & "
                    f"{1000*m['dense']:.3f} & {1000*m['sparse']:.3f} & "
                    f"{1000*m['certified']:.3f} & {row['median_paired_dense_over_sparse']:.2f} " + r'\\')
    (bootstrap.ROOT / 'article' / 'table_paired.tex').write_text('\n'.join(rows) + '\n')
    paired_rows = '\n'.join(rows)
    rows = []
    for row in data['summary']:
        if row['paired_dense']:
            continue
        name = row['name'].replace('sparse-only-', '').rsplit('-', 1)[0].capitalize()
        m = row['medians_seconds']
        rows.append(f"{name} & {row['r']} & {row['endpoint_bits']} & {row['support']} & "
                    f"{row['query_counts']['sparse']} & {1000*m['sparse']:.3f} & "
                    f"{1000*m['certified']:.3f} & {row['certificate_json_bytes']:,} " + r'\\')
    (bootstrap.ROOT / 'article' / 'table_scale.tex').write_text('\n'.join(rows) + '\n')
    article = bootstrap.ROOT / 'article' / 'sparse_incidence.tex'
    text = article.read_text()
    for name, content in [('paired', paired_rows), ('scale', '\n'.join(rows))]:
        begin, end = '% BEGIN_GENERATED_' + name.upper(), '% END_GENERATED_' + name.upper()
        block = begin + '\n' + content + '\n' + end
        marker = r'\input{table_' + name + '.tex}'
        if marker in text:
            text = text.replace(marker, block)
        else:
            text = re.sub(re.escape(begin) + '.*?' + re.escape(end),
                          lambda match: block, text, flags=re.S)
    article.write_text(text)



if __name__ == '__main__':
    main()
