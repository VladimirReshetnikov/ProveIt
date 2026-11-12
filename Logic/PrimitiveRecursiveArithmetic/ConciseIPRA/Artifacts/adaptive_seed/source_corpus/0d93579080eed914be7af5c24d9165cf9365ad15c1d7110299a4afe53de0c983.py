"""Rebuild the matched baseline and remeasure both complete standalone files."""
from pathlib import Path
import json
from audit_kernels import measure

ROOT = Path(__file__).resolve().parent

def main():
    source = (ROOT / 'root_seed_checker.py').read_text()
    first = source.index("    elif rule in ('root', 'seed'):")
    last = source.index("    elif rule == 'intro':", first)
    lines = [
        "    elif rule == 'transport':",
        "        _, source, minor, placeholder, template = proof",
        "        require(variable(placeholder) and placeholder not in scope)",
        "        formula(template, scope | {placeholder})",
        "        equality = infer(source, context, scope)",
        "        require(equality[0] == '=')",
        "        previous = infer(minor, context, scope)",
        "        require(same(previous, substitute(template, placeholder, equality[1])))",
        "        result = substitute(template, placeholder, equality[2])",
    ]
    source = source[:first] + '\n'.join(lines) + '\n' + source[last:]
    source = source.replace("    require(predecessor == 0 or (type(predecessor) is list and predecessor[0] == 'S'))\n", '')
    source = source.replace("    argument = seed if predecessor == 0 else ['I', predecessor, seed, binder, update]", "    argument = ['I', predecessor, seed, binder, update]")
    source = source[source.index('import json'):]
    source = '# Matched scalar Choice-DI baseline: ordinary I0/IS and full formula transport.\n' + source
    (ROOT / 'matched_transport_checker.py').write_text(source)
    rows = [measure(ROOT / name) for name in ('root_seed_checker.py', 'matched_transport_checker.py')]
    (ROOT / 'matched_metrics.json').write_text(json.dumps(rows, indent=2) + '\n')
    for row in rows:
        print(row['file'], row['normalized_tokens'], row['ast_nodes'], row['normalized_bytes'])

if __name__ == '__main__':
    main()
