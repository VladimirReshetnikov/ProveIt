#!/usr/bin/env python3
"""Reproduce the limited lexical source audit. This does not run Lean."""
from pathlib import Path
import argparse
import json
import re
import subprocess


def strip_comments_and_strings(text):
    output = []
    pos = 0
    depth = 0
    in_string = False
    while pos < len(text):
        if depth:
            if text.startswith('/-', pos):
                depth += 1
                pos += 2
            elif text.startswith('-/', pos):
                depth -= 1
                pos += 2
            else:
                if text[pos] == '\n':
                    output.append('\n')
                pos += 1
        elif in_string:
            if text[pos] == '\\':
                pos += 2
            elif text[pos] == '"':
                in_string = False
                pos += 1
            else:
                if text[pos] == '\n':
                    output.append('\n')
                pos += 1
        elif text.startswith('/-', pos):
            depth = 1
            pos += 2
        elif text.startswith('--', pos):
            end = text.find('\n', pos)
            pos = len(text) if end < 0 else end
        elif text[pos] == '"':
            in_string = True
            pos += 1
        else:
            output.append(text[pos])
            pos += 1
    return ''.join(output)


def audit(root):
    result = {
        'commit': subprocess.check_output(
            ['git', 'rev-parse', 'HEAD'], cwd=root, text=True
        ).strip(),
        'scope': 'Static lexical scan only; not a Lean rebuild or independent kernel replay.',
        'editions': {},
    }
    for edition in ['grh', 'grh-compact']:
        files = sorted((root / edition / 'src').rglob('*.lean'))
        tokens = {token: [] for token in [
            'sorry', 'admit', 'axiom', 'unsafe', 'implemented_by', 'native_decide'
        ]}
        lines = 0
        for path in files:
            source = path.read_text()
            lines += len(source.splitlines())
            clean = strip_comments_and_strings(source)
            for token in tokens:
                pattern = r'(?<![\w\u0080-\uffff])' + token + r'(?![\w\u0080-\uffff])'
                for match in re.finditer(pattern, clean):
                    tokens[token].append({
                        'file': str(path.relative_to(root)),
                        'line': clean[:match.start()].count('\n') + 1,
                    })
        result['editions'][edition] = {
            'file_count': len(files), 'lines': lines, 'token_hits': tokens,
        }
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('source_root', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    rendered = json.dumps(audit(args.source_root), indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end='')
