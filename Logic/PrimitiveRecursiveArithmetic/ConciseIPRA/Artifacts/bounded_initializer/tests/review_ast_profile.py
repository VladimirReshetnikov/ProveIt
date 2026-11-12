"""Finite review of an explicitly CPython-qualified ancillary AST profile."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize
import zlib

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
CANDIDATE = PACKAGE / 'code/checker_ast.py'
PRIMARY = PACKAGE / 'code/checker.py'
BASELINE = PACKAGE / 'reference/current_ast.py'


def metrics(path):
    raw = path.read_bytes()
    tree = ast.parse(raw.decode())
    normalized = (ast.unparse(tree) + '\n').encode()
    ignored = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
               tokenize.DEDENT, tokenize.COMMENT, tokenize.ENDMARKER}
    return dict(raw_bytes=len(raw), normalized_bytes=len(normalized),
                normalized_tokens=sum(t.type not in ignored for t in
                    tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
                ast_nodes=len(list(ast.walk(tree))),
                gzip9_raw_bytes=len(gzip.compress(raw, compresslevel=9, mtime=0)),
                gzip9_normalized_bytes=len(gzip.compress(normalized, compresslevel=9, mtime=0)),
                sha256=hashlib.sha256(raw).hexdigest())


def run(path, raw, optimized):
    p = subprocess.run([sys.executable] + (['-O'] if optimized else []) + [str(path)],
                       input=raw, text=True, capture_output=True, timeout=15)
    return dict(accepted=p.returncode == 0 and p.stdout == 'ACCEPT\n',
                exit_status=p.returncode, stdout=p.stdout)


def i0_seed(seed):
    return [[None, 0, seed, 0], [[0, seed, 0], seed]]


def main():
    rows = []
    for case in json.loads((PACKAGE / 'tests/composition_cases.json').read_text()):
        for optimized in (False, True):
            got = run(CANDIDATE, json.dumps(case['packet']), optimized)
            rows.append(dict(category='canonical_composition', case=case['name'],
                             checker='candidate', optimized=optimized,
                             expected=case['accept'], **got))
    raw_rejections = {
        'empty_input': '', 'invalid_json': '{', 'null_top': 'null',
        'true_top': 'true', 'false_top': 'false', 'zero_top': '0',
        'positive_number_top': '3', 'string_top': '"bad"',
        'object_top': '{}', 'empty_key_object_top': '{"":0}',
        'null_goal': '[null]', 'empty_proof': '[]', 'nonempty_string_goal': '["bad"]',
        'nonempty_string_seed': json.dumps(i0_seed('x')),
        'nonempty_key_object_seed': json.dumps(i0_seed({'x': 0})),
        'null_seed': json.dumps(i0_seed(None)),
        'canonical_false_after_zero_supply': json.dumps([[None, 0, 0, 0], [0, [0]]]),
        'future_parameter': json.dumps([[-1, -1]]),
    }
    for label, raw in raw_rejections.items():
        for path, profile in ((CANDIDATE, 'candidate'), (PRIMARY, 'primary')):
            for optimized in (False, True):
                rows.append(dict(category='rejection_control', case=label, checker=profile,
                                 optimized=optimized, expected=False, **run(path, raw, optimized)))
    # Accepted iterable aliases are characterized, not treated as errors.
    aliases = {
        'empty_string_as_zero_seed': (i0_seed(''), i0_seed([])),
        'empty_dict_as_zero_seed': (i0_seed({}), i0_seed([])),
        'empty_key_dict_as_one_seed': (i0_seed({'': {'ignored': [False, None]}}), i0_seed([[]])),
        'empty_string_as_truth_formula': ([[0, 0, 0, [0, 0]], ''], [[0, 0, 0, [0, 0]], []]),
        'empty_key_dict_as_paired_truth': ([[0, 0, 0, 0], {'': 99}], [[0, 0, 0, 0], [[]]]),
    }
    for label, (packet, canonical_packet) in aliases.items():
        for optimized in (False, True):
            for path, profile, data, expected in (
                    (CANDIDATE, 'candidate_alias', packet, True),
                    (PRIMARY, 'primary_alias', packet, False),
                    (PRIMARY, 'primary_canonical_decode', canonical_packet, True)):
                rows.append(dict(category='explicit_alias_control', case=label,
                                 checker=profile, optimized=optimized, expected=expected,
                                 **run(path, json.dumps(data), optimized)))
    # The unchanged baseline has the same top-level runtime verdict contract.
    for label in ('invalid_json', 'null_top', 'string_top', 'object_top'):
        for optimized in (False, True):
            rows.append(dict(category='baseline_public_contract', case=label,
                             checker='baseline_ast', optimized=optimized, expected=False,
                             **run(BASELINE, raw_rejections[label], optimized)))
    failures = [r for r in rows if r['accepted'] != r['expected']]
    result = dict(
        decision='Justified only as an explicitly ancillary, CPython-runtime-qualified profile.',
        python=platform.python_version(), implementation=platform.python_implementation(),
        default_recursion_limit=sys.getrecursionlimit(), zlib_runtime=zlib.ZLIB_RUNTIME_VERSION,
        candidate=metrics(CANDIDATE), baseline_ast=metrics(BASELINE),
        public_contract='Accept iff process exits zero and prints exactly ACCEPT plus newline; other outcomes reject.',
        initialization_review=[
            'The default expression d=(k:=0) executes once at function definition and creates global integer k=0.',
            'The stored default d remains zero after global k changes.',
            'The module-level q walrus assigns the bound pop method before its immediate call and before c reads q.',
            'There is no assert or optimization-sensitive branch in the trusted program.'
        ],
        raw_decoder_review=[
            'On canonical list/numeric inputs, the opener computes the same opening as the primary profile whenever evaluation completes.',
            'A list-child exception cannot turn a list into an atomic parameter: the fallback k<=list comparison raises TypeError.',
            'Empty strings and empty dictionaries traverse to []; a one-key dictionary with empty key traverses to [[]], independently of its value.',
            'These accepted aliases have respectively the zero/truth and successor-zero/paired-truth meanings according to numerical/formula position.',
            'Any nonempty string recurses into one-character strings until the finite CPython recursion limit rejects it.',
            'Any dictionary with a nonempty key similarly rejects; dictionary values are ignored by iterable traversal.',
            'The arity law, exact introduction guard, transport guard, computation generation, scope floor, and public verdict are unchanged from the reviewed composition.'
        ],
        qualification=[
            'This is not a structurally terminating parser over all finite JSON in an ideal unbounded-stack interpreter.',
            'The finite CPython resource qualification is the same qualification already present in the actual baseline AST leader.',
            'The primary explicit-list checker remains the preferred transparent implementation.',
            'Improved family coordinate minima do not imply one checker attaining all minima, an absolute lower bound, or a size result for the new B+equality arithmetic theory.'
        ],
        executions=len(rows), failures=failures, rows=rows)
    (PACKAGE / 'evidence/ast_profile_review.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('decision', 'candidate', 'baseline_ast', 'executions', 'failures')}, indent=2))
    return bool(failures)


if __name__ == '__main__':
    raise SystemExit(main())
