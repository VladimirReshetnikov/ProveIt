"""Replay the retained, untrusted producer on the two legacy source proofs."""
import importlib.util
import json
from pathlib import Path
from transduce import stream_to_array

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('compile_stream', ROOT/'reference/compile_stream.py')
compiler = importlib.util.module_from_spec(spec)
spec.loader.exec_module(compiler)
receipts = json.loads((ROOT/'reference/regeneration.json').read_text())
for receipt in receipts:
    rows = list(reversed(json.loads((ROOT/receipt['source']).read_text())))
    tree, before = compiler.parse_old(rows)
    result, after = compiler.compile_tree(tree, receipt['profile'] == 'global')
    text = ''.join(json.dumps(row, separators=(',', ':'))+'\n' for row in result)
    target = ROOT/receipt['target']
    if (text != target.read_text() or before != receipt['before_rule_counts']
            or after != receipt['after_rule_counts']):
        raise ValueError('Producer does not reproduce '+receipt['target'])
    if stream_to_array(text) != json.loads(target.with_suffix('.json').read_text()):
        raise ValueError('Wrong outer framing for '+receipt['target'])
print('Four compiled fixtures reproduced exactly.')
