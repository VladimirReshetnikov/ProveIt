#!/usr/bin/env python3
"""Remove the specifically audited duplicate from a supplied local README.

Usage: python remove_duplicate_readme.py INPUT_README OUTPUT_README
This never modifies INPUT_README, never accesses a network, and refuses an
unexpected text or a pre-existing output. Review the resulting diff before use.
"""
from pathlib import Path
import re,sys
if len(sys.argv)!=3:
    raise SystemExit(__doc__)
source,dest=map(Path,sys.argv[1:])
if source.resolve()==dest.resolve() or dest.exists():
    raise SystemExit('Refusing to overwrite an existing file or the input.')
text=source.read_text(encoding='utf-8')
pattern=re.compile(r'The complete\s+1,032-input first-letter X family.*?'
                   r'their target membership remains a separate research question\.',re.S)
hits=list(pattern.finditer(text))
normalize=lambda s:' '.join(s.split())
if len(hits)!=2 or normalize(hits[0].group())!=normalize(hits[1].group()):
    raise SystemExit('The two specifically audited matching passages were not found; no change made.')
if text[hits[0].end():hits[1].start()].strip():
    raise SystemExit('Passages are not adjacent; refusing an unreviewed edit.')
start=hits[0].end(); end=hits[1].end()
new=text[:start]+text[end:]
dest.write_text(new,encoding='utf-8')
print(f'Wrote {dest}; removed the second matching passage. Input unchanged.')
