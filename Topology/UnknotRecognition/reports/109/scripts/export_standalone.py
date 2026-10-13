"""Inline the generated tables/macros; retain the same article and bibliography."""
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parents[1]
text = (ROOT / 'article.tex').read_text()
def inline(match):
    relative = match[1]
    return '% Inlined ' + relative + '\n' + (ROOT / relative).read_text()
text = re.sub(r'\\input\{(results/[^}]+\.tex)\}', inline, text)
(ROOT / 'article_standalone.tex').write_text(text)
print('Wrote article_standalone.tex')
