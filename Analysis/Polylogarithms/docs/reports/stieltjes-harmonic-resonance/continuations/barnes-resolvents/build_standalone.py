"""Expand the modular article into a single distributable LaTeX source."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
TARGET = ROOT / 'Barnes_Resolvents_and_Harmonic_Identities.tex'


def expand(path, stack=()):
    path = path.resolve()
    if path in stack:
        raise ValueError('Cyclic LaTeX input: '+str(path))
    text = path.read_text(encoding='utf-8')
    def replace(match):
        rel = match.group(1)
        child = ROOT / rel
        if not child.suffix:
            child = child.with_suffix('.tex')
        if not child.resolve().is_relative_to(ROOT):
            raise ValueError('Input escapes package root: '+rel)
        return '\n% BEGIN '+rel+'\n'+expand(child,stack+(path,))+'\n% END '+rel+'\n'
    return re.sub(r'\\input\{([^}]+)\}', replace, text)


if __name__ == '__main__':
    TARGET.write_text('% Generated from article.tex by build_standalone.py.\n'
                      '% Edit the modular source and regenerate this file.\n'
                      +expand(ROOT/'article.tex'),encoding='utf-8')
    print(TARGET.name)
