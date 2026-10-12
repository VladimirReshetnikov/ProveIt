"""Create an additive patch with package-relative imports for fastunknot."""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]


def main():
    files = sorted((ROOT / 'code').glob('*.py'))
    names = '|'.join(re.escape(path.stem) for path in files)
    output = []
    for path in files:
        value = path.read_text()
        value = re.sub(r'^from fastunknot\.', 'from .', value, flags=re.MULTILINE)
        value = re.sub(r'^from (' + names + r') import ', r'from .\1 import ', value,
                       flags=re.MULTILINE)
        target = 'Topology/UnknotRecognition/fast/fastunknot/' + path.name
        lines = value.splitlines()
        output.extend([f'diff --git a/{target} b/{target}', 'new file mode 100644',
                       '--- /dev/null', f'+++ b/{target}', f'@@ -0,0 +1,{len(lines)} @@'])
        output.extend('+' + line for line in lines)
    result = ROOT / 'integration/additive_extension.patch'
    result.write_text('\n'.join(output) + '\n')
    print(result)


if __name__ == '__main__':
    main()
