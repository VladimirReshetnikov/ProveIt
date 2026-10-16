import re

def mask_comments(text):
    """Preserve offsets/newlines while hiding nested comments and string text."""
    out = list(text)
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif text.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif in_string:
            if text[i] == '\\' and i + 1 < len(text):
                out[i:i+2] = '  '; i += 2
            elif text[i] == '"':
                out[i] = ' '; in_string = False; i += 1
            else:
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            if j == -1: j = len(text)
            out[i:j] = ' ' * (j-i); i = j
        elif text[i] == '"':
            out[i] = ' '; in_string = True; i += 1
        else:
            i += 1
    assert depth == 0 and not in_string, 'Unclosed comment/string'
    return ''.join(out)

COMMAND = re.compile(
    r'^(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*'
    r'(?P<kind>namespace|section|end|variable|include|omit|theorem|lemma|def|abbrev|structure|inductive|class|instance|set_option|open|attribute|export|run_cmd)\b', re.M)

DECL_KINDS = {'theorem', 'lemma', 'def', 'abbrev', 'structure', 'inductive', 'class', 'instance'}

def declaration_header_end(masked, start, end):
    depth = 0
    i = start
    while i < end:
        char = masked[i]
        if char in '([{⟨': depth += 1
        elif char in ')]}⟩': depth -= 1
        assert depth >= 0, 'Unbalanced declaration header'
        if depth == 0:
            if char == '|' and not masked[masked.rfind('\n', 0, i)+1:i].strip(): return i
            if masked.startswith(':=', i): return i
            if re.match(r'where\b', masked[i:]) and (i == 0 or not masked[i-1].isalnum()): return i
        i += 1
    raise AssertionError('No body delimiter at ' + str(start) + ': ' + masked[start:end])

def parse_declarations(text):
    masked = mask_comments(text)
    commands = list(COMMAND.finditer(masked))
    frames = [{'kind': 'root', 'name': '', 'namespace': '', 'context': []}]
    result = {}
    for index, match in enumerate(commands):
        kind = match['kind']
        end = commands[index+1].start() if index+1 < len(commands) else len(text)
        tail = masked[match.end():end].strip()
        if kind in {'namespace', 'section'}:
            name = tail.split()[0] if tail else ''
            if kind == 'namespace':
                assert name, 'Anonymous namespace'
                parent = frames[-1]['namespace']
                namespace = (parent + '.' if parent else '') + name
            else:
                namespace = frames[-1]['namespace']
            frames.append({'kind': kind, 'name': name, 'namespace': namespace, 'context': []})
        elif kind == 'end':
            name = tail.split()[0] if tail else ''
            assert len(frames) > 1, 'Unmatched end'
            frame = frames.pop()
            assert not name or name == frame['name'], (name, frame)
        elif kind in {'variable', 'include', 'omit'}:
            meaningful_end = match.start() + len(masked[match.start():end].rstrip())
            frames[-1]['context'].append(text[match.start():meaningful_end].strip())
        elif kind in DECL_KINDS:
            found = re.match(r'\s*([^\s:({\[]+)', masked[match.end():end])
            assert found, 'Unnamed declaration unsupported'
            name = found.group(1)
            full_name = frames[-1]['namespace'] + '.' + name
            header_end = declaration_header_end(masked, match.end()+found.end(), end)
            body_end = match.start() + len(masked[match.start():end].rstrip())
            assert full_name not in result, 'Duplicate declaration in file: ' + full_name
            result[full_name] = {
                'kind': kind,
                'header': text[match.start():header_end].rstrip(),
                'block': text[match.start():body_end].rstrip(),
                'context': [c for f in frames for c in f['context']],
                'line': text[:match.start()].count('\n') + 1,
            }
    return result

def declarations(s):
 ds=parse_declarations(s)
 for d in ds.values():
  if d['kind']in('theorem','lemma'):
   m=re.search(r':=\s*by\n',mask_comments(d['block']))
   if m:d['header']=d['block'][:m.start()].rstrip()
 return ds

def proof_lines(d):
 if d['kind']not in('theorem','lemma'):return 0
 tail=d['block'][len(d['header']):];m=re.match(r'\s*:=\s*by\n',mask_comments(tail))
 return len(tail[m.end():].splitlines())if m else 0

def term_lines(d):
    if d['kind'] not in {'theorem','lemma'}:return 0
    tail=mask_comments(d['block'][len(d['header']):]).strip()
    if not tail.startswith(':='):return 0
    term=tail[2:].strip()
    return 0 if re.match(r'by\b',term) else len(term.splitlines())

def imports(text):return re.findall(r'^import\s+(\S+)',mask_comments(text),re.M)
