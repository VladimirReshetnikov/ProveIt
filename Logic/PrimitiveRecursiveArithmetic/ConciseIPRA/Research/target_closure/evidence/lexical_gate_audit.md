# Audit: exact integer/list JSON by lexical restriction

The intended old predicate is

    j(x) = type(x) is int OR
           (type(x) is list AND all(j(y) for y in x)).

For raw input text r, the proposed replacement first requires

    r.strip('[],-0123456789 \t\r\n') == ''

and then calls Python's standard `json.loads(r)`.

## Universal language argument

`str.strip(A)` returns the empty string exactly when every character of its input belongs to A. If a forbidden character occurs, removing allowed characters from either end cannot remove that character; the remaining string is nonempty.

Among valid JSON texts using this alphabet, the only possible value productions are array and integer number. JSON objects require braces, colons, and quoted keys; strings require quotation marks; Boolean and null values require alphabetic letters. Noninteger JSON numbers require a decimal point or exponent marker. Python's accepted nonstandard NaN and Infinity constants also require letters. All are excluded.

Each parsed scalar is therefore produced by the default integer parser and has exact type int; each array has exact type list. Recursive syntax induction proves j(json.loads(r)). Conversely, if the old json.loads call succeeds and its result satisfies j, the input contains only array, integer, separator, and JSON whitespace characters, so the lexical gate accepts. Default `parse_int`, `parse_float`, and `parse_constant` options must be retained.

This establishes exact acceptance equivalence of the old and new input gates for successfully parsed inputs, abstracting from resource exhaustion. Subsequent exact type checks inside the public validator are redundant because every object reachable from the parsed certificate is already an int or a list.

## Edge cases

- Negative zero parses as integer zero in both versions.
- Leading zero spellings, a bare minus, trailing commas, multiple top-level values, and malformed nesting remain parser rejections.
- Exponents and decimal spellings are rejected by the lexical gate and by old j after parsing to float.
- NaN, Infinity, true, false, null, strings, and objects are rejected, even in unused prefix packets, matching the recursive whole-certificate predicate.
- JSON whitespace is precisely space, tab, CR, LF; the gate admits all four. Non-ASCII whitespace and digits are not added.
- Invalid text decoding and default huge-integer conversion limits can reject before or during parsing in both versions. No resource error counts as acceptance.
- The top-level pop requirement and the kernel's own scope/type invariants remain unchanged.

## Scope caution

This proof changes input validation only. It does not change public numerical-coordinate conventions. Admitting additional raw scalar or arity aliases because they have a sound decoder requires a separate completeness and roundtrip argument; soundness of their denotation is insufficient. In particular, an unbound scalar 1 or 2 can be decoded as zero administratively without the kernel automatically providing a raw proof equating its spelling to literal 0. Preserve the old canonical scalar restriction in this measured refinement.
