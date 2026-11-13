"""Generate/check the matched Tr control and measure both complete modules.

The control differs only in its equality rule: it removes replace_term,
checks an explicit one-term template, and uses ordinary substitution.
The public syntax, scopes, seven other rules and driver are unchanged.
"""

import ast
import copy
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize

import checker
from test_checker import StripDocstrings


ROOT = Path(__file__).resolve().parent
TR_BRANCH = '''    elif rule == "tr":
        fields(proof, ("rule", "equality", "template", "major", "minor"))
        equality = proof["equality"]
        require(type(equality) is list and len(equality) == 2
                and formula_ok(equality, n), "ill-scoped major equation")
        require(len(goal) == 2, "transport requires an equation")
        template = proof["template"]
        require(term_ok(template, n + 1), "ill-scoped transport template")
        source, target = equality
        result, destination = goal
        require(destination == substitute_term(template, target),
                "transport instance does not match goal")
        verify(n, context, equality, proof["major"])
        minor = [substitute_term(template, source), result]
        verify(n, context, minor, proof["minor"])

'''


def control_source(candidate_source):
    start = candidate_source.index("def replace_term(")
    end = candidate_source.index("def fields(", start)
    source = candidate_source[:start] + candidate_source[end:]
    start = source.index('    elif rule == "brep":\n')
    end = source.index('    elif rule == "qe":\n', start)
    source = source[:start] + TR_BRANCH + source[end:]
    return source.replace("checker for the BRep native calculus.",
                          "checker for the native one-term Tr calculus.", 1)


def measure(source):
    tree = StripDocstrings().visit(ast.parse(source))
    normalized = ast.unparse(tree) + "\n"
    ignored = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE,
               tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER,
               tokenize.COMMENT}
    return {
        "significant_tokens": sum(t.type not in ignored for t in
            tokenize.generate_tokens(io.StringIO(normalized).readline)),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
        "normalized_utf8_bytes": len(normalized.encode("utf-8")),
        "source_sha256": hashlib.sha256(source.encode("utf-8")).hexdigest(),
        "normalized_sha256": hashlib.sha256(normalized.encode("utf-8")).hexdigest(),
    }


def translate_reflexivity_nodes(value):
    """The common-rule fixtures use BRep only in the fixed Refl macro."""
    if type(value) is list:
        return [translate_reflexivity_nodes(item) for item in value]
    if type(value) is not dict:
        return value
    output = {key: translate_reflexivity_nodes(item)
              for key, item in value.items()}
    if value.get("rule") == "brep":
        if value["major"] != {"rule": "i0"} or value["minor"] != {"rule": "i0"}:
            raise AssertionError("unexpected BRep in a common-rule fixture")
        output["rule"] = "tr"
        output["template"] = 0
    return output


def control_reflexivity(term):
    return {"rule": "tr", "equality": [[[], term, 0], term], "template": 0,
            "major": {"rule": "i0"}, "minor": {"rule": "i0"}}


def run():
    source = (ROOT / "checker.py").read_text(encoding="utf-8")
    expected_control = control_source(source)
    control_path = ROOT / "checker_control.py"
    if not control_path.exists():
        control_path.write_text(expected_control, encoding="utf-8")
    if control_path.read_text(encoding="utf-8") != expected_control:
        raise AssertionError("control is not the prescribed local rule replacement")
    import checker_control as control

    common_names = []
    for path in sorted((ROOT / "fixtures" / "positive").glob("*.json")):
        record = json.loads(path.read_text(encoding="utf-8"))
        if record["proof"]["rule"] == "brep":
            continue
        checker.verify(record["n"], record["context"], record["goal"], record["proof"])
        translated = translate_reflexivity_nodes(record["proof"])
        control.verify(record["n"], record["context"], record["goal"], translated)
        common_names.append(path.stem)

    # One Tr congruence certificate. Passive occurrences of the parameter
    # in H(v)=I(v,s;w.s) remain fixed; only the designated hole is filled.
    source_term, target_term, template = 0, [0], [0, 1, 2]
    at_source = checker.substitute_term(template, source_term)
    at_target = checker.substitute_term(template, target_term)
    record = {
        "n": 1, "context": [[source_term, target_term]],
        "goal": [at_source, at_target],
        "proof": {"rule": "tr", "equality": [source_term, target_term],
                  "template": template, "major": {"rule": "hyp", "index": 0},
                  "minor": control_reflexivity(at_source)},
    }
    control.verify(record["n"], record["context"], record["goal"], record["proof"])
    (ROOT / "tr_congruence.json").write_text(
        json.dumps(record, indent=2) + "\n", encoding="utf-8")

    candidate_metrics = measure(source)
    control_metrics = measure(expected_control)
    coordinates = ("significant_tokens", "ast_nodes", "normalized_utf8_bytes")
    result = {
        "python": platform.python_version(),
        "normalization": "recursively strip docstrings; ast.unparse; one final LF",
        "control": "checker_control.py: explicit one-term crossed transport",
        "candidate": "checker.py: backward crossed replacement",
        "same_public_syntax_scope_checks_and_driver": True,
        "only_executable_changes": ["remove replace_term", "replace brep branch by tr branch"],
        "candidate_metrics": candidate_metrics,
        "control_metrics": control_metrics,
        "candidate_minus_control": {
            coordinate: candidate_metrics[coordinate] - control_metrics[coordinate]
            for coordinate in coordinates
        },
        "common_rule_fixtures": common_names,
        "common_rule_fixtures_passed": len(common_names),
        "additional_Tr_congruence_fixture_passed": True,
        "all_passed": True,
        "conclusion": "BRep removes the certificate template but this readable implementation is larger; no size improvement is claimed.",
    }
    (ROOT / "comparison.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    run()
