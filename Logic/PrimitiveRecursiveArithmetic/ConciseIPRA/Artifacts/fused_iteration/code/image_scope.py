"""A local substitution-capture obstruction, not a false proof certificate."""
from pathlib import Path
import json

MISSING = object()

def opening(a, t=MISSING, d=0, *, validate=True, floor=0):
    if isinstance(a, list):
        return [opening(b, t, d + 5 - len(a), validate=validate, floor=floor)
                for b in a]
    if type(a) is not int:
        raise ValueError("a required numerical substitution image is missing")
    if floor <= a < d:
        return a
    if d % 2:
        return opening(t, d=3, floor=floor) if validate else t
    return 0

def main():
    template = [[[5, 0, 7], [5, 0, [13]]]]
    bad_image = 11
    captured = opening(template, bad_image, validate=False)
    expected = [[[5, 0, 7], [5, 0, [11]]]]
    assert captured == expected
    zero_instance = opening(template, 0, validate=False)
    assert zero_instance == [[[5, 0, 7], [5, 0, [0]]]]
    rejected = False
    try:
        opening(template, bad_image)
    except ValueError:
        rejected = True
    assert rejected
    report = {"status": "passed", "template": template,
              "unchecked_image": bad_image, "captured_result": captured,
              "zero_instance": zero_instance,
              "original_opener_rejects": rejected,
              "logical_consequence": "exists x (x=Sx)",
              "scope": "Local-rule counterexample; no accepted false certificate claimed"}
    Path(__file__).with_name("image_scope_results.json").write_text(
        json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))

if __name__ == "__main__":
    main()
