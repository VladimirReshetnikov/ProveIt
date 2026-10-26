#!/usr/bin/env python3
"""Independently pack/decode a decimal reverse-discovery seed and all fixed ports."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
ALPHABET = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
MASK = (1 << 636) - 1
SEED_MARKER = "\\begingroup\\fontsize{7.7}{8.2}\\selectfont\\ttfamily\n"
INERT_SOURCE = ROOT / "con-zfc-diophantine-forms/183-pell-carrier65"
ARCHIVE_PROVENANCE = {
    "historical_path": "docs/incoming/ConZFC_Pell_Carrier65_2026-10-25.zip",
    "git_commit_containing_archive": "636ac9c003",
    "historical_archive_sha256": "759b713ab7d3853f4fbd687439f25bada1a824e6b71da7dc0dec0516fca6e514",
    "scope": "Historical provenance only; this auditor authenticates the two byte-identical placed text files below."}
MEMBERS = {
    "proofs/SEED_PROOF.md": "c709c60d1b4e3ab504cb1cf1b3c9385cb95b7a364e1b08eabdc5f0dab1f60634",
    "equation.tex": "9e72ea21099e68bb095e3651c94c2725493f92c3aafc9d76c0ce7d914ee56582"}
PAGE = ROOT / "candidates/one-page-compact66-radix55/equation.tex"
PAGE_SHA = "440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff"
DECODER = ROOT / "research/complemented47-controller-independent/certify.py"
DECODER_SHA = "318665c36d7600a99dbddbacca11ef9a2d30f65e04a761efe25d1f3653e662ed"
OLD_DECIMAL = ROOT / "candidates/one-page-decimal-carrier65-2953/DECIMAL_INTEGER.txt"
OLD_DECIMAL_SHA = "bb8a7c133fe5baafbb41a8b7c1cbadce613e4dc8e79b6866313254dd07bea514"
LAYOUTS = {
    "current2953": {"directory": "scaled-clause-independent", "A": 1005, "C": 1945, "L": 2953,
                    "script": "bebbdc8e5fb70a41e84df0b7378fec09094ff5a571929ab8b113831e8c971e05",
                    "proof": "602b9560017f52835d36de8c1969ec8348381c8dae31876cb86905c5de2cdebe",
                    "receipt": "957faf013a17c2e8e04c03be166d903263d2aadaccac604d31f0791e005776ed",
                    "raw_bytes": 69449},
    "reversed2521": {"directory": "reversed-selector-independent", "A": 1004, "C": 1515, "L": 2521,
                     "script": "c01832bbf7a3e356e46241959ac10ecb474208fff749ba6ac539841bcd50fb4f",
                     "proof": "81e9dc739834d385a0134b23cdb6744ad7df2228af05a3ad66956fb17cdb28e8",
                     "receipt": "e778823a2ff489789db769189e6e217c8e8d1db955b15232eddd8d473b3e36ed",
                     "raw_bytes": 59297}}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def pinned(path, digest):
    raw = path.read_bytes()
    require(sha(raw) == digest, "Exact source binding: " + str(path.relative_to(REPO)))
    return raw


def seed_from_page(raw, count):
    text = raw.decode("utf-8")
    require(text.count(SEED_MARKER) == 1, "Unique exact seed group")
    seed = text.split(SEED_MARKER, 1)[1].split("\\endgroup", 1)[0]
    seed = seed.replace("\\par", "").replace("\n", "")
    require(len(seed) == count and all(c in ALPHABET for c in seed), "Entire base62 seed group")
    value = 0
    for char in seed:
        value = 62 * value + ALPHABET.index(char)
    return seed, value


def decimal(raw):
    require(raw.endswith(b"\n") and raw.count(b"\n") == 1, "Exactly one terminal decimal newline")
    text = raw[:-1].decode("ascii")
    require(text and text[0] in "123456789" and all(c in "0123456789" for c in text),
            "Entire positive canonical decimal numeral")
    return int(text)


def old_decode(value):
    n, targets, exceptions = value & MASK, (value >> 636) % (1 << 1675), value >> 2311
    actions, sigma, tau = [], 0, 0
    for q in range(215):
        mark = (n >> (430 + q)) & 1
        flags = 14 + mark * (((exceptions >> (4 * tau)) & 15) - 14)
        tau += mark
        for b in (0, 1):
            j = 2 * q + b
            fresh = (n >> j) & 1
            target = fresh * (sigma + 1) + (1 - fresh) * ((targets // 216 ** (j - sigma)) % 216)
            actions.append((target, (flags >> (2 * b)) & 1, (flags >> (2 * b + 1)) & 1))
            sigma += fresh
    require(sigma == 214 and tau == 71, "Exact old discovery/exception populations")
    return actions, n, targets, exceptions


def pack_from_actions(actions):
    require(len(actions) == 430, "Complete old action count")
    sigma, old_targets, old_place, T, P = 0, 0, 1, 0, 1
    discoveries, trace = [], []
    for j, (target, write, direction) in enumerate(actions):
        require(0 <= target <= 215 and write in (0, 1) and direction in (0, 1), "Action domain")
        fresh = int(target != 215 and target == sigma + 1)
        require(fresh or target <= sigma or target == 215, "Discovery ordering from actual old target")
        radix = (sigma + 2) ** (1 - fresh)
        digit = 0 if fresh else sigma + 1 if target == 215 else sigma - target
        require(0 <= digit < radix, "Actual mixed-radix digit bound")
        trace.append({"action": j, "sigma": sigma, "fresh": fresh, "radix": radix,
                      "digit": digit, "target": target})
        T += digit * P
        P *= radix
        if not fresh:
            old_targets += target * old_place
            old_place *= 216
        discoveries.append(fresh)
        sigma += fresh
    flags = [actions[2*q][1] + 2*actions[2*q][2] + 4*actions[2*q+1][1] + 8*actions[2*q+1][2]
             for q in range(215)]
    marks = [int(flag != 14) for flag in flags]
    E, tau = 0, 0
    for flag, mark in zip(flags, marks):
        if mark:
            E += flag << (4 * tau)
            tau += 1
    N = sum(bit << j for j, bit in enumerate(discoveries))
    N += sum(mark << (430 + q) for q, mark in enumerate(marks))
    require(sigma == 214 and tau == 71 and N <= MASK and old_targets < 1 << 1675,
            "Exact full original field bounds and populations")
    require(0 <= T < P, "Whole mixed target field strictly below prefix product")
    return {"A": N + (T + P * E) * (1 << 636), "N": N, "E": E, "P": P, "T": T,
            "old_targets": old_targets, "discoveries": discoveries, "flags": flags, "marks": marks,
            "trace": trace}


def new_decode(value, streaming=False, outer_modulo=True):
    n, q = value & MASK, value >> 636
    discoveries = [(n >> j) & 1 for j in range(430)]
    marks = [(n >> (430 + j)) & 1 for j in range(215)]
    sigmas, prefixes, radices = [0], [1], []
    for fresh in discoveries:
        radices.append((sigmas[-1] + 2) ** (1 - fresh))
        prefixes.append(prefixes[-1] * radices[-1])
        sigmas.append(sigmas[-1] + fresh)
    if streaming:
        residual, digits = q, []
        for radix in radices:
            residual, digit = divmod(residual, radix)
            digits.append(digit)
        exceptions = residual
    else:
        digits = [(q // prefixes[j]) % radices[j] for j in range(430)]
        exceptions = q // prefixes[-1]
    flags, tau, residual = [], 0, exceptions
    for mark in marks:
        if streaming:
            if mark:
                residual, flag = divmod(residual, 16)
            else:
                flag = 14
        else:
            flag = 14 + mark * (((exceptions // 16 ** tau) % 16) - 14)
        flags.append(flag)
        tau += mark
    actions = []
    for j, digit in enumerate(digits):
        target = sigmas[j + 1] - digit
        if outer_modulo:
            target %= 216
        b, flag = j % 2, flags[j // 2]
        actions.append((target, (flag >> (2*b)) & 1, (flag >> (2*b+1)) & 1))
    require(sigmas[-1] == 214 and tau == 71, "New discovery and exception populations")
    require(exceptions < 16 ** tau, "No unconsumed exceptional nibbles")
    require(not streaming or residual == 0, "Streaming flag quotient consumed exactly")
    require(all((flag != 14) == bool(mark) for flag, mark in zip(flags, marks)),
            "Exception marks reproduce exactly the nondefault flags")
    return {"actions": actions, "discoveries": discoveries, "marks": marks,
            "flags": flags, "E": exceptions, "digits": digits, "sigmas": sigmas}


def admissible_tiles(actions):
    states = [{u for u, _, direction in actions if direction == d} for d in (0, 1)]
    rank = {(d, q): 205 - 199*d + sum(p < q for p in states[d]) for d in (0, 1) for q in states[d]}
    table = {}

    def put(index, tile):
        require(index not in table, "No duplicate direct admissible tile index")
        table[index] = tile

    put(0, (2, 435, 3, 1))
    for j, (u, v, d) in enumerate(actions):
        put(j + 1, ((1-d)*rank.get((0, u), 0), j+2, d*rank.get((1, u), 0), v))
    for a in (0, 1):
        for b in (0, 1):
            put(433-2*a+b, (0, 432*a+b, 0, 432*a+b))
    for d in (0, 1):
        for q in sorted(states[d]):
            r = rank[d, q]
            for b in (0, 1):
                put(423+2*r+b, (d*r, b, (1-d)*r, 2*q+b+2))
    for a in (0, 1):
        for b in (0, 1):
            put(923+2*a+b, (0, 432*a+b, 0, 438))
    for index, tile in ((927, (2, 434, 2, 0)), (928, (3, 436, 4, 4)), (929, (4, 436, 4, 0))):
        put(index, tile)
    for t in (434, 435, 436):
        put(496+t, (1, 438, 1, t))
    for a in range(3):
        for b in range(3):
            put(933+3*a+b, (a*a, 437, b, 437))
    require(set(table) == set(range(942)) and len(set(table.values())) == 942,
            "Whole direct table has unique complete index and tuple coverage")
    return [table[j] for j in range(942)]


def coefficients(tiles, anchor):
    c = [0] * 3297
    for j, (west, north, east, south) in enumerate(tiles):
        c[j] = 2 * (1 + 1024*(1 + west + 256*north + 131072*east + 33554432*south))
    for start, bit, count in ((942, 35, 9), (960, 18, 9), (969, 27, 8), (978, 10, 8)):
        for j in range(count):
            require(c[start+j] == 0, "Direct selector and label slots are disjoint")
            c[start+j] = 2 << (bit+j)
    support = set(range(951)) | set(range(960, 986)) | {anchor}
    require(len(support) == 978 and sum(bool(v) for v in c) == 976
            and c[anchor] == c[977] == 0, "Full physical support retains both zero-weight controls")
    return c, support


def constants(c, spec):
    power = lambda e: 1 << (47*e)
    G = lambda count: sum(power(j) for j in range(count))
    a, center, length = spec["A"], spec["C"], spec["L"]
    beta = power(length) - 1
    dc = power(18) + power(a) + sum(value*power(center-e) for e, value in enumerate(c) if value)
    core = power(960)*G(9) + power(987)*G(8) + power(a)
    padding_origin = 4*G(917) if length == 2953 else 8*G(917)-4
    whole = {"beta": beta, "K": dc + power(length+9),
             "MC": beta-G(951)-power(960)*G(26)-power(a),
             "MF_source": beta+padding_origin+((1 << 45)-4)*power(center)+core}
    return whole, dc


def port_records(whole):
    records = {}
    for name, value in whole.items():
        raw = value.to_bytes((value.bit_length()+7)//8, "big")
        records[name] = {"bits": value.bit_length(), "bytes": len(raw), "sha256": sha(raw)}
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    seed, old_integer = seed_from_page(pinned(PAGE, PAGE_SHA), 436)
    pinned(DECODER, DECODER_SHA)
    old_decimal = pinned(OLD_DECIMAL, OLD_DECIMAL_SHA)
    require(decimal(old_decimal) == old_integer, "Complete old decimal and old base62 integers agree")
    actions, old_n, old_targets, old_e = old_decode(old_integer)
    packed = pack_from_actions(actions)
    require(packed["N"] == old_n and packed["E"] == old_e and packed["old_targets"] == old_targets,
            "Independent complete discovery mask, flags and original target stream reconstruction")
    require(old_integer == packed["N"] + (packed["old_targets"] << 636) + (packed["E"] << 2311),
            "Whole old integer independently reconstructed from every action")
    new_decimal = (str(packed["A"]) + "\n").encode("ascii")
    require(decimal(new_decimal) == packed["A"] and len(old_decimal)-1 == 781 and len(new_decimal)-1 == 715,
            "Whole canonical old781/new715 decimal numerals")
    prefix = new_decode(decimal(new_decimal))
    stream = new_decode(decimal(new_decimal), streaming=True)
    require(prefix == stream and prefix["actions"] == actions,
            "Every result of prefix division and successive divmod equals all430 old actions")
    for field in ("discoveries", "marks", "flags", "E"):
        require(prefix[field] == packed[field], "Independent reconstructed field: " + field)
    require(prefix["digits"] == [row["digit"] for row in packed["trace"]], "All430 mixed digits recovered")

    # Upstream placed these exact archive members in the numbered forms tree.
    # Authenticate/read only text. No submitted Python or other executable is used.
    member_raw = {}
    for name, digest in MEMBERS.items():
        member_raw[name] = pinned(INERT_SOURCE / name, digest)
    archive_seed, archive_integer = seed_from_page(member_raw["equation.tex"], 399)
    require(archive_integer == packed["A"], "Inert399 base62 literal cross-check after independent action re-encoding")

    halt_rows = [row for row in packed["trace"] if row["target"] == 215]
    require(len(halt_rows) == 1 and halt_rows[0] ==
            {"action": 125, "sigma": 80, "fresh": 0, "radix": 82, "digit": 81, "target": 215},
            "Exact actual early halt and reverse distance")
    bad_halt = new_decode(packed["A"], outer_modulo=False)["actions"]
    require([j for j in range(430) if bad_halt[j] != actions[j]] == [125]
            and bad_halt[125][0] == -1, "Actual outer-modulo omission changes exactly halt125")
    negatives = {}
    text = new_decimal[:-1].decode("ascii")
    for label, position in (("first", 0), ("middle", len(text)//2), ("last", len(text)-1)):
        replacement = "1" if text[position] != "1" else "2"
        mutant = text[:position] + replacement + text[position+1:]
        value = decimal((mutant+"\n").encode("ascii"))
        require(value != packed["A"], "Actual decimal digit changed")
        try:
            decoded = new_decode(value)["actions"]
        except ValueError as error:
            outcome = {"rejection": "decoder invariant", "detail": str(error)}
        else:
            differences = [j for j in range(430) if decoded[j] != actions[j]]
            require(differences, "Actual decimal mutation changes the decoded action list")
            j = differences[0]
            outcome = {"rejection": "action mismatch", "first_action": j,
                       "expected": actions[j], "actual": decoded[j], "changed_action_count": len(differences)}
        negatives[label] = {"position": position, "old_digit": text[position], "new_digit": replacement,
                            "mutated_decimal_sha256": sha((mutant+"\n").encode("ascii")), **outcome}

    old_tiles = admissible_tiles(actions)
    new_tiles = admissible_tiles(prefix["actions"])
    require(old_tiles == new_tiles, "Entire independent942 tile table is unchanged")
    layout_records, full_layouts = {}, {}
    for label, spec in LAYOUTS.items():
        base = ROOT / "research" / spec["directory"]
        script = base / "certify.py"
        pinned(script, spec["script"])
        pinned(base / "PROOF.md", spec["proof"])
        reference_receipt = json.loads(pinned(base / "certificate.json", spec["receipt"]))
        module_spec = importlib.util.spec_from_file_location("frozen_seed_reference_" + label, script)
        require(module_spec is not None and module_spec.loader is not None, "Pinned repository import specification")
        reference = importlib.util.module_from_spec(module_spec)
        module_spec.loader.exec_module(reference)
        _, ref_seed, ref_actions, ref_tiles, ref_c, ref_support = reference.model()
        require(ref_seed == seed and ref_actions == actions, "Exact authenticated old source actions")
        reorder = lambda tiles: tiles if label == "current2953" else tiles[:1] + list(reversed(tiles[1:]))
        before_tiles, after_tiles = reorder(old_tiles), reorder(new_tiles)
        require(before_tiles == after_tiles == ref_tiles, "All942 physical tiles match the complete frozen layout")
        before_c, before_support = coefficients(before_tiles, spec["A"])
        after_c, after_support = coefficients(after_tiles, spec["A"])
        require(before_c == after_c == ref_c and before_support == after_support == ref_support,
                "Every3297 coefficient and all978 physical positions agree")
        before_whole, before_dc = constants(before_c, spec)
        after_whole, after_dc = constants(after_c, spec)
        ref_whole, ref_dc = reference.constants(ref_c, ref_support)
        require(before_whole == after_whole == ref_whole and before_dc == after_dc == ref_dc,
                "Allfour whole integers and DC compare equal, not merely their hashes")
        ports = port_records(after_whole)
        require(ports == reference_receipt["constant_ports"] and sum(row["bytes"] for row in ports.values()) == spec["raw_bytes"],
                "Entire pinned receipt port hashes and unchanged raw-byte count")
        full_layouts[label] = {"tiles": after_tiles, "coefficients": after_c, "physical_support": sorted(after_support)}
        layout_records[label] = {"A": spec["A"], "C": spec["C"], "L": spec["L"],
                                 "constant_ports": ports, "raw_bytes": spec["raw_bytes"],
                                 "tiles_sha256": sha(encoded(after_tiles)), "coefficients_sha256": sha(encoded(after_c)),
                                 "physical_support_sha256": sha(encoded(sorted(after_support))),
                                 "all942_tiles_equal": True, "all3297_coefficients_equal": True,
                                 "all_four_whole_integers_equal": True, "whole_DC_equal": True}

    complete = {"actions": actions, "discovery_trace": packed["trace"], "flags": packed["flags"],
                "marks": packed["marks"], "layouts": full_layouts}
    files = {"OLD_DECIMAL_INTEGER.txt": old_decimal, "DECIMAL_INTEGER.txt": new_decimal,
             "ARCHIVE_BASE62_CROSSCHECK.txt": (archive_seed+"\n").encode("ascii"), "DATA.json": encoded(complete)}
    data = {
        "schema": "reverse_discovery_decimal_seed_exact_identity_v1",
        "script_sha256": sha(Path(__file__).read_bytes()), "proof_sha256": sha((HERE / "PROOF.md").read_bytes()),
        "sources": {"old_page_sha256": PAGE_SHA, "old_decoder_sha256": DECODER_SHA,
                    "old_decimal_sha256": OLD_DECIMAL_SHA, "archive_provenance": ARCHIVE_PROVENANCE,
                    "inert_source_directory": str(INERT_SOURCE.relative_to(REPO)),
                    "inert_text_files": MEMBERS, "frozen_layouts": LAYOUTS},
        "numerals": {"old_decimal_digits": len(old_decimal)-1, "new_decimal_digits": len(new_decimal)-1,
                     "saved_decimal_digits": len(old_decimal)-len(new_decimal), "old_bits": old_integer.bit_length(),
                     "new_bits": packed["A"].bit_length(), "old_base62_characters": len(seed),
                     "archive_base62_characters": len(archive_seed)},
        "packing": {"discovery_count": sum(packed["discoveries"]), "exception_nibbles": sum(packed["marks"]),
                    "N": str(packed["N"]), "E": str(packed["E"]), "T": str(packed["T"]), "P430": str(packed["P"]),
                    "P430_bits": packed["P"].bit_length(), "unchanged_entire636bit_mask": True,
                    "unchanged_entire_exception_field": True, "entire_old_integer_reencoded": True,
                    "prefix_and_streaming_routes_agree": True, "all430_actions_equal": True,
                    "actions_sha256": sha(encoded(actions))},
        "halt_modulo_negative": {**halt_rows[0], "without_outer_modulo_target": -1, "changed_actions": [125]},
        "decimal_mutation_negatives": negatives, "layouts": layout_records,
        "artifacts": {name: {"bytes": len(raw), "sha256": sha(raw)} for name, raw in files.items()},
        "scope": "Finite recipe identity only: both specialized polynomials and all ports unchanged. No complete-page size claim; no archive code executed."
    }
    require(data["numerals"]["new_bits"] == 2373 and data["numerals"]["old_bits"] == 2594,
            "Exact new and old numeral bit lengths")
    receipt = encoded(data)
    files["CERTIFICATE.json"] = receipt
    for name, raw in files.items():
        if args.write:
            (HERE / name).write_bytes(raw)
        else:
            require((HERE / name).read_bytes() == raw, "Deterministic artifact: " + name)
    print(json.dumps({"status": "PASS", "new_decimal_digits": len(new_decimal)-1,
                      "saved_decimal_digits": len(old_decimal)-len(new_decimal), "all430_actions_equal": True,
                      "whole_ports_unchanged_at": list(LAYOUTS), "script_sha256": data["script_sha256"],
                      "certificate_sha256": sha(receipt)}, sort_keys=True))


if __name__ == "__main__":
    main()
