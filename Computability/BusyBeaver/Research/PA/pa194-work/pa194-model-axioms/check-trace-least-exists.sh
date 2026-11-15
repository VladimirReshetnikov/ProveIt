#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 281ff83fc10dc9d00708ff9583c601dab47a7979b524714801ad141df285707d /dev/shm/pa194-trace-direct-syntax-repo/PA194TraceDirectSyntax.olean \
 b12feb7611facb48c3ad17c75d40013a0e580dcf30725232f707310908fff4aa "$src/PA194TraceLeastExists.lean" \
 ad2a21f4cccdef0b6d121a53b10be1ff271c660fd08ad54c058c9cea45d1bc5c /dev/shm/pa194-domain-least-at-repo/PA194DomainLeastAt.olean \
 1bda255a714ea9f3c45591dbb4ec26170476c686d2836ea4755b5f6d564101fb /dev/shm/pa194-domain-least-closed-repo/PA194DomainLeastClosedModel.olean \
 e84db1ddd611ce200d58e2a76d9abffa1e1b984de82d33332a798585b7076a75 /dev/shm/pa194-member-nonempty-repo/PA194MemberNonempty.olean \
 9f9afb2c85bdd75477759ced5d9134366ad9c9acf00d667b3797ffda3a874e64 /dev/shm/pa194-trace-subset-repo/PA194TraceSubset.olean \
 b989862609710dad18447cb9147b0ecc56e4b3a5baf4d59d99c6d0115c32c608 /dev/shm/pa194-greatest-witness-open-repo/PA194GreatestWitnessOpen.olean \
 9fdbb6b74338b33e160fe89537af84a487ea3a93f703009709a1a028bb048618 /dev/shm/pa194-greatest-bad-contradiction-repo/PA194GreatestBadContradiction.olean \
 2811574e5c96b2ae68fa548a422c9465c3129ddd950f6e9022b24c92c55715fb /dev/shm/pa194-bad-trace-step-shift-repo/PA194BadTraceStepShift.olean \
 3a0bbad40878949b2738aeb6cb19e1a4d1458d402f5129d679de845e7139041d /dev/shm/pa194-fixed-instance-shift-repo/PA194FixedInstanceShift.olean \
 eb3f9ff1894227d17b5a9d03ebeeb5930d13775d490e089435e261968b18b0b7 /dev/shm/pa194-least-dummy-index-repo/PA194LeastDummyIndex.olean \
 18ec94b853ff7f1bd6db2b422a28486a6609c36adeaab0a7dfcee1416c4fbe70 /dev/shm/pa194-trace-direct-shift-repo-v2/PA194TraceDirectShift.olean \
 ca0a0224cf8fd61c958fa33c8d53d6b72d203edb14beafa587af385e1a5f25ec /dev/shm/pa194-greatest-bad-step-repo/PA194GreatestBadStep.olean \
 e29d1e4594e4d6938240859fbb8d81ba38cd0ac43e98cad91b6c669055ea9617 /dev/shm/pa194-greatest-member-projection-repo/PA194GreatestMemberProjection.olean \
 8aee8706b129bd55e5de0432ec9dedf28976aede67e2ec8fb379b241e2f267f7 /dev/shm/pa194-least-bad-direct-trans-repo/PA194LeastBadDirectGoodTransitive.olean \
 b160e900665e334211c576b8c076d81c6a0393be5d025edf8154922ad2db2434 /dev/shm/pa194-ordinal-step-application-code-repo/PA194OrdinalStepApplicationCode.olean \
 24f5487d2265bc0af9b63a6c1684d61cd796c4aeebf11a214dc2bf52fff6eec3 /dev/shm/pa194-least-bad-direct-good-repo/PA194LeastBadDirectMemberGood.olean \
 63110ad58e1f69209ef1d8932b0a2165b0834824b3254ea3ae937d609730b412 /dev/shm/pa194-trace-direct-member-repo/PA194TraceDirectMember.olean \
 0c809a85600a1fe9280bea0d596bc9a6ce1a99903fa291e62f50e498926b8f91 /dev/shm/pa194-trace-direct-at-repo/PA194TraceDirectAt.olean \
 03e477e4b4996500303b468758f755ef24fa6f1f41416f38ba608dd9e768d27e /dev/shm/pa194-greatest-successor-repo/PA194GreatestSuccessorAtCode.olean \
 a85fbe811c71eedeba5153a55b27227915b06ffcf5b1fbba23a68745aa8b7655 /dev/shm/pa194-domain-greatest-repo/PA194DomainGreatestAtCode.olean \
 41e19a43b9d790073b142906b85cc7b6517e5b1b2078f1161f3c3ee51462a0ec /dev/shm/pa194-context-exs-witness-repo/PA194ContextExsWitnessCode.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-domain-least-at-repo:/dev/shm/pa194-domain-least-closed-repo:/dev/shm/pa194-member-nonempty-repo:/dev/shm/pa194-trace-subset-repo:/dev/shm/pa194-greatest-witness-open-repo:/dev/shm/pa194-greatest-bad-contradiction-repo:/dev/shm/pa194-bad-trace-step-shift-repo:/dev/shm/pa194-fixed-instance-shift-repo:/dev/shm/pa194-least-dummy-index-repo:/dev/shm/pa194-trace-direct-shift-repo-v2:/dev/shm/pa194-greatest-bad-step-repo:/dev/shm/pa194-greatest-member-projection-repo:/dev/shm/pa194-least-bad-direct-trans-repo:/dev/shm/pa194-ordinal-step-application-code-repo:/dev/shm/pa194-domain-transitive-repo:/dev/shm/pa194-least-bad-direct-good-repo:/dev/shm/pa194-ordinal-base-application-code-repo:/dev/shm/pa194-trace-direct-member-repo:/dev/shm/pa194-least-bad-member-good-repo:/dev/shm/pa194-least-excludes-instances-repo:/dev/shm/pa194-ordinal-bad-not-zero-repo:/dev/shm/pa194-trace-member-backward-repo:/dev/shm/pa194-trace-direct-at-repo:/dev/shm/pa194-trace-direct-syntax-repo:/dev/shm/pa194-greatest-successor-repo:/dev/shm/pa194-domain-greatest-repo:/dev/shm/pa194-least-excludes-at-repo:/dev/shm/pa194-domain-instances-repo:/dev/shm/pa194-member-domain-at-repo:/dev/shm/pa194-member-domain-closed-repo:/dev/shm/pa194-trace-member-forward-repo:/dev/shm/pa194-expanded-trace-at-repo:/dev/shm/pa194-separation-trace-open-repo:/dev/shm/pa194-context-projections-contradiction-repo:/dev/shm/pa194-context-triple-specialize-repo:/dev/shm/pa194-least-excludes-closed-repo:/dev/shm/pa194-full-sep-witness-branch-repo:/dev/shm/pa194-separation-witness-from-root-repo:/dev/shm/pa194-separation-trace-witness-repo:/dev/shm/pa194-separation-trace-shift-repo:/dev/shm/pa194-separation-trace-at-code-repo:/dev/shm/pa194-context-exs-witness-repo:/dev/shm/pa194-context-quantifier-code-repo:/dev/shm/pa194-ordinal-step-application-code-repo:/dev/shm/pa194-context-specialize-code-repo:/dev/shm/pa194-context-mp-code-repo:/dev/shm/pa194-context-conjunction-code-repo:/dev/shm/pa194-context-shift-code-repo:/dev/shm/pa194-internal-separation-shift-repo:/dev/shm/pa194-empty-source-proof-repo:/dev/shm/pa194-congruence-source-proof-repo:/dev/shm/pa194-standard-equality-suppliers-repo:/dev/shm/pa194-ordinal-suppliers-repo:/dev/shm/pa194-standard-ordinal-reduction-repo:/dev/shm/pa194-intersection-proof-repo:/dev/shm/pa194-full-sep-open-repo:/dev/shm/pa194-full-sep-theory-replay:/dev/shm/pa194-standard-no-free-replay:/dev/shm/pa194-closed-sep-classifier-replay:/dev/shm/pa194-fairness-full-source-replay:/dev/shm/pa194-generic-sim-replay:/dev/shm/pa194-adjunctive-sim-v2-replay:/dev/shm/pa194-shift-interface-replay:/dev/shm/pa194-unrestricted-existential-v2-replay:/dev/shm/pa194-qf-ranked-existential-audit:/dev/shm/pa194-general-shift-replay:/dev/shm/pa194-general-reverse-shift-replay:/dev/shm/pa194-general-freshness-audit:/dev/shm/pa194-observational-general-audit:/dev/shm/pa194-quoted-induction-repo:/dev/shm/pa194-reopen-proof-repo:/dev/shm/pa194-close-proof-repo:/dev/shm/pa194-uniform-fully-closed-repo:/dev/shm/pa194-uniform-closure-replay:/dev/shm/pa194-unclose-envelope-replay:/dev/shm/pa194-separation-trace-open-repo:/dev/shm/pa194-separation-trace-witness-repo:/dev/shm/pa194-separation-trace-shift-repo:/dev/shm/pa194-context-exs-witness-repo:/dev/shm/pa194-context-quantifier-code-repo:/dev/shm/pa194-separation-trace-at-code-repo:/dev/shm/pa194-induction-step-shift-repo:/dev/shm/pa194-uniform-sep-combined-repo:/dev/shm/pa194-separation-shift-code-repo:/dev/shm/pa194-internal-induction-at-context-repo:/dev/shm/pa194-context-specialize-code-repo:/dev/shm/pa194-context-mp-code-repo:/dev/shm/pa194-context-conjunction-code-repo:/dev/shm/pa194-context-shift-code-repo:/dev/shm/pa194-internal-separation-shift-repo:/dev/shm/pa194-internal-induction-base-at-repo:/dev/shm/pa194-induction-base-shift-repo:/dev/shm/pa194-ordinal-uniform-repo:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-typed-schema-repo:/dev/shm/pa194-fully-closed-repo:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-repo:/dev/shm/pa194-ranked-open-separation-repo:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194TraceLeastExists; do
 lean -j1 -M 4000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
[[ $(rg -c 'depends on axioms:' "$out/PA194TraceLeastExists.log") == 3 ]]
check_inputs
echo 'PASS: trace least-existence composition; dependencies prebuilt.'
