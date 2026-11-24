# Lylighte's research handoff

November 24, 2026. This archive records local work on three gaps in the pequalnp project. The checkout used for the research was `755e437b95776da124d29aff8c2ea82c121fd9d7`. The upstream checker has not accepted these materials as a solution to L-meta-920 or L-meta-1414.

**中文摘要**　L-meta-920 的数学推导和有限穷举给出 29 门下界，Lean 已验证的无条件下界为 25 门，题目要求 39 门。29 门规模仍有一类电路待排除。L-meta-1414 保留了反向命题的手工证明和部分 Lean 核验。L-meta-905 的最终解答由另一位贡献者提交；这里存放本机独立产生的部分结果。

## L-meta-920 — lower bounds for a 13-output circuit

The problem asks whether every binary monotone circuit for the thirteen projective-plane outputs on the promised domain needs at least 39 gates. A 39-gate construction is known. A mathematical reduction and exhaustive finite checks give a lower bound of **29 gates**. The last 434 candidate prefixes for size 28 yielded 62,704 classes of sixth-OR extensions. Every class was excluded and none reached a search cutoff. The account of the argument includes reproduction instructions. [29-gate lower bound](plane920-core/twenty-nine.md) · [Independent coverage receipt](plane920-search/audit-strong-28.json)

At size 29, a possible circuit in the sparse dual must have eight OR gates, eight hidden AND gates and thirteen output AND gates. The reductions leave 90 classes of three-OR prefixes and 2,266 four-OR continuations. At shutdown, the stronger fifth-level test had processed 1,311 of those 2,266 continuations. Among the processed ones, 120,064 fifth-level extensions remained open. Unprocessed cases and branches reaching a cutoff must be retained. [Remaining cases](plane920-core/twenty-nine-candidates.md) · [Search checkpoints](plane920-core/unrestricted/) · [Raw-input restrictions](plane920-math/eight-raw-anchors.md)

The unconditional lower bound previously checked in Lean is **25 gates**. The file for the connected case additionally restricts the last split of a candidate of size at most 25 to 1+12 or 2+11. The larger file built locally. Its final independent replay and axiom audit were interrupted at shutdown. [25-gate theorem](plane920-lean/Plane920TwentyFive.lean) · [Connected-case source](plane920-lean/Plane920RootTwo.lean) · [Module-level verification record](plane920-lean/root-two-handoff.md)

One reusable subresult is that any five complete target lines require at least six hidden AND gates even with free OR gates. The eleven archives collectively contain all 354 CNF, LRAT and JSON triples selected by the recorded five-target audit. It checked 37,808 admissible tuples and 1,303,178 RUP additions. [Subfamily proof](plane920-math/partial-helper-proof.md) · [Audit receipt](plane920-math/small-core/five-partial-audit.json) · [Certificates](plane920-math/certificates/)

## L-meta-1414 — a restriction of the seven-cycle edge function

The local mathematical argument proves the positive assertion that the posted statement negates. It finds a variable restriction making at least three gates removable on the zero side or at least four on the one side. The evidence includes 84 cofactor witnesses, a finite formula enumeration, two control circuits and Lean sensitivity lemmas. A general Lean proof of the positive assertion remains open in these materials. The gap was returned under `statement_seems_false`. [Mathematical argument](cycle1414-math/positive-proof.md) · [Witnesses](cycle1414-math/cofactor-witnesses.json) · [Finite enumeration](cycle1414-search/) · [Lean sensitivity lemmas](cycle1414-lean/sensitivity/)

## L-meta-905 — partial Petersen circuit results

The project accepted another contributor's solution in PR #2775. Local artifacts include a necessary condition on six-gate candidates, a Lean classification covering 257 specified first-mask pairs, and a concrete CNF/LRAT exclusion for orbit 15-593. The archive includes the classification's local Lean import dependencies. [Upstream PR #2775](https://github.com/brilliant-hq/pequalnp-proofs/pull/2775) · [Necessary condition](petersen-struct/PetersenSafe.lean) · [Orbit classification](petersen-cnf-bridge/cross-root-handoff.md) · [Certificate and checker](petersen-cert/)

## Reading and checking the archive

Paths beginning with `state/` in the original notes refer to the matching folder under `research-handoff/` in this branch. The snapshot includes the recorded prefix-search checkpoints, the five-target certificate collection above, and selected Lean sources and smaller results. Other bulk solver traces, compiled Lean objects and machine-specific tool installations are not bundled. Some original experiment scripts refer to those local inputs or tool paths.

To inspect the completed search joins using Node.js 20 or later, run the following from this directory. These two commands read the recorded shard files and regenerate the corresponding audit receipts.

```sh
node plane920-core/audit-early-29.cjs
node plane920-search/audit-strong-28.cjs
```

To unpack and check the five-target certificates using a POSIX shell, run the following from this directory. The archives extract under `plane920-math/small-core/five-partial/`. The audit regenerates the CNFs and checks the proof traces.

```sh
for part in plane920-math/certificates/*.tar.gz; do
  tar -xzf "$part" -C plane920-math
done
node plane920-math/audit-five-partial.js
```

The repository's `lean/lean-toolchain` and `lean/lake-manifest.json` pin the Lean environment. With the project's Lean build artifacts available, the standalone lower-bound source can be checked from the repository root with `cd lean`, followed by `lake env lean ../research-handoff/plane920-lean/Plane920TwentyFive.lean`. The SHA-256 manifest in this directory covers the published files, including each compressed certificate archive.
