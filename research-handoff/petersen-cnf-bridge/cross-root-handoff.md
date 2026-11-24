# Shared proofs for two unsafe prefix gates

The scope is a six-gate read-two separator for the specified Petersen boundary, with two unsafe gates at its front and the four safe terminal gates in the project's existing normal form. Each covered first gate represents every one of the 2,048 × 2,048 ordered second gate choices.

## Semantic interface

* `RootEnvelope.lean` constructs group-wide upper positive columns and lower negative columns. One missing mixed-row bit within a private edge's four rows forces a bare edge at the output. The spent-variable and degree bounds yield contradictions for the whole mask box.
* `EnvelopeTree.lean` proves soundness for a postfix tree of 22 possible splits and two leaf kinds. `EnvelopeMask.lean` proves that deleting a wire from both signs of all rows can only remove mixed rows. This permits a lower bound on the first gate's used vertex set for the entire group.
* `EnvelopeOrbit.lean` relabels the actual input circuit and its first masks by a verified Petersen automorphism. It carries the candidate, read budget, and normal-form assumptions through the relabeling. `OrbitRows.lean` connects packed subtrees and finite membership lists to the resulting circuit exclusion.
* The single-process study in `EnvelopeTenBench.lean` compares 7,570 independent nodes against 907 shared nodes. `VariableUseBench.lean` compares three exact-use trees totaling 2,621 nodes against the one lower-use tree of 1,233 nodes. Both export actual circuit exclusions and their individual receipts contain timings, peak working set, source hashes and axiom output.

## Reproduction

All commands run from this directory. Use the project's bundled Node executable for each script. The Lean commands use `time-lean-module.ps1 MODULE`, which rejects warnings, errors, placeholders, and resource overruns.

1. Run `cross-root-search.cjs`, then `envelope-merge.cjs`, then `envelope-orbits.cjs`. Running the latter again with `--expand` searches up to 5,000 tree nodes per relaxed template while retaining the original first five selected trees.
2. Run `orbit-atlas-shard.cjs cross-orbit-pools.json A 0 5` to generate the first 257 distinct rows and their complete trees. Kernel dependencies, in order, are `RootEnvelope`, `EnvelopeTree`, `EnvelopeMask`, `EnvelopeOrbit`, and `OrbitRows`. Importing the existing workspace's prior modules supplies the circuit and graph semantics.
3. Check `OrbitAtlasA`. Its `all_entries` theorem excludes every candidate matching a listed pair. Its `count` and `unique` theorems certify its number of distinct firsts. The three small benchmark modules also support a transitive-constant audit in `OrbitAtlasAudit`, with the prior five-gate bound used as its positive control.
4. Run `orbit-manifest.cjs` to reconstruct the list of 32 remaining firsts, original branch frequencies and available Lean receipts. The 49 generated templates for 454 roots are held in `cross-expanded-pools.json`; only completed shard receipts represent kernel-checked coverage.

The exploratory catalogue and estimates are independent of historical SAT verdicts. The timings in `*-run.json` separate end-to-end compiler time from explicit markers surrounding individual proof families. An independently checked file may import more constants than its final theorem uses; the transitive audit follows theorem dependencies.

## Completed checks

| Kernel comparison | Prior time | Shared time | Ratio |
|---|---:|---:|---:|
| Ten first masks, separate trees and a single shared tree | 82.852 s | 8.908 s | 9.30× |
| Fifteen different first masks, three exact-use groups and one lower-use group | 27.247 s | 14.015 s | 1.94× |

`OrbitAtlasA` proves 257 distinct first-mask pairs with 7,823 nodes across five templates. The verifier took 186.514 s end to end and reached 4,616,089,600 bytes of peak working set. Eighty-six of these pairs formerly used a polar leaf. It exports the actual-circuit conclusion, the cardinality, and uniqueness. `OrbitAtlasAudit` independently traversed constants for this result and both benchmark theorems: all three were free of the imported five-gate bound, its original theorem, and proof placeholders. The printed axiom set for each consists of propext, Classical.choice and Quot.sound.
