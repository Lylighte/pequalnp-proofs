# Connected 25-gate candidates on the 13-point plane

The Lean theorem Plane920.RootCost.last_partition reduces the last hidden merge of a correct binary AND/OR project circuit whose normalized hidden graph is connected and whose total size is at most 25. Its two parent components partition the thirteen inputs. Their sizes must be 1 and 12, or 2 and 11. In the latter case at least eight of the physical non-output gates must be dual AND gates, that is, original OR gates. The last hidden gate itself is a dual AND. Plane920.RootCost.remaining_count verifies the count of 91 possible smaller sides: thirteen singletons and 78 two-point sets. This excludes 4,004 of the 4,095 unordered nontrivial cuts. Previously three collineation orbits covering 1,872 cuts had been excluded.

## Certificate

For a split into A and B, and a crossing line L, define x=|L∩A|−1 and y=|L∩B|−1. A dual OR pays x+y earlier hidden dual ANDs on that line. A dual AND also pays for itself and can waive one side only if the fixed opposite driver matches that side's designated minimum label. The soundness theorem cost_le computes the smallest allowed line charge for each fixed pair of driver labels. The sum of the charges is a lower bound on the physical gate budget, by disjointness of minimum labels from different plane lines and of the two child component pools.

All twelve representatives with smaller side between three and six points require at least thirteen hidden gates for every driver-label pair and both operation types. The threshold is tight for the collinear three-point representative. The published problem allows at most twelve hidden gates in this candidate size range. The singleton and two-point bounds are kept distinct from the excluded classes.

The orbit certificate contains 13 explicit collineations, each with checked point permutation, line permutation, inverses and incidence preservation. The certificate for 8,192 labeled masks chooses a collineation that strictly decreases each nonrepresentative mask in the selected cardinality range. The Lean checker verifies each ticket and proves coverage by strong induction. The JavaScript source constructs witnesses and is not part of the Lean premises. Two-point sets are normalized independently to obtain the eight-gate floor.

## Files and costs

- Plane920RootTwo.lean is the flattened proof with the single official import PEqualNP.Defs. Size is 379,808 bytes. SHA-256 is c99ad3578c67c107c9215f6908fbad71e2cbc3856aacf5106836799402fd11db.
- RootNumericReps.lean contains the twelve representative tests. Its local build took 23.483 seconds and independent leanchecker replay took 31.480 seconds.
- RootNumericAll.lean covers all 8,192 tickets in 32 shards. Its local build took 168.713 seconds. Observed peak resident memory reached 2,088 MiB during this build. All Lean invocations used one process and a 3,500 MiB allocation cap.
- RootNumericPrune.lean, RootNumericPair.lean and RootNumericFinal.lean connect the finite evidence to the actual gate list and budget. They compiled in 16.707, 20.318, and 15.970 seconds respectively.
- The construction of 39 gates and the unconditional lower bound 25 are unchanged. No proof of the seven-point auxiliary lower bound or of global 26 follows from this cut classification alone.

To reproduce locally, in D:\pequalnp-agent\state\plane920-lean run the bundled Node executable with the following script arguments:

    D:\pequalnp-agent\tools\node\node.exe root-two-bundle.cjs
    D:\pequalnp-agent\tools\node\node.exe check.cjs build:Plane920RootTwo replay:Plane920RootTwo build:RootTwoAudit
