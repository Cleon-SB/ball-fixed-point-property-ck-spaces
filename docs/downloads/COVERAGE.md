# Paper-to-Lean correspondence

Current target: `csb-BFPPCKsps-FV.tex` (928 lines).
SHA-256: `feefe0f1af582753d5b22ada4baa01e87b1c1533706f47cd02d4c3c1b8ddc5ca`.

On 2026-09-14 the unused Appendix A (Lemma A.1 and Remark A.2) and its two
explanatory references were removed from the manuscript. The main results
and their proofs are unchanged. The Lean sources are unchanged; the former
appendix remains available as supplementary formalized material. The original
checked manuscript hash is preserved in `VALIDATION.md`.

A subsequent editorial revision of 2026-09-14 incorporates the author's
formatting and introductory changes, Boolean terminology, three motivating
sentences, and the Koppelberg reference. A duplicated equation label in the
author's split display was corrected. Mathematical statements and construction
formulas are unchanged, and all Lean source files remain unchanged. The new
background paragraphs explain the order notions already used in the modules
below; they introduce no additional proof assumptions.

The final submission source was renamed `csb-BFPPCKsps-FV.tex` at the author's
request. Its contents match the saved author source byte for byte. Compared
with the previous 918-line version, it adds the Lean formalization paragraph
and an extra blank line. All 38 statement/proof environments are identical
modulo whitespace; the entire source is identical modulo whitespace after
removing that added paragraph. The correspondence table below is unchanged.

This map concerns mathematical results. Historical attribution, bibliographic
priority, and journal formatting are not assertions certified by Lean.

| Paper component | Lean modules and principal declarations |
|---|---|
| BFPP definition | `Transfer`: `HasBFPP`, `UnitBall` |
| Equivalence with all closed balls | `BallScaling`: `hasBFPP_iff_all_closedBalls`, including radius zero |
| Introductory discrete affine recurrence | `DiscretePropagation`: `affine_propagation_lipschitz`, `discrete_recurrence_nonexpansive` |
| Main result and BFPP characterization | `Characterization`: `hasBFPP_iff_extremallyDisconnected` |
| Ordinal envelopes and contraction | `Suprema`, `BoundedFamilies`, `Envelopes`: `upperEnvelope_nonexpansive`, `lowerEnvelope_nonexpansive` |
| TCP definition and automatic nonexpansiveness | `TransfinitePropagator`: `IsTCP`, `IsTCP.nonexpansive` |
| Transfer and order domination | `Transfer`: `fixedPointEquiv`, `fixedPointFree_transfer`, `nonexpansive_transfer`, `order_domination` |
| Delay, unchanged tails, no subsolutions | `Profiles`: `delay`, `tail_delay`, `subsolution_eq_zero` |
| Continuous regularization | `Regularization`: `regularizeValue_continuous`, successor and limit formulas |
| Profile and domain geometry | `ProfileGeometry`, `TwoProfiles`, `TwoProfileGeometry` |
| Finite synthesis, density, positive extension and uniqueness | `FiniteSynthesis`, `StepFunctions`, `StepAlgebra`, `PositiveSynthesis`: `stepCombination_denseRange`, `positiveSynthesis_exists`, `positiveSynthesis_unique` |
| Representing finite Radon measures | `SynthesisMeasure`, `SynthesisIntegral`: `positiveSynthesis_measure_representation`, `synthesisMeasure_real_mass` |
| Convex integral identity and combined mass bound | `ConvexIntegral`: `synthesizeMap_convexIntegral_max_min`, `synthesisMass_add_le_one` |
| Analysis from level-set deficits | `Deficits`, `Analysis`: `InseparableLevels.analyze`, `analyze_nonexpansive`, `analyze_le_of_bounds` |
| Center and C₀ profiles | `Center`, `C0Profiles`, `CenteredSynthesis` |
| Two-profile realization | `Families`, `Realization`: actual `synthesize`, `analyze_synthesize_le`, `ballMap_nonexpansive`, `ballMap_fixedPointFree` |
| Ordinal order topology and compact initial intervals | `OrdinalIndex`, `StepFunctions` |
| Countable cozero unions | `Cozero`, `CountablePairs` |
| Boolean and order terminology (unnumbered background) | mathlib's `BooleanAlgebra`, `Clopens`, `IsChain`, `IsLUB`; the gap and cofinal sequence notions used in `BooleanGap`, `CofinalSequences`, `IndexedGaps` |
| Boolean gap and cofinal indexing | `ChainCompleteness`, `BooleanGap`, `CofinalSequences`, `IndexedGaps` |
| Zero-dimensional construction | `ClopenCompleteness`, `ClopenPairs`: `IndexedGap.toInseparablePair`, `not_hasBFPP_of_zeroDimensional_not_ED` |
| Transfinite sign extension and termination | `SignExtension`, `Hartogs`, `SignRecursion`, `SignTermination`, `SaturatedChains`, `SignRealization` |
| Regular cofinal lengths and uncountability | `CofinalReindexing`, `OrdinalCofinality`, `CountablePairs`, `RegularPairs` |
| Extension and affine isometric encoding | `OrdinalPairs`, `ProfileExtension`, `ExtensionDelay`, `Interleaving`, `TwoProfileStructure`, `EncodedDomain` |
| Encoded A, J, P and fixed-point obstruction | `EncodedMaps` |
| Prefix envelopes and exact recurrence formulas | `EnvelopeOrder`, `InterleavingEnvelopes`, `ProfileRestriction`, `EncodedRules` |
| Successor rules on the actual prefix sets | `PrefixFactorization`, `DelayPrefixBound`, `EncodedRecurrence`: `encodedPropagator_isTCP` |
| Single-ordinal transfinite realization | `MainTransfinite`: `exists_transfinite_realization` |
| Whole-ball map for every non-ED compact Hausdorff K | `Necessity`: `exists_nonexpansive_fixedPointFree_of_not_ED` |
| ED implies BFPP | `EDSupremum`, `BallOrderGeometry`, `InvariantIntervals`, `LatticeFixedPoint`, `Characterization` |
| BFPP implies F-space | `ContinuousBall`, `FSpaceNecessary`: `isFSpace_of_hasBFPP` |
| Complex scalar extension | `ComplexBall`: `exists_complex_fixedPointFree_of_not_ED` |
| Supplementary result (former Appendix A): terminal pointwise supremum | `PointwiseSupremum`, `PointwisePrefixes`, `TerminalSupremum` |
| Supplementary normalization (former Appendix A) | `TerminalNormalization`, `NormalizedAppendix`: `exists_normalized_terminal_supremum` bundles continuous profiles, every limit identity, terminal supremum, norm one, and discontinuity |

The names above lie in namespace `BFPP`; module names identify files, not
additional namespaces. The main declaration is `BFPP.exists_transfinite_realization`.

## Fidelity of the statements

`exists_transfinite_realization` assumes only that K is compact Hausdorff,
an F-space, and not extremally disconnected. It constructs the ordinal, domain,
and all three maps, with explicit conclusions for:

- `κ.card.ord = κ`, regularity, and `ℵ₀ < κ.card`;
- nonemptiness, closedness, boundedness, and convexity of D;
- nonexpansiveness of A, J, and P, and the precise `IsTCP D P` rules;
- absence of fixed points for A∘J∘P and J∘P∘A.

`HasBFPP C(K, ℝ)` concerns the whole closed unit ball with the supremum norm.
`BoundedFamily ι` is mathlib's bounded continuous function space with the index
topology explicitly discrete: it represents ℓ∞ with its genuine supremum metric.
Ordinal spaces for C₀ synthesis independently carry their order topology.
No discrete-topology assumption is made about K.

`IsFSpace K` uses the paper's disjoint-cozero-sets/disjoint-closures formulation.
`TotallySeparatedSpace K` supplies the clopen-separation form of the
zero-dimensional case for compact Hausdorff K.

The former appendix uses `I = Set.Icc (0 : ℝ) 1` as codomain. Suprema are in that
complete interval, giving empty prefixes value zero. They are pointwise
suprema, distinct from order suprema in C(K). Its cardinal is independent of
the cardinal used for the main realization.

## Proof organization and scope

- The finite synthesis estimate makes extension well-defined directly; linear
  independence need not be packaged as a separate lemma.
- Centered synthesis is proved contractive directly from positivity. The
  measure representation, mass identities, and displayed convex-integral
  calculation are also formalized separately. Inner regularity handles the uncountable union in the mass
  formula; countable additivity is not misapplied.
- The ED implication is proved internally through continuous lattice suprema
  and minimal invariant intervals. The external fixed-point theorem cited in
  the paper is not assumed as an axiom.
- The supplementary terminal-supremum construction minimizes cardinality among all discontinuous families of
  continuous [0,1]-valued functions. An open nonclosed set supplies such a
  family; the minimizing family yields the same stated conclusions.

An independent statement review found no weakened principal conclusion or
hidden realization assumption. `Audit.lean` checks all BFPP declarations,
including generated ones, and rejects any axiom except `propext`,
`Classical.choice`, and `Quot.sound`. The statement correspondence complements
the audit: kernel checking alone does not certify fidelity to a manuscript.
