import BFPP

/-! Kernel dependency audit of every declaration in the BFPP namespace.
The allowlist is restricted to Lean's standard logical axioms.
-/

#print axioms BFPP.contractive_realization
#print axioms BFPP.BoundedFamily.supremum_nonexpansive
#print axioms BFPP.upperEnvelope_nonexpansive
#print axioms BFPP.Profile.subsolution_eq_zero
#print axioms BFPP.Profile.tail_mix
#print axioms BFPP.twoProfileSet_convex
#print axioms BFPP.twoProfileSet_isBounded
#print axioms BFPP.twoProfileSet_nonempty
#print axioms BFPP.TwoProfile.fixedPointFree_delay
#print axioms BFPP.isFSpace_of_hasBFPP
#print axioms BFPP.InseparableLevels.analyze_nonexpansive
#print axioms BFPP.InseparableLevels.contractive_realization
#print axioms BFPP.Profile.regularizeValue_continuous
#print axioms BFPP.Profile.positiveTail
#print axioms BFPP.Profile.center_add_positiveTail_dist
#print axioms BFPP.finite_synthesis_bounds_finset
#print axioms BFPP.stepCombination_denseRange
#print axioms BFPP.positiveSynthesis_exists
#print axioms BFPP.positiveSynthesis_unique
#print axioms BFPP.centeredSynthesis_dist
#print axioms BFPP.InseparablePair.synthesize_nonexpansive
#print axioms BFPP.InseparablePair.analyze_synthesize_le
#print axioms BFPP.InseparablePair.ballMap_fixedPointFree
#print axioms BFPP.InseparablePair.not_hasBFPP
#print axioms BFPP.countable_union_cozero
#print axioms BFPP.exists_first_bad_limit
#print axioms BFPP.not_hasBFPP_of_not_totallySeparated
#print axioms BFPP.exists_chainGap
#print axioms BFPP.exists_regular_cofinal_sequence
#print axioms BFPP.not_hasBFPP_of_zeroDimensional_not_ED
#print axioms BFPP.extremallyDisconnected_of_hasBFPP
#print axioms BFPP.exists_nonexpansive_fixedPointFree_of_not_ED
#print axioms BFPP.edSup_isLUB
#print axioms BFPP.exists_minimal_invariant_interval
#print axioms BFPP.fixedPoint_of_interval_balls
#print axioms BFPP.hasBFPP_iff_extremallyDisconnected
#print axioms BFPP.IsTCP.nonexpansive
#print axioms BFPP.encodedPropagator_isTCP
#print axioms BFPP.exists_transfinite_realization
#print axioms BFPP.exists_complex_fixedPointFree_of_not_ED
#print axioms BFPP.positiveSynthesis_measure_representation
#print axioms BFPP.synthesisMeasure_real_mass
#print axioms BFPP.exists_terminal_pointwise_supremum_of_not_ED
#print axioms BFPP.normalizedTerminal_norm
#print axioms BFPP.normalizedTerminal_not_continuous
#print axioms BFPP.exists_normalized_terminal_supremum
#print axioms BFPP.InseparablePair.synthesizeMap_convexIntegral_max_min
#print axioms BFPP.InseparablePair.synthesisMass_add_le_one
#print axioms BFPP.hasBFPP_iff_all_closedBalls
#print axioms BFPP.discrete_recurrence_nonexpansive

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "BFPP." then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  logInfo m!"Axiom audit passed for {checked} declarations in namespace BFPP."
