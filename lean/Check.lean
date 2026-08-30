import Erdos307.Barrier
import Erdos307.Breeder
import Erdos307.Bridge
import Erdos307.Campaign
import Erdos307.Capstone
import Erdos307.CharSum
import Erdos307.Closed
import Erdos307.Congruential
import Erdos307.Coprime60
import Erdos307.Dictionary
import Erdos307.Distinctness
import Erdos307.DivisorSum
import Erdos307.Extremal
import Erdos307.Frame
import Erdos307.FunctionField
import Erdos307.HalfLyap
import Erdos307.InfZero
import Erdos307.Injective
import Erdos307.Ladder
import Erdos307.KovicProp18
import Erdos307.LevelBarrier
import Erdos307.LiveSlot
import Erdos307.LocalComplete
import Erdos307.LyapFalse
import Erdos307.Mod8
import Erdos307.NoGain
import Erdos307.NoInvariant
import Erdos307.NoPlace
import Erdos307.NoPoly
import Erdos307.NormalForm
import Erdos307.Numeral
import Erdos307.PairAvg
import Erdos307.PairLocal
import Erdos307.PlusThin
import Erdos307.Pythagorean
import Erdos307.RhoBarrier
import Erdos307.Rigidity
import Erdos307.Sixty
import Erdos307.SquareSieve
import Erdos307.Squarefree
import Erdos307.StratumGeneral
import Erdos307.StratumM30
import Erdos307.TailBound

/-! # Axiom audit for the whole development

Regenerated mechanically from `Erdos307/*.lean`, so it cannot drift behind the source. Run from
`lean/`:

    lake env lean Check.lean

Expected: everything on `{propext, Classical.choice, Quot.sound}` or fewer, with exactly one
exception, `dfs_run` and the `erdos307_sixty` that consumes it.

`#print axioms` reports nothing about whether a theorem's hypotheses are satisfiable. A vacuous
theorem passes this file cleanly; one did. `Vacuity.lean` is the companion check.
-/

open Erdos307

#print axioms reciprocal_sum_gt_two
#print axioms P58
#print axioms N58
#print axioms P59
#print axioms N59
#print axioms recipSum58_lt_two
#print axioms recipSum59_gt_two
#print axioms barrier_numeric
#print axioms barrier_algebraic
#print axioms barrier
#print axioms two_cycle_iff_double_fixed
#print axioms ad_dprod
#print axioms dprod_ne_dprod
#print axioms bridge_forward
#print axioms disjoint_primeFactors_of_cycle
#print axioms bridge_backward
#print axioms mass_eq
#print axioms bridge
#print axioms jacobiSym_add_four_mul
#print axioms jacobiSym_A_eq_B
#print axioms dprod_pos
#print axioms recipSum_eq
#print axioms solution_disjoint
#print axioms erdos307_barrier
#print axioms quadratic_inv
#print axioms twist_inv_involutive
#print axioms sum_char_twist_inv
#print axioms hmono_all
#print axioms recip_sum_ge_two
#print axioms card_ge_59
#print axioms erdos307_barrier_closed
#print axioms const_increment_iterate
#print axioms two_nsmul_eq_zero_of_period_two
#print axioms no_period_two_of_two_nsmul_ne_zero
#print axioms period_two_of_const_increment_of_ne
#print axioms zmod_two_mul_eq_zero_of_period_two
#print axioms coprime_loss
#print axioms loss_antitone
#print axioms loss_at_277
#print axioms half_add_half
#print axioms multiset_solution
#print axioms distinctness_carries_the_barrier
#print axioms transfer_dissolves
#print axioms divisorsAntidiagonal_subset_square
#print axioms divisorsAntidiagonal_pairwiseDisjoint
#print axioms tau_div_eq_antidiagonal_sum
#print axioms sum_tau_div_le_harmonic_sq
#print axioms sum_tau_le_mul_harmonic_sq
#print axioms harmonic_eq_sum_one_div
#print axioms sum_tau_div_le_log_sq
#print axioms count_in_residue_classes
#print axioms two_pow_omega_le_tau
#print axioms nth_prime_le_orderEmb
#print axioms orderEmb_prod
#print axioms orderEmb_sum
#print axioms prod_first_primes_le
#print axioms recipSum_le_first_primes
#print axioms hRatio_of_extremal
#print axioms csum_insert_prime
#print axioms dprod_insert_prime
#print axioms frame_cycle
#print axioms frame_solve
#print axioms anatomy_on_support
#print axioms csum_eq_mul_recipSum
#print axioms anatomy_iff
#print axioms deg_drop_of_terms
#print axioms no_two_cycle_of_drop
#print axioms no_fixed_point_of_drop
#print axioms ff_no_cycle
#print axioms log_lt_half_sub
#print axioms delta_decreasing
#print axioms two_le_add_of_mul_eq_one
#print axioms exists_block_sum_near
#print axioms infimum_zero
#print axioms den_eq_of_coprime_cross
#print axioms dprod_eq_of_mass_eq
#print axioms csum_eq_of_mass_eq
#print axioms dprod_primeFactors
#print axioms eq_of_cross
#print axioms k_nonpos
#print axioms rung_cross
#print axioms rung_mass_indep
#print axioms rung_minus_one
#print axioms rung_parity_mixed
#print axioms rung_parity_odd
#print axioms k_determined
#print axioms admissible_extends
#print axioms admissible_of_card_add
#print axioms level_enumeration_terminates
#print axioms live_slot_threshold
#print axioms recipSum9_lt_three_halves
#print axioms three_halves_le_recipSum10
#print axioms threshold_bracket
#print axioms regime_one_collapse
#print axioms regime_one_same_argument
#print axioms regime_two_constant
#print axioms regime_two_constant'
#print axioms regime_three_count
#print axioms no_single_class
#print axioms criterion_fails_of_pos
#print axioms criterion_fails_of_nonpos
#print axioms no_lambda_works
#print axioms one_lt_sigmaN0
#print axioms sigmaN0_lt
#print axioms lyapunov_criterion_false
#print axioms odd_sq_mod8
#print axioms cofactor_odd
#print axioms mod8_law
#print axioms prime_sums_congruent
#print axioms prime_sum_eq_product
#print axioms parity_law
#print axioms omega_even_of_even_derivative
#print axioms not_both_even
#print axioms dprod_odd
#print axioms derivative_mod8
#print axioms plus_quantity_mod8
#print axioms sq_values_mod8
#print axioms plus_hit_residue
#print axioms even_sq_mod8
#print axioms plus_hit_residue_split
#print axioms odd_sq_sub_one_dvd
#print axioms mod8_law_int
#print axioms mixed_member_mod16
#print axioms even_member_mod16
#print axioms mixed_prime_sum_mod8
#print axioms cycle_product
#print axioms le_max_of_both
#print axioms cycle_bound
#print axioms cycle_bound_max
#print axioms gain_lt_one_order
#print axioms nogain
#print axioms half_works
#print axioms no_f_above_two
#print axioms mass_sum_threshold
#print axioms lambda_eq_half
#print axioms exists_f_of_injective
#print axioms increment_iff
#print axioms no_two_cycle_of_decreasing
#print axioms Descends
#print axioms not_descends_of_le
#print axioms der_thirty
#print axioms not_descent_of_strictMono
#print axioms padic_lowers_on_support
#print axioms raises_two
#print axioms raises_three
#print axioms raises_five
#print axioms not_descent_padic
#print axioms no_place_descent
#print axioms const_prod_eq_one_of_tendsto
#print axioms eps_eq_zero_of_identity
#print axioms nonconstant_empty
#print axioms nopoly
#print axioms Erdos307.Dictionary.cost_of_ratio
#print axioms Erdos307.Dictionary.mass_window
#print axioms Erdos307.Dictionary.uniform_from_multiplicity
#print axioms Erdos307.Dictionary.band_bound
#print axioms Erdos307.Dictionary.band_bound_general
#print axioms Erdos307.Dictionary.forced_prime
#print axioms Erdos307.Dictionary.threshold_pushes
#print axioms Erdos307.Dictionary.rung_floor
#print axioms no_family_of_any_shape
#print axioms dvd_sum_erase_iff
#print axioms Q_determined
#print axioms oneprime_forced
#print axioms oneprime_cycle
#print axioms oneprime_converse
#print axioms oneprime_mass_identity
#print axioms oneprime_mass_bound
#print axioms slot_layers
#print axioms slot_recovery
#print axioms cofactor_survival
#print axioms qr_filter
#print axioms symbolfact
#print axioms np0
#print axioms np1
#print axioms np2
#print axioms np3
#print axioms np4
#print axioms np5
#print axioms np6
#print axioms np7
#print axioms np8
#print axioms np9
#print axioms np10
#print axioms np11
#print axioms np12
#print axioms np13
#print axioms np14
#print axioms np15
#print axioms np16
#print axioms np17
#print axioms np18
#print axioms np19
#print axioms np20
#print axioms np21
#print axioms np22
#print axioms np23
#print axioms np24
#print axioms np25
#print axioms np26
#print axioms np27
#print axioms np28
#print axioms np29
#print axioms np30
#print axioms np31
#print axioms np32
#print axioms np33
#print axioms np34
#print axioms np35
#print axioms np36
#print axioms np37
#print axioms np38
#print axioms np39
#print axioms np40
#print axioms np41
#print axioms np42
#print axioms np43
#print axioms np44
#print axioms np45
#print axioms np46
#print axioms np47
#print axioms np48
#print axioms np49
#print axioms np50
#print axioms np51
#print axioms np52
#print axioms np53
#print axioms np54
#print axioms np55
#print axioms np56
#print axioms np57
#print axioms np58
#print axioms np59
#print axioms prod_first59_nat
#print axioms prod_first59
#print axioms sum_first59
#print axioms sum_first58
#print axioms base_case
#print axioms card_filter_dvd_le
#print axioms sum_filter_comm
#print axioms pairavg_bound
#print axioms no_pinning
#print axioms no_pinning_isUnit
#print axioms A_sub_B
#print axioms collapse_identity
#print axioms regime_one_first
#print axioms regime_one_second
#print axioms square_lifts_to_prime_powers
#print axioms regime_one_first_mod
#print axioms four_two_eq_zero
#print axioms targets_agree_mod_eight
#print axioms plus_semiprime_identity
#print axioms plus_range
#print axioms plus_injective_aux
#print axioms plus_recover
#print axioms count_le_divisor_sum
#print axioms two_roots
#print axioms two_roots_quadratic
#print axioms card_large_le_card_small
#print axioms tau_le_two_small
#print axioms pyth_sum_of_squares
#print axioms pyth_discriminant
#print axioms split_identity
#print axioms split_product
#print axioms mass_ge_two_of_pythagorean
#print axioms mass_ge_two_of_pyth_support
#print axioms card_ge_59_of_pythagorean
#print axioms emptytest
#print axioms sum_ge_card_of_prod_eq_one
#print axioms two_le_sum_of_mul_eq_one
#print axioms card_ge_59_of_recipSum_ge_two
#print axioms card_union_ge_59_of_masses
#print axioms dprod
#print axioms csum
#print axioms dprod_div
#print axioms rigidity_coprime
#print axioms solution_structure
#print axioms forced39
#print axioms pool99
#print axioms rsum
#print axioms thr
#print axioms plusVal
#print axioms nsqB
#print axioms nsqB_false_of_isSquare
#print axioms rsum_nil
#print axioms rsum_cons
#print axioms rsum_append
#print axioms rsum_perm
#print axioms plusVal_perm
#print axioms inv_cast_le
#print axioms rsum_take_shift
#print axioms rsum_sublist_le
#print axioms sublist_of_pairwise_lt
#print axioms dfs
#print axioms dfs_sound
#print axioms list_prod_toList
#print axioms list_sum_toList
#print axioms prod_sort
#print axioms rsum_sort
#print axioms plusVal_sort
#print axioms csum_union_eq
#print axioms plus_square
#print axioms forced_mem
#print axioms elt_le_795
#print axioms forced39_facts
#print axioms pool99_complete
#print axioms forced39_complete
#print axioms forced39_card
#print axioms forced39_nodup
#print axioms forced39_sum
#print axioms forced39_coe
#print axioms pool99_pairwise
#print axioms pool99_pos
#print axioms dfs_run
#print axioms erdos307_sixty
#print axioms sieve_core
#print axioms sum_sq_expand
#print axioms square_sieve
#print axioms primeSquareSum_certificate
#print axioms good_density_pos
#print axioms squarefree_positive_density_of_bound
#print axioms deriv_thirty_mul_prime
#print axioms stratum_linear
#print axioms stratum_linear_conv
#print axioms stratum_sigma_lt
#print axioms stratum_sigma_defect
#print axioms stratum_M30
#print axioms Erdos307.KovicProp18.kovic_valid
#print axioms Erdos307.KovicProp18.kovic_step_invalid
#print axioms Erdos307.KovicProp18.kovic_step_invalid'
#print axioms Erdos307.StratumGeneral.stratum_sigma_lt_general
#print axioms Erdos307.StratumGeneral.stratum_sigma_mul
#print axioms Erdos307.StratumGeneral.stratum_sigma_defect_general
#print axioms Erdos307.StratumGeneral.stratum_sigma_lt_thirty
#print axioms tail_factor
#print axioms tail_quadratic
#print axioms tail_discriminant
#print axioms tail_bound
#print axioms tail_m_even
#print axioms tail_bound_sharp
#print axioms tail_discriminant_alpha
#print axioms Erdos307.Breeder.breeder_bilinear_iff
#print axioms Erdos307.Breeder.breeder_key
#print axioms Erdos307.Breeder.breeder_q_integral
#print axioms Erdos307.Breeder.breeder_integral
#print axioms tail_finite
#print axioms tail_value_sub_sq
#print axioms tail_value_mod_dvd
#print axioms hensel_lift_identity
#print axioms hensel_all_powers
#print axioms tail_no_local_obstruction
