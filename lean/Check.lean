import Erdos307.Campaign
import Erdos307.Injective
import Erdos307.PairAvg
import Erdos307.SquareSieve
import Erdos307.RhoBarrier
import Erdos307.HalfLyap
import Erdos307.LyapFalse
import Erdos307.NoInvariant
import Erdos307.InfZero
import Erdos307.Congruential
import Erdos307.LiveSlot
import Erdos307.Squarefree
import Erdos307.Rigidity
import Erdos307.Barrier
import Erdos307.Capstone
import Erdos307.Extremal
import Erdos307.Numeral
import Erdos307.Closed
import Erdos307.Sixty
import Erdos307.Bridge
import Erdos307.Frame
import Erdos307.Ladder
import Erdos307.Mod8
import Erdos307.NoGain
import Erdos307.NoPlace
import Erdos307.NoPoly
import Erdos307.NormalForm
import Erdos307.PairLocal
import Erdos307.PlusThin
import Erdos307.Pythagorean
import Erdos307.FunctionField
open Erdos307
#print axioms rigidity_coprime
#print axioms solution_structure
#print axioms reciprocal_sum_gt_two
#print axioms recipSum58_lt_two
#print axioms recipSum59_gt_two
#print axioms barrier_numeric
#print axioms barrier_algebraic
#print axioms barrier
#print axioms recipSum_eq
#print axioms solution_disjoint
#print axioms erdos307_barrier
#print axioms nth_prime_le_orderEmb
#print axioms prod_first_primes_le
#print axioms recipSum_le_first_primes
#print axioms hRatio_of_extremal
#print axioms np59
#print axioms prod_first59_nat
#print axioms sum_first59
#print axioms sum_first58
#print axioms base_case
#print axioms hmono_all
#print axioms card_ge_59
#print axioms erdos307_barrier_closed
#print axioms dfs_sound
#print axioms erdos307_sixty

-- the campaign lemma (rem:campaign): one binary certificate per tail family
#print axioms Erdos307.jacobiSym_add_four_mul
#print axioms Erdos307.jacobiSym_A_eq_B

-- lem:sigmainj (the injectivity behind thm:pairavg)
#print axioms Erdos307.den_eq_of_coprime_cross
#print axioms Erdos307.dprod_eq_of_mass_eq
#print axioms Erdos307.csum_eq_of_mass_eq

-- thm:pairavg (counting skeleton)
#print axioms Erdos307.card_filter_dvd_le
#print axioms Erdos307.sum_filter_comm
#print axioms Erdos307.pairavg_bound
#print axioms Erdos307.eq_of_cross

-- the square sieve (thm:a9, cor:a9rate)
#print axioms Erdos307.sieve_core
#print axioms Erdos307.sum_sq_expand
#print axioms Erdos307.square_sieve

-- thm:rhobarrier
#print axioms Erdos307.card_ge_59_of_recipSum_ge_two
#print axioms Erdos307.card_union_ge_59_of_masses

-- thm:halflyap (elementary Lyapunov proof of the barrier)
#print axioms Erdos307.log_lt_half_sub
#print axioms Erdos307.delta_decreasing
#print axioms Erdos307.two_le_add_of_mul_eq_one
#print axioms criterion_fails_of_pos
#print axioms criterion_fails_of_nonpos
#print axioms no_lambda_works
#print axioms one_lt_sigmaN0
#print axioms sigmaN0_lt
#print axioms lyapunov_criterion_false
#print axioms half_works
#print axioms no_f_above_two
#print axioms mass_sum_threshold
#print axioms exists_f_of_injective
#print axioms increment_iff
#print axioms no_two_cycle_of_decreasing
#print axioms exists_block_sum_near
#print axioms infimum_zero
#print axioms const_increment_iterate
#print axioms two_nsmul_eq_zero_of_period_two
#print axioms no_period_two_of_two_nsmul_ne_zero
#print axioms zmod_two_mul_eq_zero_of_period_two
#print axioms lambda_eq_half
#print axioms live_slot_threshold
#print axioms threshold_bracket
#print axioms primeSquareSum_certificate
#print axioms good_density_pos
#print axioms squarefree_positive_density_of_bound

/-! ### Bridge -/
#print axioms Erdos307.two_cycle_iff_double_fixed
#print axioms Erdos307.ad_dprod
#print axioms Erdos307.dprod_ne_dprod
#print axioms Erdos307.bridge_forward
#print axioms Erdos307.disjoint_primeFactors_of_cycle
#print axioms Erdos307.bridge_backward
#print axioms Erdos307.mass_eq
#print axioms Erdos307.bridge

/-! ### Frame -/
#print axioms Erdos307.csum_insert_prime
#print axioms Erdos307.dprod_insert_prime
#print axioms Erdos307.frame_cycle
#print axioms Erdos307.frame_solve
#print axioms Erdos307.anatomy_on_support
#print axioms Erdos307.csum_eq_mul_recipSum
#print axioms Erdos307.anatomy_iff

/-! ### Ladder -/
#print axioms Erdos307.k_nonpos
#print axioms Erdos307.rung_cross
#print axioms Erdos307.rung_mass_indep
#print axioms Erdos307.rung_minus_one
#print axioms Erdos307.rung_parity_mixed
#print axioms Erdos307.rung_parity_odd
#print axioms Erdos307.k_determined

/-! ### Mod8 -/
#print axioms Erdos307.odd_sq_mod8
#print axioms Erdos307.cofactor_odd
#print axioms Erdos307.mod8_law
#print axioms Erdos307.prime_sums_congruent
#print axioms Erdos307.parity_law
#print axioms Erdos307.omega_even_of_even_derivative
#print axioms Erdos307.not_both_even
#print axioms Erdos307.dprod_odd
#print axioms Erdos307.derivative_mod8
#print axioms Erdos307.plus_quantity_mod8
#print axioms Erdos307.sq_values_mod8
#print axioms Erdos307.plus_hit_residue
#print axioms Erdos307.odd_sq_sub_one_dvd
#print axioms Erdos307.mod8_law_int
#print axioms Erdos307.mixed_member_mod16
#print axioms Erdos307.even_member_mod16
#print axioms Erdos307.mixed_prime_sum_mod8

/-! ### NoGain -/
#print axioms Erdos307.cycle_product
#print axioms Erdos307.le_max_of_both
#print axioms Erdos307.cycle_bound
#print axioms Erdos307.cycle_bound_max
#print axioms Erdos307.gain_lt_one_order
#print axioms Erdos307.nogain

/-! ### NoPlace -/
#print axioms Erdos307.not_descends_of_le
#print axioms Erdos307.der_thirty
#print axioms Erdos307.not_descent_of_strictMono
#print axioms Erdos307.padic_lowers_on_support
#print axioms Erdos307.raises_two
#print axioms Erdos307.raises_three
#print axioms Erdos307.raises_five
#print axioms Erdos307.not_descent_padic
#print axioms Erdos307.no_place_descent

/-! ### NoPoly -/
#print axioms Erdos307.const_prod_eq_one_of_tendsto
#print axioms Erdos307.eps_eq_zero_of_identity
#print axioms Erdos307.nonconstant_empty
#print axioms Erdos307.nopoly

/-! ### NormalForm -/
#print axioms Erdos307.dvd_sum_erase_iff
#print axioms Erdos307.Q_determined
#print axioms Erdos307.oneprime_forced
#print axioms Erdos307.oneprime_cycle
#print axioms Erdos307.oneprime_mass_identity
#print axioms Erdos307.oneprime_mass_bound
#print axioms Erdos307.slot_layers
#print axioms Erdos307.slot_recovery
#print axioms Erdos307.qr_filter

/-! ### PairLocal -/
#print axioms Erdos307.no_pinning
#print axioms Erdos307.no_pinning_isUnit
#print axioms Erdos307.A_sub_B
#print axioms Erdos307.collapse_identity
#print axioms Erdos307.regime_one_first
#print axioms Erdos307.regime_one_second
#print axioms Erdos307.regime_one_first_mod
#print axioms Erdos307.four_two_eq_zero
#print axioms Erdos307.targets_agree_mod_eight

/-! ### PlusThin -/
#print axioms Erdos307.plus_semiprime_identity
#print axioms Erdos307.plus_range
#print axioms Erdos307.plus_injective_aux
#print axioms Erdos307.plus_recover
#print axioms Erdos307.count_le_divisor_sum
#print axioms Erdos307.two_roots
#print axioms Erdos307.two_roots_quadratic
#print axioms Erdos307.card_large_le_card_small
#print axioms Erdos307.tau_le_two_small

/-! ### Pythagorean -/
#print axioms Erdos307.pyth_sum_of_squares
#print axioms Erdos307.pyth_discriminant
#print axioms Erdos307.split_identity
#print axioms Erdos307.split_product
#print axioms Erdos307.mass_ge_two_of_pythagorean
#print axioms Erdos307.card_ge_59_of_pythagorean
#print axioms Erdos307.sum_ge_card_of_prod_eq_one
#print axioms Erdos307.two_le_sum_of_mul_eq_one

/-! ### FunctionField -/
#print axioms Erdos307.deg_drop_of_terms
#print axioms Erdos307.no_two_cycle_of_drop
#print axioms Erdos307.no_fixed_point_of_drop
#print axioms Erdos307.ff_no_cycle
