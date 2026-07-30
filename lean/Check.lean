import Erdos307.Campaign
import Erdos307.Injective
import Erdos307.PairAvg
import Erdos307.SquareSieve
import Erdos307.RhoBarrier
import Erdos307.HalfLyap
import Erdos307.LyapFalse
import Erdos307.Rigidity
import Erdos307.Barrier
import Erdos307.Capstone
import Erdos307.Extremal
import Erdos307.Numeral
import Erdos307.Closed
import Erdos307.Sixty
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
