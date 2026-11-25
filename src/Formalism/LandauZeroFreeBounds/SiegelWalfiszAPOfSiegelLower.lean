module

import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Positivity
public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InRegionMono

@[expose] public section

open Complex hiding log exp
open Real Set Filter MeasureTheory Metric Topology Asymptotics LSeries DirichletCharacter ArithmeticFunction Finset
open Iff (mp mpr)
open Eventually (of_forall)
open scoped ArithmeticFunction.Moebius ComplexConjugate ComplexOrder
namespace Formalism.ZeroFreeDirichlet

variable {q : ℕ} [NeZero q]

private lemma norm_mellin_tail_le {A B : ℝ} {F : ℂ → ℂ} {s : ℂ} {g : ℝ → ℂ} (hA : 0 < A) (hF : Differentiable ℂ F) (hm : Measurable g)
    (hb : ∀ x, ‖g x‖ ≤ B) (he : ∀ z, 1 < re z → F z = z * ∫ t in Ioi A, g t * t ^ (-z - 1))
    (hs : 0 < re s) : ‖F s‖ ≤ B * (‖s‖ / re s) * A ^ (-re s) := by
  have hFb x : ‖indicator (Ioi A) g x‖ ≤ B := (norm_indicator_le_norm_self _ _).trans <| hb x
  have hI z : ∫ t in Ioi A, g t * t ^ (-z - 1) = mellin (indicator (Ioi A) g) (-z) := by
    rw [mellin, ← indicator_smul, setIntegral_indicator measurableSet_Ioi, mpr inter_eq_right <| Ioi_subset_Ioi hA.le]
    ring
  rw [AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (fun z _ => hF.analyticAt z)
    (DifferentiableOn.analyticOnNhd (fun z hz => by
      simp_rw [hI]
      have := mellin_differentiableAt_of_isBigO_rpow (s := -z) (a := 0)
        ((memLp_top_of_bound (hm.indicator measurableSet_Ioi).aestronglyMeasurable B <| of_forall hFb).locallyIntegrable le_top |>.locallyIntegrableOn _)
        (isBigO_of_le' _ fun x => by aesop)
        (by simp_all)
        (IsBigO.of_bound' <| by filter_upwards [Ioo_mem_nhdsGT hA] with x hx
                                simp [mpr not_lt hx.2.le])
        (sub_one_lt _)
      fun_prop) <| isOpen_lt continuous_const continuous_re) (convex_halfSpace_re_gt 0).isPreconnected (by norm_num)
    (((continuous_re.tendsto 2).eventually <| eventually_gt_nhds <| by norm_num).mono he) hs, norm_mul]
  grw [norm_integral_le_of_norm_le ((integrableOn_Ioi_cpow_of_lt (by simp
                                                                     linarith) hA).norm.const_mul B)
      (of_forall fun x => norm_mul_le_of_le (hb x) le_rfl),
    integral_const_mul, setIntegral_congr_fun measurableSet_Ioi fun t ht => norm_cpow_eq_rpow_re_of_pos (hA.trans ht) _,
    integral_Ioi_rpow_of_lt (by simp
                                linarith) hA]
  simp
  grind

private lemma norm_zeta_sub_pole_sub_one_le {s : ℂ} (hs : 0 < re s) : ‖riemannZeta₀ s - 1‖ ≤ ‖s‖ / re s := by
  have hfb (x : ℝ) : ‖ofReal (Int.fract x)‖ ≤ 1 := by
    simp
    grind [Int.abs_fract, Int.fract_lt_one]
  have := norm_mellin_tail_le zero_lt_one (differentiable_riemannZeta₀.const_sub 1) (by fun_prop) hfb ?_ hs
  · simpa [norm_sub_rev] using this
  intro z hz
  have h := LSeries_one_eq_riemannZeta hz ▸ LSeries_eq_mul_integral' 1 zero_le_one hz (by aesop)
  rw [(setIntegral_congr_fun measurableSet_Ioi fun x hx => by
        have hx0 := lt_trans zero_lt_one hx.out
        simp [Int.fract, ← Int.natCast_floor_eq_floor hx0.le, neg_add_eq_sub, cpow_sub _ _ <| mpr ofReal_ne_zero hx0.ne']
        field).trans <| integral_sub (integrableOn_Ioi_cpow_of_lt (by simpa) zero_lt_one)
      ((integrableOn_Ioi_cpow_of_lt (a := -z - 1) (by simp
                                                      linarith) zero_lt_one).bdd_mul
        (by fun_prop) <| of_forall hfb),
    integral_Ioi_cpow_of_lt (by simpa) zero_lt_one] at h
  simp at *
  grind [riemannZeta₀, one_re]

private lemma norm_lfunction_sub_partial_sum_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < re s) {N : ℕ} (hN : 1 ≤ N) :
    ‖LFunction χ s - ∑ n ∈ range (N + 1), term (χ ·) s n‖ ≤ 2 * q * (‖s‖ / re s) * N ^ (-re s) := by
  have hS (m : ℕ) : ∑ k ∈ Icc 1 m, (if N < k then χ k else 0) = ∑ k ∈ range (max m N + 1) \ range (N + 1), χ k := by
    rw [← sum_filter]
    congr
    grind
  have hc (m : ℕ) : ‖∑ k ∈ range m, χ k‖ ≤ q := by
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      by_cases h : m < q
      · grw [norm_sum_le_of_le _ fun k _ => norm_le_one χ _]
        simpa using h.le
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le <| not_lt.1 h
      rw [sum_range_add, show ∑ k ∈ range q, χ k = 0 by
        rw [← MulChar.sum_eq_zero_of_ne_one hχ]
        exact sum_nbij' (↑) ZMod.val (by simp) (by grind) (by simp +contextual [Nat.mod_eq_of_lt]) (by simp) <| by simp, zero_add]
      simpa using ih m <| lt_add_of_pos_left _ <| NeZero.pos q
  have hb (m : ℕ) : ‖∑ k ∈ Icc 1 m, if N < k then χ k else 0‖ ≤ 2 * q := by
    grw [hS, sum_sdiff_eq_sub <| range_subset_range.2 <| by lia, norm_sub_le, hc, hc]
    linarith
  refine norm_mellin_tail_le (mpr Nat.cast_pos hN) ((differentiable_LFunction hχ).fun_sub (Differentiable.fun_sum fun n _ s => (hasDerivAt_term _ n s).differentiableAt)) (by fun_prop) (fun t => hb ⌊t⌋₊) (fun z hz => ?_) hs
  rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi (mpr Nat.one_le_cast hN))
      fun t ht => by simp at ht
                     simp [hS, Nat.floor_le_of_le ht.2],
    ← neg_add', ← LSeries_eq_mul_integral _ le_rfl (by linarith) (LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n _ => by split_ifs <;> simp [norm_le_one]) hz) <| isBigO_of_le' _ fun n => by simpa using hb n,
    LFunction_eq_LSeries χ hz, LSeries, LSeries, ← (LSeriesSummable_of_one_lt_re χ hz).sum_add_tsum_compl,
    add_sub_cancel_left, _root_.tsum_subtype]
  exact tsum_congr fun n => by simp [term, indicator_apply]
                               grind

private lemma norm_von_mangoldt_lseries_near_one_le : ∃ δ > 0, ∀ (a : ℕ → ℂ) (s : ℂ), (∀ n, ‖a n‖ ≤ 1) → 1 < re s → re s < 1 + δ →
    ‖LSeries (a * fun n => (Λ n : ℂ)) s‖ ≤ 1 / (re s - 1) + 2 := by
  obtain ⟨δ, hδ, h⟩ := mp Metric.eventually_nhds_iff <| mp eventually_nhdsWithin_iff <|
    log_deriv_riemannZeta_add_inv_sub_sub_isLittleO.bound one_pos
  refine ⟨δ, hδ, fun a s ha hs hs2 => ?_⟩
  have h1 : 1 < re (re s : ℂ) := by simpa
  refine (tsum_of_norm_bounded (hasSum_re (LSeries_vonMangoldt_eq_deriv_riemannZeta_div h1 ▸ (LSeriesSummable_vonMangoldt h1).LSeriesHasSum)) fun n => (norm_term_le s <| by simpa using mul_le_of_le_one_left (norm_nonneg (Λ n : ℂ)) <| ha n).trans
    ((norm_term_le_of_re_le_re _ (by simp) n).trans (re_eq_norm.2 <| term_nonneg (by simp) _).symm.le)).trans ?_
  have h4 := neg_le_of_abs_le ((abs_re_le_norm _).trans (h (y := re s) (by simp [Complex.dist_eq, ← ofReal_one, ← ofReal_sub, abs_of_pos (sub_pos.2 hs)]
                                                                           linarith) (by aesop)))
  simp [← ofReal_one, ← ofReal_sub, neg_div] at h4 ⊢
  linarith [one_half_lt_eulerMascheroniConstant]

private noncomputable def regularizedLFunction (ψ : DirichletCharacter ℂ q) : ℂ → ℂ := if ψ = 1 then LFunctionTrivChar₁ q else LFunction ψ

private lemma regularizedLFunction_differentiable (ψ : DirichletCharacter ℂ q) : Differentiable ℂ (regularizedLFunction ψ) := by
  unfold regularizedLFunction
  split_ifs with h
  exacts [differentiable_LFunctionTrivChar₁ q, differentiable_LFunction h]

private lemma regularizedLFunction_log_deriv (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < re s) :
    LSeries ((fun n : ℕ => ψ n) * fun n => (Λ n : ℂ)) s = -logDeriv (regularizedLFunction ψ) s + if ψ = 1 then (s - 1)⁻¹ else 0 := by
  have h1 : s ≠ 1 := by aesop
  have h2 := LFunction_ne_zero_of_one_le_re ψ (.inr h1) hs.le
  rw [LSeries_twist_vonMangoldt_eq ψ hs, ← deriv_LFunction_eq_deriv_LSeries ψ hs, ← LFunction_eq_LSeries ψ hs]
  unfold regularizedLFunction
  split_ifs with h
  · simp [logDeriv_apply, deriv_LFunctionTrivChar₁_apply_of_ne_one, h1]
    grind
  simp [logDeriv_apply, neg_div]

private lemma regularizedLFunction_lower_bound (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < re s) (hs2 : re s ≤ 2) :
    (re s - 1) ^ 2 / 3 ≤ ‖regularizedLFunction ψ s‖ := by
  have h1 : s ≠ 1 := by aesop
  have hb : 1 ≤ ‖LFunction ψ s‖ * re (riemannZeta <| re s) := by
    rw [← norm_one (α := ℂ), ← LSeries.mul_mu_eq_one ψ hs, LFunction_eq_LSeries ψ hs, norm_mul]
    gcongr
    exact tsum_of_norm_bounded (hasSum_re <| LSeriesHasSum_one <| by simpa) fun n =>
      (norm_term_le s <| by simp
                            exact (mul_le_mul (norm_le_one ψ n) (by exact_mod_cast abs_moebius_le_one) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)).trans
        ((norm_term_le_of_re_le_re _ (by simp) n).trans (re_eq_norm.2 <| term_nonneg (by simp) _).symm.le)
  have h0 : 0 < re s := by linarith
  have hR : re (riemannZeta <| re s) * (re s - 1) ≤ 3 := by
    have hz := (re_le_norm _).trans (norm_zeta_sub_pole_sub_one_le (s := re s) (by simpa))
    simp [riemannZeta_eq_inv_sub_add, hs.ne', ← ofReal_one, ← ofReal_sub, add_mul, sub_ne_zero, abs_of_pos h0, h0.ne'] at hz ⊢
    nlinarith
  have h5 : re s - 1 ≤ 3 * ‖LFunction ψ s‖ := by nlinarith [norm_nonneg <| LFunction ψ s]
  unfold regularizedLFunction
  split_ifs with h
  · subst h
    simp [h1]
    have := re_le_norm <| s - 1
    simp at this
    nlinarith
  nlinarith

private lemma regularizedLFunction_growth (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 / 2 ≤ re s) : ‖regularizedLFunction ψ s‖ ≤ 3 * q * (‖s‖ + 1) ^ 2 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hs' : ‖s‖ / re s ≤ 2 * ‖s‖ := by rw [div_le_iff₀ (by linarith)]
                                        nlinarith [norm_nonneg s]
  unfold regularizedLFunction
  split_ifs with h
  · obtain ⟨P, hP, e⟩ : ∃ P : ℂ, ‖P‖ ≤ q ∧ LFunctionTrivChar₁ q s = P * (s + (s - 1) * (riemannZeta₀ s - 1)) := by
      refine ⟨∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)), (Finset.norm_prod_le _ _).trans <| (prod_le_prod₀ (fun _ _ => norm_nonneg _) fun p hp => ?_).trans <|
        (Nat.cast_prod _ _).symm.trans_le (Nat.cast_le.2 (Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q))), ?_⟩
      · have := (Nat.prime_of_mem_primeFactors hp).two_le
        grw [norm_sub_le, norm_natCast_cpow_le_norm_natCast_cpow_of_pos (by lia) (z := 0) (by simp; linarith)]
        norm_num [this]
      rcases eq_or_ne s 1 with rfl | h1
      · simp [cpow_neg_one]
      simp [h1, LFunctionTrivChar_eq_mul_riemannZeta, riemannZeta_eq_inv_sub_add]
      grind
    rw [e, norm_mul]
    grw [hP, norm_add_le, norm_mul, norm_sub_le s 1, norm_zeta_sub_pole_sub_one_le <| by linarith, hs', norm_one]
    nlinarith [norm_nonneg s]
  have := norm_lfunction_sub_partial_sum_le h (by linarith : 0 < re s) le_rfl
  simp [sum_range_succ] at this
  grw [norm_le_norm_sub_add (LFunction ψ s) 1, this, hs', norm_one]
  nlinarith [sq_nonneg ‖s‖]

private lemma regularizedLFunction_ne_zero (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 ≤ re s) : regularizedLFunction ψ s ≠ 0 := by
  unfold regularizedLFunction
  split_ifs with h
  · rcases eq_or_ne s 1 with rfl | h1
    · exact LFunctionTrivChar₁_apply_one_ne_zero q
    simp [h1, sub_eq_zero, LFunction_ne_zero_of_one_le_re _ (.inr h1) hs]
  exact LFunction_ne_zero_of_one_le_re _ (.inl h) hs

private lemma norm_log_deriv_le {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball c R))
    (h0 : ∀ z ∈ ball c R, f z ≠ 0) (hb : ∀ z ∈ ball c R, ‖f z‖ ≤ ‖f c‖ * rexp M) {z : ℂ} (hz : ‖z - c‖ ≤ R / 2) :
    ‖logDeriv f z‖ ≤ 24 * M / R := by
  obtain ⟨g, hg0, hg⟩ := ((hf.deriv isOpen_ball).div hf h0).isExactOn_ball.with_val_at c 0
  have hgd : DifferentiableOn ℂ g _ := fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
  obtain ⟨k, hk, hfg⟩ := mp (logDeriv_eqOn_iff hf hgd.cexp isOpen_ball isPreconnected_ball
    (by simp) h0) fun z hz => by simp [logDeriv_apply, (hg z hz).cexp.deriv]
  rw [logDeriv, ← (hg z <| mem_ball_iff_norm.2 <| by linarith).deriv]
  refine (norm_deriv_le_of_forall_mem_sphere_norm_le (R := R / 4) (by positivity) (hgd.diffContOnCl_ball <| closedBall_subset_ball' <| by rw [Complex.dist_eq]
                                                                                                                                          linarith) (C := 6 * M) fun w hw => ?_).trans_eq <| by ring
  have := mem_sphere_iff_norm.1 hw
  have := norm_sub_le_norm_sub_add_norm_sub w z c
  have := borelCaratheodory_zero (f := fun w => g <| c + w) hM
    (hgd.comp (by fun_prop) fun w hw => by simp_all) (fun w hw => ?_) hR (mem_ball_zero_iff.2 <| by linarith) <| by simpa
  · simp at this
    refine this.trans ?_
    rw [div_le_iff₀ <| by linarith]
    nlinarith
  have h1 := hb (c + w) <| by simpa using hw
  rw [hfg <| by simp_all, hfg <| mem_ball_self hR] at h1
  simpa [norm_exp, hk, hg0] using h1
private lemma landau_zero_sum_le {f : ℂ → ℂ} (c : ℂ) (M : ℝ) (hd : Differentiable ℂ f)
    (hb : ∀ w ∈ closedBall c 0.37182818286, ‖f w‖ ≤ ‖f c‖ * rexp M) (hz : ∀ p, re c ≤ re p → f p ≠ 0)
    (S : Finset ℂ) (hS : ∀ q ∈ S, dist c q ≤ 0.1 ∧ f q = 0) :
    ∑ q ∈ S, re (c - q)⁻¹ - re (logDeriv f c) ≤ 240 * (M + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt M
  induction n generalizing f M S
  all_goals
    have hM := hb c <| by norm_num
    simp [hz c le_rfl] at hM
    push_cast at hn
  · linarith
  next n ih =>
    by_cases hp : ∃ p, dist c p ≤ 0.1 ∧ f p = 0
    · obtain ⟨p, hr, hzero⟩ := hp
      have hre : 0 ≤ re (c - p)⁻¹ := by
        simp
        exact div_nonneg (by grind) <| normSq_nonneg _
      obtain ⟨g, hg, rfl⟩ : ∃ g, Differentiable ℂ g ∧ (· - p) * g = f :=
        ⟨_, differentiableOn_univ.1 ((differentiableOn_dslope univ_mem).2 hd.differentiableOn),
          funext (sub_smul_dslope_of_zero hzero)⟩
      simp at hz hS
      have := ih (M - 1) hg (fun w hw => norm_le_of_forall_mem_frontier_norm_le isBounded_closedBall
        hg.diffContOnCl (fun u hu => by
          simp [frontier_closedBall', ← Complex.dist_eq] at hu hb
          specialize hb u hu.le
          grw [← (by linarith [dist_triangle_right u c p] : dist u c - dist c p ≤ dist u p), hu, hr] at hb
          grw [Real.exp_sub, exp_one_lt_d9]
          norm_num at hb ⊢
          linarith)
        (by simpa)) (by grind) (S.erase p) (fun q hq => by grind) <| by linarith
      rw [logDeriv_mul] <;> simp_all [logDeriv_apply, hg c]
      by_cases hpS : p ∈ S
      · rw [← add_sum_erase S _ hpS]
        linarith
      · rw [erase_eq_of_notMem hpS] at this
        linarith
    · push Not at hp
      rw [sum_eq_zero fun q hq => (hp q (hS q hq).1 (hS q hq).2).elim]
      have := norm_log_deriv_le (R := 0.1) (M := M + 1) (by norm_num) (by linarith)
        hd.differentiableOn
        (fun z hz => hp z (mem_ball'.1 hz).le)
        (fun z hz => (hb z (by simp at hz ⊢
                               linarith)).trans (by simp_all)) (z := c) (by norm_num)
      norm_num at this
      linarith [(abs_le.1 <| abs_re_le_norm <| logDeriv f c).1]

private lemma regularizedLFunction_growth_ratio (ψ : DirichletCharacter ℂ q) {z w : ℂ} {d D : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hz : re z = 1 + d)
    (hw : ‖w‖ ≤ 1 / 2) (hD : q * (‖z‖ + 2) ≤ D) : ‖regularizedLFunction ψ (z + w)‖ ≤ ‖regularizedLFunction ψ z‖ * (9 * D ^ 2 / d ^ 2) := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.2 NeZero.one_le
  refine (regularizedLFunction_growth ψ <| by simp
                                              linarith [(abs_le.1 <| abs_re_le_norm w).1]).trans ?_
  calc _ ≤ 3 * D ^ 2 := by nlinarith [pow_le_pow_left₀ (by positivity) (by nlinarith [norm_add_le z w] : q * (‖z + w‖ + 1) ≤ D) 2]
    _ ≤ _ := by rw [mul_div_assoc', le_div_iff₀ <| by positivity]
                nlinarith [hz ▸ regularizedLFunction_lower_bound ψ (by linarith) <| by linarith]

private lemma trigonometric_polynomial_nonneg (w : ℂ) (hw : ‖w‖ ≤ 1) : 0 ≤ re (3 + 4 * w + w ^ 2) := by
  simp [sq]
  nlinarith [sq_nonneg (w.re + 1), norm_nonneg w, Complex.sq_norm w, normSq_apply w]

private theorem regularizedLFunction_zero_free : ∃ c > 0, ∃ L₀ : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) (L : ℝ),
    L₀ ≤ L → q * (|ρ.im| + 2) ≤ rexp L → 1 - c / L ≤ ρ.re → regularizedLFunction χ ρ = 0 → χ ^ 2 = 1 ∧ χ ≠ 1 ∧ ρ.im = 0 := by
  obtain ⟨δ₀, hδ₀, hv⟩ := norm_von_mangoldt_lseries_near_one_le
  obtain ⟨r₁, hr₁, hζ⟩ := Metric.eventually_nhds_iff.1 riemannZeta_eventually_ne_zero_nhds_one
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 <| (tendsto_exp_div_pow_atTop 2).eventually_ge_atTop 4e9
  refine ⟨80000⁻¹, by norm_num, max L₀ <| max 1 <| max δ₀⁻¹ (r₁ ^ 2)⁻¹, fun q _ χ ρ L hL hρL hβ hρ => ?_⟩
  simp at hL
  obtain ⟨hL0, hL1, hLδ, hLr⟩ := hL
  generalize hγd : ρ.im = γ at *
  rw [div_eq_mul_inv _ L] at hβ
  generalize hd : L⁻¹ / 10000 = d
  generalize hs : 1 + d + γ * I = s
  have hd0 : 0 < d := by bound
  have := inv_le_one_of_one_le₀ hL1
  have hβ1 : ρ.re < 1 := lt_of_not_ge fun h => regularizedLFunction_ne_zero χ h hρ
  have hu0 : 0 < 1 + d - ρ.re := by linarith
  have hu : 8 / 9 * d⁻¹ ≤ re (s - ρ)⁻¹ := hs ▸ by
    simp [normSq_apply, hγd]
    exact (inv_anti₀ hu0 (by linarith : 1 + d - ρ.re ≤ 9 / 8 * d)).trans_eq' <| by ring
  have hn1 : dist s ρ ≤ 0.1 := hs ▸ by
    rw [dist_eq_re_im, sqrt_le_left <| by norm_num]
    simp
    nlinarith
  by_contra H
  obtain ⟨S, hS, hX⟩ : ∃ S : Finset ℂ, (∀ w ∈ S, dist s w ≤ 0.1 ∧ regularizedLFunction χ w = 0) ∧
      re (s - ρ)⁻¹ + (if χ = 1 then d / (d ^ 2 + γ ^ 2) else 0) + (if χ ^ 2 = 1 then d / (d ^ 2 + (γ + γ) ^ 2) else 0) / 4 ≤
        ∑ w ∈ S, re (s - w)⁻¹ + 9 := by
    by_cases hg : d ≤ γ ^ 2 ∨ χ ^ 2 ≠ 1
    · refine ⟨{ρ}, by simp_all, ?_⟩
      rw [sum_singleton]
      rcases hg with hg | hg
      · split_ifs <;> linarith [div_le_one_of_le₀ (by nlinarith : d ≤ d ^ 2 + γ ^ 2) (by positivity), div_le_one_of_le₀ (by nlinarith : d ≤ d ^ 2 + (γ + γ) ^ 2) (by positivity)]
      · split_ifs <;> simp_all
    push Not at hg
    obtain ⟨hg, hc2⟩ := hg
    by_cases hc1 : χ = 1
    · have hρ1 : ρ ≠ 1 := by aesop
      simp [hc1, regularizedLFunction, LFunctionTrivChar_eq_mul_riemannZeta hρ1, sub_eq_zero, hρ1, prod_eq_zero_iff, hζ (y := ρ) (by
        rw [Complex.dist_eq_re_im, Real.sqrt_lt' hr₁]
        simp [hγd]
        nlinarith [inv_le_of_inv_le₀ (by positivity) hLr])] at hρ
      obtain ⟨p, hp, h⟩ := hρ
      have := (norm_natCast_cpow_le_norm_natCast_cpow_iff hp.1.one_lt (w := 0) (z := -ρ)).1 (by simp_all)
      simp at this
      linarith
    have hbn : dist s (conj ρ) ≤ 0.1 := hs ▸ by
      rw [dist_eq_re_im, sqrt_le_left <| by norm_num]
      simp [hγd]
      nlinarith
    have hFL : regularizedLFunction χ (conj ρ) = 0 := by
      have hd := differentiable_LFunction hc1
      have key := AnalyticOnNhd.eq_of_eventuallyEq (hd.differentiableOn.analyticOnNhd isOpen_univ)
        ((Differentiable.differentiableOn fun x => differentiableAt_conj_conj_iff.2 (hd _)).analyticOnNhd isOpen_univ) (z₀ := 2) (g := conj ∘ LFunction χ ∘ conj) ?_
      · simpa [regularizedLFunction, hc1, congr_fun key <| conj ρ] using hρ
      filter_upwards [continuousAt_const.eventually_lt continuous_re.continuousAt (by norm_num : (1:ℝ) < re 2)] with z hz
      rw [Function.comp_apply, Function.comp_apply, LFunction_eq_LSeries χ hz, LFunction_eq_LSeries χ <| by simp_all, LSeries, LSeries, conj_tsum]
      congr 1 with n
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hc2 n with h | h | h <;>
        simp [term, hn, h, ← conj_cpow _ _ (natCast_arg ▸ pi_ne_zero.symm : (n : ℂ).arg ≠ π)]
    refine ⟨{ρ, conj ρ}, by simp_all, ?_⟩
    rw [sum_pair <| fun h => H ⟨hc2, hc1, hγd ▸ conj_eq_iff_im.1 h.symm⟩]
    have : d / (d ^ 2 + (γ + γ) ^ 2) ≤ 4 * re (s - conj ρ)⁻¹ := hs ▸ by
      simp [normSq_apply, hγd]
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) <| by nlinarith]
      nlinarith [mul_pos hd0 hu0]
    grind
  have LA := fun ψ c (hc : re c = 1 + d) (hi : |im c| ≤ |γ| + |γ|) =>
    landau_zero_sum_le c (L + L + L) (regularizedLFunction_differentiable ψ)
      (fun w hw => by
        simpa using (regularizedLFunction_growth_ratio ψ (D := 2 * rexp L) hd0 (by linarith) hc ((mem_closedBall_iff_norm.1 hw).trans (by norm_num)) (by nlinarith [norm_le_abs_re_add_abs_im c, abs_of_pos (show 0 < re c by linarith)])).trans (by
          gcongr
          rw [Real.exp_add, Real.exp_add, ← hd]
          field_simp
          nlinarith [(le_div_iff₀ <| by positivity).1 <| hL₀ L hL0]))
      fun p hp => regularizedLFunction_ne_zero ψ <| by linarith
  have hs1 : 1 < re s := by aesop
  have hs2 : 1 < re (s + γ * I) := by simp_all
  have h2 := LA χ s (hs ▸ by simp) (hs ▸ by simp) S hS
  have h3 := LA (χ ^ 2) (s + γ * I) (hs ▸ by simp) (by simpa [← hs] using abs_add_le γ γ) ∅ (by simp)
  have h1 := hv 1 (1 + d) (by simp) (by simp_all) <| by simp
                                                        linarith [inv_le_of_inv_le₀ hδ₀ hLδ]
  subst hs
  have h341 := (hasSum_re ((((LSeriesSummable_vonMangoldt (s := 1 + d) (by simp_all)).LSeriesHasSum.mul_left 3).add
      ((LSeriesSummable_twist_vonMangoldt χ hs1).LSeriesHasSum.mul_left 4)).add
      (LSeriesSummable_twist_vonMangoldt (χ ^ 2) hs2).LSeriesHasSum)).nonneg fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    convert (re_ofReal_mul (Λ n / (n * n ^ d)) _).ge.trans' (mul_nonneg (by positivity) (trigonometric_polynomial_nonneg (χ n / n ^ (γ * I)) (by simpa [norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)] using norm_le_one χ n))) using 2
    simp [hn, MulChar.pow_apply' χ two_ne_zero, cpow_add _ _ (Nat.cast_ne_zero.2 hn), ofReal_cpow (Nat.cast_nonneg n)]
    field_simp
  rw [regularizedLFunction_log_deriv χ hs1, regularizedLFunction_log_deriv (χ ^ 2) hs2] at h341
  split_ifs at h341 hX <;> simp [inv_re, normSq_apply, ← sq] at h341 h3 h1 <;> linarith [(re_le_norm _).trans h1, show d⁻¹ = 10000 * L from hd ▸ by field_simp]

private noncomputable def mellinKernel (x σ t : ℝ) : ℂ := let s := (σ + t * I : ℂ); x ^ s * (s * (s + 1))⁻¹

private lemma norm_mellin_denominator_le {σ t m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (h : m ≤ σ) : ‖((σ + t * I) * (σ + t * I + 1))⁻¹‖ ≤ m⁻¹ * (1 + t ^ 2)⁻¹ := by
  rw [norm_inv, ← mul_inv]
  refine inv_anti₀ (by positivity) <| le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  rw [Complex.sq_norm, normSq_mul, normSq_apply, normSq_apply]
  simp
  nlinarith [mul_le_mul h h hm.le <| hm.le.trans h, mul_le_mul hm1 hm1 hm.le zero_le_one, sq_nonneg <| t * t]

private lemma hasMellin_linear_weight {s : ℂ} (hs : 0 < re s) : HasMellin (fun t : ℝ => ((max (1 - t) 0 : ℝ) : ℂ)) s (s * (s + 1))⁻¹ := by
  have h1 := hasMellin_cpow_Ioc 0 <| by simpa
  have h2 := hasMellin_cpow_Ioc 1 (s := s) (by simp
                                               linarith)
  have := hasMellin_sub h1.1 h2.1
  rw [h1.2, h2.2, add_zero, one_div, one_div, inv_sub_inv (ne_zero_of_re_pos hs) (ne_zero_of_re_pos (s := s + 1) (by simp
                                                                                                                     linarith)),
    add_sub_cancel_left, one_div] at this
  refine ⟨(integrableOn_congr_fun (s := Ioi (0 : ℝ)) (fun t (ht : 0 < t) => ?_) measurableSet_Ioi).1 this.1,
    (setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_).symm.trans this.2⟩ <;>
  by_cases h : t ≤ 1 <;> simp [indicator, ht, h, (not_le.1 _).le]

private lemma mellin_kernel_integral {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    Integrable (mellinKernel x σ) ∧ (1 / (2 * π)) • ∫ t, mellinKernel x σ t = ((max (1 - x⁻¹) 0 : ℝ) : ℂ) := by
  have hm (t : ℝ) := hasMellin_linear_weight (s := σ + t * I) (by simpa)
  have hK := (integrable_inv_one_add_sq.const_mul _).mono' (Measurable.aestronglyMeasurable <| by fun_prop) <| of_forall fun t =>
      norm_mellin_denominator_le (lt_min hσ one_pos) (min_le_right _ _) <| min_le_left _ _
  refine ⟨hK.bdd_mul (c := x ^ σ) (Measurable.aestronglyMeasurable (by fun_prop)) (of_forall fun t => by simp [norm_cpow_eq_rpow_re_of_pos hx]), ?_⟩
  rw [← mellinInv_mellin_eq σ _ (inv_pos.2 hx) (hasMellin_linear_weight (by simpa)).1 (hK.congr (of_forall fun t => (hm t).2.symm)) (by fun_prop), mellinInv]
  simp only [(hm _).2, ofReal_inv, inv_cpow_ofReal_nonneg hx.le, cpow_neg, inv_inv, smul_eq_mul, mellinKernel]

private lemma smoothed_perron_formula {a : ℕ → ℂ} {σ x : ℝ} (hσ : 0 < σ) (ha : LSeriesSummable a σ) (hx : 0 < x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, a n * (1 - n / x) = (1 / (2 * π)) • ∫ t : ℝ, LSeries a (σ + t * I) * mellinKernel x σ t := by
  have hi := (mellin_kernel_integral hσ hx).1
  have hk n (hn : n ≠ 0) : (1 / (2 * π)) • ∫ t : ℝ, term a (σ + t * I) n * mellinKernel x σ t = a n * ((max (1 - n / x) 0 : ℝ) : ℂ) := by
    rw [← inv_div x, ← (mellin_kernel_integral hσ <| by positivity).2, mul_smul_comm, ← integral_const_mul]
    congr 2 with t
    simp only [mellinKernel, term_of_ne_zero hn]
    rw [ofReal_div, div_cpow_ofReal_nonneg hx.le n.cast_nonneg, ofReal_natCast]
    ring
  simp_rw [LSeries, ← tsum_mul_right]
  rw [← (integral_tsum_of_summable_integral_norm (F := fun n (t : ℝ) => term a (σ + t * I) n * mellinKernel x σ t)
    (fun n => hi.bdd_mul (c := ‖term a σ n‖) (Measurable.aestronglyMeasurable (by unfold term
                                                                                  split_ifs <;> fun_prop)) (of_forall fun t => by simp [norm_term_eq]))
    ((ha.norm.mul_right (∫ t, ‖mellinKernel x σ t‖)).congr fun n => by rw [← integral_const_mul]
                                                                       simp [norm_term_eq])), ← tsum_const_smul'', tsum_eq_sum fun n hn => ?_]
  · refine sum_congr rfl fun n hn => ?_
    simp at hn
    rw [hk n (by lia), max_eq_left (sub_nonneg.2 ((div_le_one hx).2 ((Nat.le_floor_iff hx.le).1 hn.2)))]
    simp
  · rcases eq_or_ne n 0 with rfl | h0
    · simp
    simp at hn
    rw [hk n h0, max_eq_right (sub_nonpos.2 ((one_le_div hx).2 (Nat.lt_of_floor_lt (hn (by lia))).le))]
    simp

private theorem smoothed_character_sum_bound : ∃ δ₀ > 0, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x η T : ℝ), 1 ≤ x → 0 < η → η < δ₀ →
    η ≤ 1 / 8 → 1 ≤ T → (∀ w, 1 - 3 * η < re w → |im w| < T + 1 → regularizedLFunction χ w ≠ 0) →
    ‖∑ n ∈ Icc 1 ⌊x⌋₊, (χ n * Λ n : ℂ) * (1 - n / x) - (if χ = 1 then (((x - 2 + 1 / x) / 2 : ℝ) : ℂ) else 0)‖ ≤
      6 * Real.log (9 * (q * (T + 5)) ^ 2 / η ^ 2) / η * (x ^ (1 - η) + x ^ (1 + η) / T) + 3 / η * x ^ (1 + η) / T := by
  obtain ⟨δ₀, hδ₀, hv⟩ := norm_von_mangoldt_lseries_near_one_le
  refine ⟨δ₀, hδ₀, fun q _ χ x η T hx hη hηδ hη1 hT hz => ?_⟩
  set b := 1 + η
  set a := 1 - η
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hTT : -T ≤ T := by linarith
  have hab : a ≤ b := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  set B := 6 * Real.log (9 * (q * (T + 5)) ^ 2 / η ^ 2) / η
  have hre (t : ℝ) : 1 < re (b + t * I) := by aesop
  have hFb (t : ℝ) : ‖logDeriv (regularizedLFunction χ) (b + t * I)‖ ≤ 3 / η := by
    have h1 := hv _ _ (fun n => norm_le_one χ n) (hre t) <| by simp
                                                               linarith
    rw [show re (b + t * I) - 1 = η by aesop] at h1
    rw [← norm_neg, eq_sub_of_add_eq (regularizedLFunction_log_deriv χ <| hre t).symm]
    grw [norm_sub_le, h1]
    split_ifs
    · grw [norm_inv, inv_anti₀ hη <| by simpa [b] using re_le_norm <| b + t * I - 1]
      field_simp
      linarith
    · rw [norm_zero]
      field_simp
      linarith
  have hF (s : ℂ) (h1 : a ≤ re s) (h2 : re s ≤ b) (h3 : |im s| ≤ T) :
      DifferentiableAt ℂ (logDeriv <| regularizedLFunction χ) s ∧ ‖logDeriv (regularizedLFunction χ) s‖ ≤ B :=
    ⟨((regularizedLFunction_differentiable χ).analyticAt s).deriv.differentiableAt.div (regularizedLFunction_differentiable χ s) (hz s (by linarith) (by linarith)), by
      set c := s + ((1 + η - re s : ℝ) : ℂ)
      have hr : re c = 1 + η := by aesop
      rw [show im s = im c by aesop] at h3
      have H (w : ℂ) (hw : w ∈ ball c (4 * η)) : 1 - 3 * η < re w ∧ |im w| < T + 1 ∧ ‖w - c‖ ≤ 1 / 2 := by
        have h0 := mem_ball_iff_norm.1 hw
        have h1 := abs_le.1 <| abs_re_le_norm <| w - c
        have h2 := abs_im_le_norm <| w - c
        simp [sub_re, hr, sub_im] at h1 h2
        grind
      refine (norm_log_deriv_le (by positivity) (Real.log_pos ?_) (regularizedLFunction_differentiable χ).differentiableOn (fun w hw => hz w (H w hw).1 (H w hw).2.1) (fun w hw => ?_) ?_).trans_eq (by ring)
      · rw [one_lt_div <| by positivity]
        nlinarith [show 5 ≤ q * (T + 5) by nlinarith]
      · rw [Real.exp_log]
        · simpa using regularizedLFunction_growth_ratio χ hη (by linarith) hr (H w hw).2.2
            (by nlinarith [norm_le_abs_re_add_abs_im c, abs_of_pos <| show 0 < re c by linarith])
        positivity
      · simp only [c, sub_add_cancel_left, norm_neg, norm_real, Real.norm_eq_abs, abs_le]
        grind⟩
  have hm : Measurable (logDeriv <| regularizedLFunction χ) := (measurable_deriv _).div (regularizedLFunction_differentiable χ).continuous.measurable
  set G : ℂ → ℂ := fun s => -logDeriv (regularizedLFunction χ) s * ((x : ℂ) ^ s * (s * (s + 1))⁻¹)
  have hB0 := (norm_nonneg _).trans (hF b (by simp_all) (by simp) <| by simp_all).2
  have hGb (σ t C : ℝ) (hσ : a ≤ σ) (hC : ‖logDeriv (regularizedLFunction χ) (σ + t * I)‖ ≤ C) : ‖G (σ + t * I)‖ ≤ C * x ^ σ * 2 * (1 + t ^ 2)⁻¹ := by
    have := norm_mellin_denominator_le (σ := σ) (t := t) (m := 1 / 2) (by norm_num) (by norm_num) (by linarith)
    simp [G, norm_cpow_eq_rpow_re_of_pos hx0]
    norm_num at this hC ⊢
    nlinarith [mul_le_mul hC this (by positivity) <| (norm_nonneg _).trans hC, rpow_pos_of_pos hx0 σ]
  have hb' (t : ℝ) := hGb _ t _ hab <| hFb t
  have hi := (integrable_inv_one_add_sq.const_mul _).mono'
    (Measurable.aestronglyMeasurable <| by fun_prop) <| of_forall hb'
  have P := smoothed_perron_formula (σ := b) (by linarith)
    (LSeriesSummable_twist_vonMangoldt χ (by simp_all)) hx0
  simp only [regularizedLFunction_log_deriv χ <| hre _, Pi.mul_apply] at P
  obtain ⟨i1, e1⟩ := mellin_kernel_integral hη hx0
  obtain ⟨i2, e2⟩ := mellin_kernel_integral (by linarith : 0 < b) hx0
  have e (t : ℝ) : (b + t * I - 1)⁻¹ * mellinKernel x b t = (x * mellinKernel x η t - mellinKernel x b t) / 2 := by
    have := ne_zero_of_re_pos (s := b + t * I - 1) (by simp_all)
    have := ne_zero_of_re_pos (s := b + t * I + 1) (by simp
                                                       linarith)
    simp only [mellinKernel]
    rw [show (η : ℂ) + t * I = b + t * I - 1 by simp [b]
                                                ring, sub_add_cancel, cpow_sub _ _ (by positivity), cpow_one]
    field_simp
    ring
  calc _ = ‖(1 / (2 * π)) • ∫ t : ℝ, G (b + t * I)‖ := ?_
    _ ≤ _ := ?_
  · congr 1
    split_ifs at P ⊢
    · rw [P]
      simp only [add_mul, e]
      erw [integral_add hi (((i1.const_mul _).sub i2).div_const _)]
      simp only [Pi.sub_apply]
      rw [smul_add, integral_div, integral_sub (i1.const_mul _) i2, integral_const_mul, ← smul_div_assoc, smul_sub, ← mul_smul_comm, e1, e2,
        max_eq_left <| sub_nonneg.2 <| inv_le_one_of_one_le₀ hx]
      push_cast
      field_simp
      ring_nf
    · simp [P, G, mellinKernel]
  have hrect := integral_boundary_rect_eq_zero_of_differentiableOn G (a - T * I) (b + T * I) ?_
  · simp at hrect
    have hA : ‖∫ y in -T..T, G (a + y * I)‖ ≤ 2 * π * (B * x ^ a) := by
      refine (intervalIntegral.norm_integral_le_of_norm_le hTT (of_forall fun y hy => hGb a y B le_rfl
        (hF _ (by simp) (by simp_all) (by simpa using abs_le.2 ⟨hy.1.le, hy.2⟩)).2)
        ((integrable_inv_one_add_sq.const_mul _).intervalIntegrable)).trans ?_
      simp
      nlinarith [arctan_lt_pi_div_two T, mul_nonneg hB0 (rpow_pos_of_pos hx0 a).le]
    have hH (y : ℝ) (hy : |y| = T) : ‖∫ t in a..b, G (t + y * I)‖ ≤ B * x ^ b * 2 * T⁻¹ := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_).trans <| mul_le_of_le_one_right (by positivity) <| abs_le.2 ⟨by linarith, by linarith⟩
      obtain ⟨h1, h2⟩ := uIoc_of_le hab ▸ ht
      refine (hGb t y B h1.le (hF _ (by simp
                                        linarith) (by simp_all) <| by simp_all).2).trans ?_
      rw [← sq_abs y, hy]
      gcongr
      nlinarith
    have hR : ‖∫ t in (Ioc (-T) T)ᶜ, G (b + t * I)‖ ≤ 4 * (3 / η * x ^ b) * T⁻¹ := by
      refine (norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _).integrableOn
        (of_forall hb')).trans ?_
      rw [integral_const_mul, eq_sub_of_add_eq' <| integral_add_compl measurableSet_Ioc integrable_inv_one_add_sq, ← intervalIntegral.integral_of_le hTT]
      simp
      nlinarith [(by positivity : (0:ℝ) ≤ 3 / η * x ^ b), arctan_inv_of_pos hT0, arctan_lt_self <| inv_pos.2 hT0]
    have e := congr_arg norm <| eq_sub_of_add_eq' <| sub_eq_zero.1 hrect
    have h1 := hH (-T) <| by simp_all
    simp [norm_I, one_mul, ofReal_neg, neg_mul] at e h1
    rw [norm_smul_of_nonneg <| by positivity, ← integral_add_compl measurableSet_Ioc hi, ← intervalIntegral.integral_of_le hTT,
      one_div, inv_mul_le_iff₀ <| by positivity]
    grw [norm_add_le, e, norm_sub_le, norm_mul, norm_I, one_mul, norm_sub_le, hA, h1, hH T <| by simp_all, hR]
    linear_combination 2 * mul_le_mul_of_nonneg_right two_le_pi (by positivity : (0:ℝ) ≤ (B + 3 / η) * x ^ b / T)
  · intro s hs
    simp [mem_reProdIm, uIcc_of_le hab, uIcc_of_le hTT] at hs
    have hd := (hF s hs.1.1 hs.1.2 <| abs_le.2 hs.2).1
    have := ne_zero_of_re_pos (s := s) (by linarith)
    have := ne_zero_of_re_pos (s := s + 1) (by simp
                                               linarith)
    exact (by fun_prop (disch := simp [*]) : DifferentiableAt ℂ G s).differentiableWithinAt

private lemma product_lfunction_lower_bound {χ₁ χ₂ : DirichletCharacter ℂ q} (h1 : χ₁ ^ 2 = 1) (h2 : χ₂ ^ 2 = 1) (h1' : χ₁ ≠ 1) (h2' : χ₂ ≠ 1)
    (hψ : χ₁ * χ₂ ≠ 1) {σ : ℝ} (hσ : 7 / 8 ≤ σ) (hσ1 : σ < 1) (hz : regularizedLFunction χ₁ σ = 0) (M : ℕ) :
    1 / 81 ≤ ‖regularizedLFunction χ₁ 1‖ * ‖regularizedLFunction χ₂ 1‖ * ‖regularizedLFunction (χ₁ * χ₂) 1‖ * ((2 - σ) ^ (M + 1) / (1 - σ)) + 18 * 10 ^ 7 * q ^ 3 * (3 / 4) ^ M := by
  set N := regularizedLFunction (1 : DirichletCharacter ℂ 1) * (regularizedLFunction χ₁ * regularizedLFunction χ₂ * regularizedLFunction (χ₁ * χ₂)) with hN
  have hNd : Differentiable ℂ N := (regularizedLFunction_differentiable _).mul <| ((regularizedLFunction_differentiable _).mul <| regularizedLFunction_differentiable _).mul <| regularizedLFunction_differentiable _
  have hN2 : 1 / 81 ≤ ‖N 2‖ := by
    rw [hN]
    simp only [Pi.mul_apply, norm_mul]
    calc (1:ℝ) / 81 = 1 / 3 * (1 / 3 * (1 / 3) * (1 / 3)) := by norm_num
      _ ≤ _ := by gcongr <;> convert regularizedLFunction_lower_bound _ (s := 2) (by norm_num) (by norm_num) <;> norm_num
  have hN0 : N 2 ≠ 0 := norm_pos_iff.1 <| by linarith
  set H := dslope N 1 with hH
  have hHd : Differentiable ℂ H := differentiableOn_univ.1 <| (differentiableOn_dslope univ_mem).2 hNd.differentiableOn
  set F : ℂ → ℂ := fun s => N s / (s - 1) / N 2 with hF
  have hq (χ : DirichletCharacter ℂ q) (h : χ ^ 2 = 1) (n : ℕ) : 0 ≤ 1 + χ n := by
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr h n with e | e | e <;> norm_num [e]
  set a : ℕ → ℂ := fun n => Λ n * (1 + χ₁ n) * (1 + χ₂ n) with ha
  have ha0 : 0 ≤ a := fun n => mul_nonneg (mul_nonneg (zero_le_real.2 vonMangoldt_nonneg) <| hq χ₁ h1 n) <| hq χ₂ h2 n
  have hA (s : ℂ) (hs : 1 < re s) : LSeriesHasSum a s
      (LSeries ((fun n : ℕ => (1 : DirichletCharacter ℂ 1) n) * fun n => (Λ n : ℂ)) s +
        LSeries ((fun n : ℕ => χ₁ n) * fun n => (Λ n : ℂ)) s +
        LSeries ((fun n : ℕ => χ₂ n) * fun n => (Λ n : ℂ)) s +
        LSeries ((fun n : ℕ => (χ₁ * χ₂) n) * fun n => (Λ n : ℂ)) s) := by
    unfold LSeriesHasSum
    convert ((((LSeriesSummable_twist_vonMangoldt (1 : DirichletCharacter ℂ 1) hs).LSeriesHasSum.add
      (LSeriesSummable_twist_vonMangoldt χ₁ hs).LSeriesHasSum).add
      (LSeriesSummable_twist_vonMangoldt χ₂ hs).LSeriesHasSum).add
      (LSeriesSummable_twist_vonMangoldt (χ₁ * χ₂) hs).LSeriesHasSum) using 1
    ext n
    simp [term, ha, MulChar.one_apply (isUnit_of_subsingleton _)]
    split_ifs <;> ring
  have hab : LSeries.abscissaOfAbsConv a < (2 : ℝ) := (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    fun y hy => (hA y <| by simpa).LSeriesSummable).trans_lt <| by exact_mod_cast (by norm_num : (1:ℝ) < 2)
  have hE (s : ℂ) (hs : 1 < re s) : HasDerivAt F (-LSeries a s * F s) s := by
    have hl (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) : HasDerivAt (regularizedLFunction χ) (logDeriv (regularizedLFunction χ) s * regularizedLFunction χ s) s := by
      rw [logDeriv_apply, div_mul_cancel₀ _ <| regularizedLFunction_ne_zero χ hs.le]
      exact (regularizedLFunction_differentiable χ s).hasDerivAt
    have hn1 : s - 1 ≠ 0 := sub_ne_zero.2 <| by aesop
    refine ((((hl 1 1).mul <| ((hl q χ₁).mul <| hl q χ₂).mul <| hl q <| χ₁ * χ₂).div ((hasDerivAt_id s).sub_const 1) hn1).div_const _).congr_deriv ?_
    rw [(hA s hs).LSeries_eq, regularizedLFunction_log_deriv _ hs, regularizedLFunction_log_deriv _ hs, regularizedLFunction_log_deriv _ hs, regularizedLFunction_log_deriv _ hs]
    simp [hF, hN, h1', hψ]
    grind
  have hFa := (show DifferentiableOn ℂ F {s | 1 < re s} from fun s hs => (hE s hs).differentiableAt.differentiableWithinAt).analyticOnNhd
    (isOpen_lt continuous_const continuous_re) 2 <| by norm_num
  have hpos (m : ℕ) : 0 ≤ (-1) ^ m * iteratedDeriv m F 2 := by
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases m with _ | m
      · norm_num [hF, hN0]
      rw [iteratedDeriv_succ', EqOn.iteratedDeriv_of_isOpen (g := -LSeries a * F) (fun s hs => (hE s hs).deriv) (isOpen_lt continuous_const continuous_re) m (show (1:ℝ) < re 2 by norm_num), neg_mul, iteratedDeriv_neg,
        iteratedDeriv_mul ((LSeries_analyticOnNhd a 2 <| by simp_all).contDiffAt) <| hFa.contDiffAt, mul_neg, ← neg_mul, mul_sum]
      exact sum_nonneg fun i hi => by
        rw [show m + 1 = i + (m - i) + 1 by simp_all]
        exact (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (LSeries.iteratedDeriv_alternating ha0 hab i)) (ih (m - i) (by lia))).trans_eq (by push_cast; ring)
  have e : H =ᶠ[𝓝 2] fun s => N 2 * F s - N 1 * (1 * s - 1)⁻¹ := by
    filter_upwards [eventually_ne_nhds (by norm_num : (2:ℂ) ≠ 1)] with s hs
    rw [hH, hF, dslope_of_ne _ hs, slope_def_field]
    field_simp
  have hNb (w : ℂ) (hw : ‖w - 2‖ ≤ 3 / 2) : ‖N w‖ ≤ 3 * (1:ℕ) * (9 / 2) ^ 2 * (3 * q * (9 / 2) ^ 2 * (3 * q * (9 / 2) ^ 2) * (3 * q * (9 / 2) ^ 2)) := by
    have h₁ := (abs_le.1 <| (abs_re_le_norm <| w - 2).trans hw).1
    have h₂ := norm_le_norm_sub_add w 2
    simp at h₁ h₂
    rw [hN, Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, norm_mul, norm_mul, norm_mul]
    gcongr <;> refine (regularizedLFunction_growth _ <| by linarith).trans ?_ <;> gcongr <;> linarith
  have hHb (s : ℂ) (hs : s ∈ sphere (2:ℂ) (3/2)) : ‖H s‖ ≤ 6 * 10 ^ 7 * q ^ 3 := by
    rw [mem_sphere_iff_norm] at hs
    have h1 : 1 / 2 ≤ ‖s - 1‖ := by linarith [norm_sub_le_norm_sub_add_norm_sub s 1 2, show ‖(1:ℂ) - 2‖ = 1 by norm_num]
    rw [hH, dslope_of_ne _ <| by rintro rfl
                                 norm_num at hs, slope_def_field, norm_div, div_le_iff₀ <| by linarith]
    nlinarith [norm_sub_le (N s) <| N 1, hNb s hs.le, hNb 1 <| by norm_num, (by positivity : (0:ℝ) ≤ q ^ 3)]
  set T : ℕ → ℂ := fun n => (n.factorial : ℂ)⁻¹ • ((σ:ℂ) - 2) ^ n • iteratedDeriv n H 2 with hTd
  have hT : HasSum T (H σ) := hasSum_taylorSeries_of_entire hHd 2 σ
  have hTn (n : ℕ) : ‖T n‖ ≤ 6 * 10 ^ 7 * q ^ 3 * (3 / 4) ^ n := by
    simp [hTd, norm_pow]
    refine (mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_left₀ (b := 9 / 8) (norm_nonneg _) ?_ n)
      (norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num) hHd.diffContOnCl hHb) (norm_nonneg _) <| by positivity) <| by positivity).trans_eq ?_
    · rw [← ofReal_ofNat, ← ofReal_sub, norm_real, norm_of_nonpos <| by linarith]
      linarith
    rw [show (9 / 8 : ℝ) = 3 / 4 * (3 / 2) by norm_num, mul_pow]
    field_simp
  have htail : ‖∑' i, T (i + (M + 1))‖ ≤ 18 * 10 ^ 7 * q ^ 3 * (3 / 4) ^ M :=
    (tsum_of_norm_bounded ((hasSum_geometric_of_lt_one (by norm_num) (by norm_num : (3 / 4 : ℝ) < 1)).mul_left
      (6 * 10 ^ 7 * q ^ 3 * (3 / 4) ^ (M + 1) : ℝ)) fun i => (hTn _).trans_eq <| by ring).trans_eq <| by ring
  have ht (n : ℕ) : T n = N 2 * ((n.factorial : ℂ)⁻¹ * (2 - σ) ^ n * ((-1) ^ n * iteratedDeriv n F 2)) - N 1 * (2 - σ) ^ n := by
    simp [hTd]
    rw [e.iteratedDeriv_eq, iteratedDeriv_fun_sub (contDiffAt_const.mul hFa.contDiffAt)
      (by fun_prop (disch := norm_num) : ContDiffAt ℂ n (fun s : ℂ => N 1 * (1 * s - 1)⁻¹) 2),
      iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate (f := fun s : ℂ => (1 * s - 1)⁻¹),
      iter_deriv_inv_linear_sub, show (σ:ℂ) - 2 = (2 - σ) * (-1) by ring, mul_pow]
    field_simp
    ring_nf
    simp
  have e' := hT.summable.sum_add_tsum_nat_add <| M + 1
  rw [hT.tsum_eq, hH, dslope_of_ne _ <| by exact_mod_cast hσ1.ne, slope_def_field, show N σ = 0 by simp_all, zero_sub, neg_div,
    ← div_neg, neg_sub, sum_congr rfl fun i _ => ht i, sum_sub_distrib, ← mul_sum, ← mul_sum, geom_sum_eq <| by norm_cast
                                                                                                                linarith] at e'
  rw [show ‖regularizedLFunction χ₁ 1‖ * ‖regularizedLFunction χ₂ 1‖ * ‖regularizedLFunction (χ₁ * χ₂) 1‖ = ‖N 1‖ by simp [hN, show regularizedLFunction (1 : DirichletCharacter ℂ 1) 1 = 1 by simp [regularizedLFunction]]]
  calc (1:ℝ) / 81 ≤ ‖N 2‖ * ‖∑ i ∈ range (M + 1), (i.factorial : ℂ)⁻¹ * (2 - σ) ^ i * ((-1) ^ i * iteratedDeriv i F 2)‖ :=
        hN2.trans (le_mul_of_one_le_right (norm_nonneg _) ((Complex.le_def.1 (le_trans (by norm_num [hF, hN0] : (1:ℂ) ≤ _) (single_le_sum (fun i _ => mul_nonneg
          (mul_nonneg (by positivity) (pow_nonneg (by norm_cast
                                                      linarith) i)) (hpos i)) (mem_range.2 (Nat.succ_pos M))))).1.trans (re_le_norm _)))
    _ = ‖N 1 * ((2 - σ) ^ (M + 1) / (1 - σ) : ℝ) - ∑' i, T (i + (M + 1))‖ := by rw [← norm_mul]
                                                                                push_cast
                                                                                grind
    _ ≤ _ := by
      grw [norm_sub_le, norm_mul, norm_real, norm_of_nonneg <| div_nonneg (pow_nonneg (by linarith) _) <| by linarith, htail]

private lemma lfunction_bound_near_one {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {r ℓ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 8) (hℓ : (q : ℝ) ≤ rexp ℓ) {z : ℂ}
    (hz : 1 - r ≤ re z) (hz2 : ‖z‖ ≤ 2) : ‖regularizedLFunction χ z‖ ≤ (7 + 1 / r) * rexp (r * ℓ) ^ 2 := by
  rw [show regularizedLFunction χ = LFunction χ from ite_eq_right hχ]
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hE := (rpow_le_rpow (by positivity) hℓ hr.le).trans_eq <| by rw [← exp_mul, mul_comm]
  have h2 : ‖∑ n ∈ range <| q + 1, term (χ ·) z n‖ ≤ q ^ r * harmonic q := by
    refine (norm_sum_le _ _).trans ((sum_le_sum (g := fun n : ℕ => (q : ℝ) ^ r * (n : ℝ)⁻¹) fun n hn => ?_).trans_eq
      (by simp [mul_sum, sum_range_succ', harmonic]))
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn0
    rw [norm_term_eq, ite_eq_right hn0]
    calc ‖χ n‖ / (n : ℝ) ^ re z ≤ 1 / (n : ℝ) ^ (1 - r) :=
          div_le_div₀ zero_le_one (norm_le_one χ _) (by positivity) <| rpow_le_rpow_of_exponent_le hn1 hz
      _ ≤ (q : ℝ) ^ r * (n : ℝ)⁻¹ := by
          rw [rpow_sub <| by linarith, rpow_one, one_div_div, div_eq_mul_inv]
          gcongr
          simp_all
  have h6 : rexp (r * ℓ) * ℓ ≤ 1 / r * rexp (r * ℓ) ^ 2 := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hr]
    nlinarith [add_one_le_exp <| r * ℓ, exp_pos <| r * ℓ]
  have hl := (log_le_iff_le_exp <| by linarith).2 hℓ
  have h7 := mul_le_mul_of_nonneg hE ((harmonic_le_one_add_log q).trans (by linarith : 1 + Real.log q ≤ 1 + ℓ))
    (by positivity) <| by linarith [log_nonneg hq]
  have h8 := mul_le_mul_of_nonneg_left ((one_le_rpow hq hr.le).trans hE) (exp_pos <| r * ℓ).le
  nlinarith [norm_le_norm_sub_add (LFunction χ z) (∑ n ∈ range <| q + 1, term (χ ·) z n), norm_lfunction_sub_partial_sum_le hχ (by linarith) <| NeZero.pos q,
    mul_le_mul (show ‖z‖ / re z ≤ 8 / 3 by rw [div_le_iff₀ (by linarith)]
                                           linarith) ((by rw [rpow_add <| by linarith, rpow_one] : (q : ℝ) * q ^ (-re z) = q ^ (1 + -re z)).trans_le
    (rpow_le_rpow_of_exponent_le hq (by linarith : 1 + -re z ≤ r))) (by positivity) (by positivity)]

private lemma lfunction_one_le_deriv_bound_mul {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {r ℓ β : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 8) (hℓ : (q : ℝ) ≤ rexp ℓ)
    (hβ : 1 - r / 2 ≤ β) (h0 : regularizedLFunction χ β = 0) : ‖regularizedLFunction χ 1‖ ≤ 2 / r * ((7 + 1 / r) * rexp (r * ℓ) ^ 2) * (1 - β) := by
  have hβ1 := lt_of_not_ge fun h => regularizedLFunction_ne_zero χ (by simpa) h0
  have e : ‖(1:ℂ) - β‖ = 1 - β := by rw [← ofReal_one, ← ofReal_sub, norm_real, norm_of_nonneg <| by linarith]
  have := Convex.norm_image_sub_le_of_norm_deriv_le (C := 2 / r * ((7 + 1 / r) * rexp (r * ℓ) ^ 2)) (fun w _ => regularizedLFunction_differentiable χ w)
    (fun w hw => ?_) (convex_closedBall (1 : ℂ) (r / 2)) (x := (β : ℂ)) (y := 1) (by rw [mem_closedBall, Complex.dist_eq, norm_sub_rev, e]
                                                                                     linarith)
    (mem_closedBall_self (by positivity))
  · simp_all
  refine (norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < r / 2) (regularizedLFunction_differentiable χ).diffContOnCl
    fun z hz => lfunction_bound_near_one hχ hr hr1 hℓ ?_ ?_).trans <| le_of_eq <| by field_simp
  all_goals
    rw [mem_closedBall, Complex.dist_eq] at hw
    rw [mem_sphere_iff_norm] at hz
    have h := norm_sub_le_norm_sub_add_norm_sub z w 1
    have h' := (abs_le.1 <| (abs_re_le_norm <| z - 1).trans h).1
    simp at h'
    linarith [norm_le_norm_sub_add z 1, norm_one (α := ℂ)]

private lemma real_zero_changeLevel {q₀ : ℕ} [NeZero q₀] (h : q₀ ∣ q) {χ : DirichletCharacter ℂ q₀} {β : ℝ} (h1 : χ ^ 2 = 1) (h1' : χ ≠ 1)
    (hz : LFunction χ β = 0) : changeLevel h χ ^ 2 = 1 ∧ changeLevel h χ ≠ 1 ∧ regularizedLFunction (changeLevel h χ) β = 0 := by
  have := (changeLevel_eq_one_iff h).not.2 h1'
  exact ⟨by rw [← map_pow, h1, map_one], this, by simp [regularizedLFunction, this, LFunction_changeLevel h χ (.inl h1'), hz]⟩

theorem excBound : ExcBound := by
  intro ε hε
  obtain ⟨r, hr0, hr1, hrε⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 8 ∧ 12 * r ≤ ε :=
    ⟨min ε 1 / 12, by positivity, by grind, by grind⟩
  have hq (q : ℕ) [NeZero q] : (q : ℝ) ^ (-ε) ≤ 1 := rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast NeZero.pos q) <| by linarith
  by_cases hA : ∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁) (β₁ : ℝ), χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧
    LFunction χ₁ β₁ = 0 ∧ 1 - r / 2 ≤ β₁
  swap
  · push Not at hA
    exact ⟨r / 2, by positivity, fun q _ χ β h h' hz => by nlinarith [hA q _ χ β h h' hz, hq q]⟩
  obtain ⟨q₁, _, χ₁, β₁, h1, h1', hz1, hβ₁⟩ := hA
  obtain ⟨r₁, hr₁, hnz⟩ := Metric.eventually_nhds_iff.1 <| ((differentiable_LFunction h1').continuous.comp continuous_ofReal).continuousAt.eventually_ne
    (x := 1) (by simpa using LFunction_apply_one_ne_zero h1')
  obtain ⟨c, hc0, hc1, hc2, hc3⟩ : ∃ c > 0, c ≤ r / 2 ∧ c ≤ r₁ ∧
      c ≤ (q₁ : ℝ) ^ (-ε) / (162 * (2 / r * (7 + 1 / r)) ^ 2 * (7 + 1 / r) * rexp (51 * r)) :=
    ⟨_, lt_min (by positivity) (lt_min hr₁ (by have := NeZero.pos q₁
                                               positivity)), min_le_left _ _,
      (min_le_right _ _).trans <| min_le_left _ _, (min_le_right _ _).trans <| min_le_right _ _⟩
  refine ⟨c, hc0, fun q₂ _ χ₂ β₂ h2 h2' hz2 => ?_⟩
  rw [le_sub_comm]
  have hc' := mul_le_of_le_one_right hc0.le <| hq q₂
  have hβ₂1 := lt_of_not_ge fun h => LFunction_ne_zero_of_one_le_re χ₂ (.inl h2') (by simpa) hz2
  rcases le_or_gt β₂ (1 - r / 2) with hb | hb
  · linarith
  obtain ⟨a1, b1, c1⟩ := real_zero_changeLevel (dvd_mul_right q₁ q₂) h1 h1' hz1
  obtain ⟨a2, b2, c2⟩ := real_zero_changeLevel (dvd_mul_left q₂ q₁) h2 h2' hz2
  by_cases hψ : changeLevel (dvd_mul_right q₁ q₂) χ₁ * changeLevel (dvd_mul_left q₂ q₁) χ₂ = 1
  · rw [← (eq_inv_of_mul_eq_one_left hψ).trans <| inv_eq_of_mul_eq_one_right <| (sq _).symm.trans a2, show regularizedLFunction _ = _ from ite_eq_right b1,
      LFunction_changeLevel _ χ₁ <| .inl h1'] at c2
    have : β₂ ≤ 1 - r₁ := not_lt.1 fun h => hnz (by rw [Real.dist_eq, abs_sub_lt_iff]
                                                    grind)
      ((mul_eq_zero.1 c2).resolve_right (prod_ne_zero_iff.2 fun p hp => sub_ne_zero.2 fun h => ?_))
    · linarith
    have := congr_arg norm h
    rw [norm_one, norm_mul, norm_natCast_cpow_of_pos (Nat.pos_of_mem_primeFactors hp)] at this
    simp at this
    nlinarith [norm_le_one χ₁ p, rpow_nonneg (Nat.cast_nonneg p) (-β₂), rpow_lt_one_of_one_lt_of_neg
      (x := (p : ℝ)) (z := -β₂) (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt) (by linarith)]
  refine (mul_le_mul_of_nonneg_right hc3 <| by positivity).trans ?_
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, rexp ℓ = (q₁ * q₂ : ℕ) := ⟨_, exp_log <| by exact_mod_cast NeZero.pos <| q₁ * q₂⟩
  have hℓ0 : 0 ≤ ℓ := by rw [← Real.exp_le_exp, hℓ, Real.exp_zero]
                         exact_mod_cast NeZero.pos (q₁ * q₂)
  obtain ⟨M, hM1, hM2⟩ : ∃ M : ℕ, 12 * ℓ ≤ M ∧ (M : ℝ) ≤ 12 * ℓ + 1 :=
    ⟨⌈12 * ℓ⌉₊, Nat.le_ceil _, (Nat.ceil_lt_add_one (by positivity)).le⟩
  have hβ₁1 := lt_of_not_ge fun h => regularizedLFunction_ne_zero _ (by simpa) c1
  have g := product_lfunction_lower_bound a1 a2 b1 b2 hψ (by linarith) hβ₁1 c1 <| M + 100
  have u1 := lfunction_one_le_deriv_bound_mul b1 hr0 hr1 hℓ.ge hβ₁ c1
  have u2 := lfunction_one_le_deriv_bound_mul b2 hr0 hr1 hℓ.ge hb.le c2
  have u3 := lfunction_bound_near_one hψ hr0 hr1 hℓ.ge (z := 1) (by simp
                                                                    linarith) (by simp)
  have t1 : ((3:ℝ) / 4) ^ M * ((q₁ * q₂ : ℕ) : ℝ) ^ 3 ≤ 1 := by
    rw [← hℓ]
    calc _ ≤ rexp (-1 / 4) ^ M * rexp ℓ ^ 3 := by gcongr
                                                  linarith [add_one_le_exp (-1 / 4 : ℝ)]
      _ ≤ 1 := by rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul, ← Real.exp_add]
                  exact exp_le_one_iff.2 (by linarith)
  have t2 : (2 - β₁) ^ (M + 100 + 1) ≤ rexp (r * ℓ) ^ 6 * rexp (51 * r) := by
    rw [← Real.exp_natCast_mul, ← Real.exp_add]
    refine (pow_le_pow_left₀ (b := rexp (r / 2)) (by linarith) (by linarith [add_one_le_exp (r / 2)]) _).trans ?_
    rw [← Real.exp_natCast_mul]
    exact exp_le_exp.2 <| by push_cast
                             nlinarith
  have hX : 0 ≤ 2 / r * ((7 + 1 / r) * rexp (r * ℓ) ^ 2) := by positivity
  have k := mul_le_mul (mul_le_mul (mul_le_mul u1 u2 (norm_nonneg _) (mul_nonneg hX (by linarith))) u3 (norm_nonneg _)
    (mul_nonneg (mul_nonneg hX (by linarith)) (mul_nonneg hX (by linarith)))) t2 (pow_nonneg (by linarith) _)
    (mul_nonneg (mul_nonneg (mul_nonneg hX <| by linarith) <| mul_nonneg hX <| by linarith) <| by positivity)
  rw [mul_div_assoc', div_add' _ _ _ <| by linarith, le_div_iff₀ <| by linarith] at g
  have key : 1 ≤ (1 - β₂) * (162 * (2 / r * (7 + 1 / r)) ^ 2 * (7 + 1 / r) * rexp (51 * r)) * rexp (r * ℓ) ^ 12 := by
    refine le_of_mul_le_mul_left ?_ (by linarith : 0 < 1 - β₁)
    nlinarith [g, k, mul_le_mul_of_nonneg_left (show 18 * 10 ^ 7 * ((q₁ * q₂ : ℕ) : ℝ) ^ 3 * (3 / 4) ^ (M + 100) ≤ 1 / 1000 by
      rw [pow_add]
      linarith) (by linarith : (0:ℝ) ≤ 1 - β₁)]
  have hV6 : rexp (ℓ * -ε) * rexp (r * ℓ) ^ 12 ≤ 1 := by
    rw [← Real.exp_natCast_mul, ← Real.exp_add]
    exact exp_le_one_iff.2 (by push_cast
                               nlinarith)
  rw [div_mul_eq_mul_div, ← mul_rpow (by positivity) (by positivity), ← Nat.cast_mul, ← hℓ, ← Real.exp_mul, div_le_iff₀ (by positivity)]
  exact le_of_mul_le_mul_right (hV6.trans key) <| by positivity

private lemma unsmoothed_sum_bound {a : ℕ → ℂ} {b : Prop} [Decidable b] {x h E L : ℝ} (h1 : 1 ≤ h) (hhx : h ≤ x)
    (hL : ∀ n : ℕ, n ≤ 2 * x → ‖a n‖ ≤ L)
    (hE : ∀ y, x ≤ y → y ≤ 2 * x → ‖∑ n ∈ Icc 1 ⌊y⌋₊, a n * (1 - n / y) - if b then (((y - 2 + 1 / y) / 2 : ℝ) : ℂ) else 0‖ ≤ E) :
    ‖∑ n ∈ Icc 1 ⌊x⌋₊, a n - if b then (x : ℂ) else 0‖ ≤ 3 * x * E / h + 2 * h * (L + 1) := by
  obtain ⟨δ, hδ1, hδ⟩ : ∃ δ : ℂ, ‖δ‖ ≤ 1 ∧ ∀ z : ℂ, (if b then z else 0) = δ * z :=
    ⟨if b then 1 else 0, by aesop, fun z => by simp⟩
  simp [hδ] at hE ⊢
  have key (y : ℝ) (hy : x ≤ y) (hy2 : y ≤ 2 * x) :
      ∃ D : ℂ, ‖D‖ ≤ E ∧ (y : ℂ) * D = ∑ n ∈ Icc 1 ⌊y⌋₊, a n * (y - n) - δ * ((y - 1) ^ 2 / 2) := by
    refine ⟨_, hE y hy hy2, ?_⟩
    have := ofReal_ne_zero.2 <| by linarith
    rw [mul_sub, mul_sum]
    grind
  obtain ⟨D₀, hD₀, e0⟩ := key x le_rfl <| by linarith
  obtain ⟨D₁, hD₁, e1⟩ := key (x + h) (by linarith) <| by linarith
  have hL0 := (norm_nonneg _).trans (hL 0 (by grind))
  obtain ⟨R, hR, hs⟩ : ∃ R : ℂ, ‖R‖ ≤ (h + 1) * (L * h) ∧ ∑ n ∈ Icc 1 ⌊x + h⌋₊, a n * ((x + h : ℝ) - n) =
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n * (x - n) + h * ∑ n ∈ Icc 1 ⌊x⌋₊, a n + R := by
    refine ⟨∑ n ∈ Ioc ⌊x⌋₊ ⌊x + h⌋₊, a n * ((x + h : ℝ) - n), (norm_sum_le _ _).trans
      ((sum_le_card_nsmul _ _ (L * h) fun n hn => ?_).trans ?_), ?_⟩
    · obtain ⟨h2, h3⟩ := mem_Ioc.1 hn
      have h3 := (Nat.cast_le.2 h3).trans (Nat.floor_le (by linarith))
      have h4 : x < n := (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast h2)
      rw [norm_mul, ← ofReal_natCast, ← ofReal_sub, norm_real, norm_of_nonneg <| by linarith]
      bound
    · rw [nsmul_eq_mul, Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono (by linarith))]
      have := mul_nonneg hL0 (by linarith : 0 ≤ h)
      nlinarith [Nat.floor_le (by linarith : 0 ≤ x + h), Nat.lt_floor_add_one x]
    erw [← sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_mono (by linarith : x ≤ x + h)), mul_sum, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    push_cast
    ring
  have I : (h : ℂ) * (∑ n ∈ Icc 1 ⌊x⌋₊, a n - δ * x) = (x + h : ℝ) * D₁ - x * D₀ - R + δ * ((h * (h / 2 - 1) : ℝ) : ℂ) := by
    push_cast at e1 hs ⊢
    grind
  have := congr_arg norm I
  rw [norm_mul, norm_real, norm_of_nonneg <| by linarith] at this
  have h6 : |h * (h / 2 - 1)| ≤ h * h := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  refine le_of_mul_le_mul_left ?_ (by linarith : 0 < h)
  rw [this]
  grw [norm_add_le, norm_sub_le, norm_sub_le, norm_mul, norm_mul, norm_mul, hD₁, hD₀, hR, hδ1, norm_real, norm_real, norm_real,
    norm_of_nonneg <| by linarith, norm_of_nonneg <| by linarith, norm_eq_abs]
  have : h * (3 * x * E / h) = 3 * x * E := by field_simp
  nlinarith [mul_nonneg (sub_nonneg.2 hhx) ((norm_nonneg _).trans hD₀), mul_nonneg (mul_nonneg hL0 (by linarith : (0:ℝ) ≤ h)) (sub_nonneg.2 h1)]

private lemma eventually_rpow_le_exp (s b K : ℝ) (hb : 0 < b) : ∀ᶠ u in atTop, K * u ^ s ≤ rexp (b * u) := by
  filter_upwards [(tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb).eventually <| gt_mem_nhds (by positivity : (0:ℝ) < 1 / (|K| + 1)),
    eventually_gt_atTop 0] with u h1 h2
  rw [lt_div_iff₀ (by positivity), neg_mul, Real.exp_neg, mul_right_comm, ← div_eq_mul_inv, div_lt_one (exp_pos _)] at h1
  have := rpow_nonneg h2.le s
  nlinarith [le_abs_self K]

theorem siegelWalfisz : SiegelWalfisz := by
  unfold SiegelWalfisz psiChi
  intro A hA
  obtain ⟨c₁, hc₁, L₀, hZ⟩ := regularizedLFunction_zero_free
  obtain ⟨δ₀, hδ₀, hM⟩ := smoothed_character_sum_bound
  obtain ⟨cS, hcS, hS⟩ := excBound (2 * A)⁻¹ <| by positivity
  obtain ⟨c, hc, hc1, hc2, hc3⟩ : ∃ c > 0, c ≤ c₁ ∧ c ≤ cS ∧ c ≤ 1 :=
    ⟨min c₁ <| min cS 1, by positivity, by simp, by simp, by simp⟩
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.1 <| (eventually_ge_atTop 1).and <| (eventually_ge_atTop L₀).and <| (eventually_rpow_le_exp (2 * A) 1 5 one_pos).and
    ((eventually_gt_atTop <| c / (8 * δ₀)).and <| (eventually_rpow_le_exp 2 2 (576 / c ^ 2) two_pos).and
    (eventually_rpow_le_exp 2 (c / 32) (3600 / c + 6) <| by positivity))
  obtain ⟨C, hC1, hC⟩ : ∃ C, 1 ≤ C ∧ 8 * rexp (c / 32 * u₀) ≤ C := ⟨_, le_max_left _ _, le_max_right _ _⟩
  refine ⟨c / 32, C, by positivity, fun q _ χ x hx hq => ?_⟩
  have hx0 : 0 < x := by linarith
  obtain ⟨u, hu0, hux⟩ : ∃ u > 0, log x = u ^ 2 :=
    ⟨_, sqrt_pos.2 <| log_pos <| by linarith, (sq_sqrt <| log_nonneg <| by linarith).symm⟩
  rw [hux] at hq ⊢
  rw [sqrt_sq hu0.le]
  simp only [mul_comm ((Λ _ : ℝ) : ℂ)]
  obtain ⟨v, hv⟩ : ∃ v, v = rexp (-(c / 32) * u) := by simp
  rw [← hv]
  have hv0 := hv ▸ exp_pos _
  have hΛ (n : ℕ) : ‖χ n * (Λ n : ℂ)‖ ≤ Λ n := by
    rw [norm_mul, norm_real, norm_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_left vonMangoldt_nonneg <| norm_le_one χ _
  have hL (n : ℕ) (hn : (n : ℝ) ≤ 2 * x) : ‖χ n * (Λ n : ℂ)‖ ≤ 2 * u ^ 2 := by
    refine (hΛ n).trans <| vonMangoldt_le_log.trans ?_
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
      positivity
    rw [← hux, ← log_rpow hx0]
    exact log_le_log (by positivity) <| by rw [rpow_two]
                                           nlinarith
  by_cases hbig : u₀ ≤ u
  swap
  · have := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
    have e2 : 1 ≤ rexp (c / 32 * u₀) * v := by rw [hv, ← Real.exp_add]
                                               exact one_le_exp <| by nlinarith
    calc _ ≤ 8 * x := by
          grw [norm_sub_le, (norm_sum_le_of_le (Icc 1 ⌊x⌋₊) fun n _ => hΛ n).trans <| Chebyshev.psi_le_const_mul_self hx0.le]
          split_ifs <;> simp [abs_of_pos hx0] <;> nlinarith
      _ ≤ 8 * rexp (c / 32 * u₀) * x * v := by nlinarith
      _ ≤ _ := by gcongr
  obtain ⟨hu1, h1, h2, h3, h4, h5⟩ := hu₀ u hbig
  rw [one_mul] at h2
  rw [rpow_two] at h4 h5
  have hq' : (q : ℝ) ≤ u ^ (2 * A) := by rwa [← rpow_natCast, ← rpow_mul hu0.le, Nat.cast_ofNat] at hq
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.2 NeZero.one_le
  have hη : 0 < c / (8 * u) := by positivity
  have hvu : (3600 / c + 6) * u ^ 2 * v ≤ 1 := by
    rwa [← le_div_iff₀ hv0, hv, one_div, ← Real.exp_neg, neg_mul, neg_neg]
  have hv1 : v ≤ 1 := by rw [hv]
                         exact exp_le_one_iff.2 <| by nlinarith
  have e8 : rexp (-(c / 8 * u)) = v ^ 4 := by rw [hv, ← Real.exp_natCast_mul]
                                              ring
  have hh1 : 1 ≤ x * v ^ 2 := by
    rw [hv, ← Real.exp_natCast_mul, ← exp_log hx0, hux, ← Real.exp_add]
    exact one_le_exp <| by push_cast
                           nlinarith
  have hqe : q * (rexp u + 5) ≤ rexp (2 * u) := by rw [two_mul, Real.exp_add]
                                                   nlinarith [one_le_exp hu0.le]
  refine (unsmoothed_sum_bound hh1 (mul_le_of_le_one_right hx0.le <| pow_le_one₀ hv0.le hv1) hL (E := 1200 / c * u ^ 2 * x * v ^ 4)
    fun y hy1 hy2 => (hM q χ y (c / (8 * u)) (rexp u) (by linarith) hη ?_ ?_ (one_le_exp hu0.le) ?_).trans ?_).trans ?_
  · rw [div_lt_iff₀ <| by positivity] at h3 ⊢
    linarith
  · bound
  · intro ⟨β, γ⟩ hw1 hw2 hw0
    obtain ⟨hχ2, hχ1, rfl⟩ := hZ q χ ⟨β, γ⟩ (2 * u) (by linarith)
      (by nlinarith [abs_nonneg γ])
      (by
        have : 3 * (c / (8 * u)) ≤ c₁ / (2 * u) := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) <| by positivity]
          nlinarith
        linarith) hw0
    have := hS q χ β hχ2 hχ1 <| by simp [regularizedLFunction, hχ1] at hw0
                                   simpa
    rw [rpow_neg <| Nat.cast_nonneg _] at this
    have h6 := inv_anti₀ (by positivity) <| (rpow_inv_le_iff_of_pos (Nat.cast_nonneg _) hu0.le <| by positivity).2 hq'
    nlinarith [mul_le_mul_of_nonneg_left h6 hcS.le, mul_le_mul_of_nonneg_right hc2 (inv_pos.2 hu0).le,
      mul_pos hc <| inv_pos.2 hu0, show 3 * (c / (8 * u)) = 3 / 8 * (c * u⁻¹) by ring]
  · have hy0 : 0 < y := by linarith
    have hl1 := hux ▸ log_le_log hx0 hy1
    have hl2 : log y ≤ 2 * u ^ 2 := by
      have := log_le_log hy0 <| show y ≤ x ^ 2 by nlinarith
      rwa [log_pow, hux, Nat.cast_ofNat] at this
    have : u ^ 2 * (c / (8 * u)) = c / 8 * u := by field_simp
    rw [rpow_def_of_pos hy0, rpow_def_of_pos hy0, mul_div_assoc <| 3 / (c / (8 * u)), ← Real.exp_sub]
    calc _ ≤ 6 * (6 * u) / (c / (8 * u)) * (y * v ^ 4 + y * v ^ 4) + 3 / (c / (8 * u)) * (y * v ^ 4) := by
          rw [← e8, ← exp_log hy0, ← Real.exp_add, Real.log_exp]
          gcongr
          · rw [log_le_iff_le_exp <| by positivity]
            calc _ = (q * (rexp u + 5)) ^ 2 * (576 / c ^ 2 * u ^ 2) := by field_simp
                                                                          ring
              _ ≤ rexp (2 * u) ^ 2 * rexp (2 * u) := by gcongr
              _ = _ := by rw [← Real.exp_natCast_mul, ← Real.exp_add]
                          ring_nf
          all_goals nlinarith
      _ = (576 * u ^ 2 + 24 * u) / c * y * v ^ 4 := by field_simp
                                                       ring
      _ ≤ _ := by
        simp [div_mul_eq_mul_div]
        gcongr ?_ / c
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hy2) <| sq_nonneg u) <| pow_nonneg hv0.le 4,
          mul_nonneg (mul_nonneg (by nlinarith : 0 ≤ u ^ 2 - u) hy0.le) <| pow_nonneg hv0.le 4]
  · have e : 3 * x * (1200 / c * u ^ 2 * x * v ^ 4) / (x * v ^ 2) = 3600 / c * u ^ 2 * (x * v ^ 2) := by
      grind
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hvu (mul_pos hx0 hv0).le, mul_nonneg (mul_nonneg hx0.le <| sq_nonneg v) (by nlinarith : (0:ℝ) ≤ u ^ 2 - 1),
      mul_le_mul_of_nonneg_right hC1 (mul_pos hx0 hv0).le]

theorem zFRDirichlet : ZFRDirichlet := GlobalTheory.LandauPageRegion.main

end Formalism.ZeroFreeDirichlet
