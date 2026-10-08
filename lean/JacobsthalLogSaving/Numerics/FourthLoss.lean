import JacobsthalLogSaving.Estimates.SourceRootReference
import JacobsthalLogSaving.Numerics.LossFour

/-!
# The fourth omission loss term as an explicit iterated integral

`omissionLossTerm 3 = ∫_1^2 dx ∫_1^x du ∫_1^u dt ∫_1^t dτ loss4Kernel τ t u x`, obtained by unfolding
three gate iterates and moving the source variable `y` innermost (bounded Fubini on rectangles), exactly
as the vendored development does for `omissionLossTerm 2`.
-/

namespace JacobsthalLogSaving.Numerics

open Set MeasureTheory
open OAI.Erdos970 OAI.Erdos970.ErdosContinuousOmission OAI.Erdos970.ErdosContinuousBoundary
open OAI.Erdos970.ErdosOmissionBindings OAI.Erdos970.ErdosOmissionTail
open JacobsthalLogSaving.Erdos970.ErdosOmissionBindings JacobsthalLogSaving.Erdos970.ErdosOmissionTail
open OAI.Erdos970.NumberTheoryLean.FinitePathGeometry

theorem fourth_loss_bounded :
    omissionLossTerm 3 = ∫ y : ℝ in (1:ℝ)..5, omissionDensity 3 .even y := by
  have ho : (∫ y in sourceDomain .odd, omissionDensity 3 .odd y) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y _hy
    have h := (omission_wrong_parity_zero 1).2 (2*y+2) 2
    norm_num only [Nat.mul_one] at h
    rw [omissionDensity, h, mul_zero]
  have hz : (∫ y in Ioi 5, omissionDensity 3 .even y) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    exact omissionDensity_high_zero 3 .even (by norm_num; change 5 < y at hy; linarith)
  have h := intervalIntegral.integral_Ioi_sub_Ioi (omissionDensity_integrable 3 .even)
    (by norm_num : (1:ℝ) ≤ 5)
  rw [hz, sub_zero] at h
  rw [omissionLossTerm, ho, add_zero]
  exact h

/-- Kernel in `(y, x)` after unfolding the outer (even) gate. -/
noncomputable def fourthKernel (p : ℝ×ℝ) : ℝ :=
  (2*(p.1^2-1)/(max 1 p.2))*gateIterate 2 omissionForce .odd (2*p.1+2-p.2) p.2

/-- Composition of a jointly continuous profile with continuous arguments. -/
theorem profile_comp_continuous {H : Profile} (hH : JointContinuous H) (i : Side)
    {r b : ℝ×ℝ → ℝ} (hr : Continuous r) (hb : Continuous b) :
    Continuous (fun p : ℝ×ℝ => H i (r p) (b p)) :=
  (hH i).comp (hr.prodMk hb)

theorem fourthKernel_measurable : Measurable fourthKernel := by
  have hc : Continuous (fun p : ℝ×ℝ => gateIterate 2 omissionForce .odd (2*p.1+2-p.2) p.2) :=
    profile_comp_continuous (gateIterate_continuous omissionForce_continuous 2) .odd
      (by fun_prop) continuous_snd
  have hp : Measurable (fun p : ℝ×ℝ => 2*(p.1^2-1)/(max 1 p.2)) := by fun_prop
  exact hp.mul hc.measurable

theorem fourthKernel_bound {y x : ℝ} (hy : y ∈ Icc (1:ℝ) 5) (hx : x ∈ Icc (1:ℝ) 2) :
    |fourthKernel (y,x)| ≤ 48 := by
  have hx0 : 0 < x := by linarith [hx.1]
  unfold fourthKernel
  dsimp only
  rw [max_eq_right hx.1]
  have hp0 : 0 ≤ 2*(y^2-1)/x := by
    apply div_nonneg _ hx0.le
    nlinarith [hy.1]
  have hp48 : 2*(y^2-1)/x ≤ 48 := by
    apply (div_le_iff₀ hx0).mpr
    nlinarith [hy.1, hy.2, hx.1]
  have hg0 := gateIterate_nonnegative omissionForce_nonnegative 2 .odd (2*y+2-x) x
  have hg1 := gateIterate_force_le_one 2 .odd (2*y+2-x) x
  rw [abs_of_nonneg (mul_nonneg hp0 hg0)]
  exact (mul_le_mul_of_nonneg_left hg1 hp0).trans (by simpa only [mul_one] using hp48)

theorem fourth_density_kernel (y : ℝ) :
    omissionDensity 3 .even y = ∫ x : ℝ in (1:ℝ)..2, fourthKernel (y,x) := by
  change 2*(y^2-1)*gate (gateIterate 2 omissionForce) .even (2*y+2) 2 = _
  have hc : upperCutoff .even (2*y+2) 2 = 2 := baseCutoff_on (by norm_num) le_rfl
  rw [gate, hc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  dsimp only [fourthKernel, Side.flip]
  ring

theorem fourth_loss_rectangle :
    omissionLossTerm 3 = ∫ x in Icc (1:ℝ) 2, ∫ y in Icc (1:ℝ) 5, fourthKernel (y,x) := by
  rw [fourth_loss_bounded]
  simp_rw [fourth_density_kernel]
  rw [intervalIntegral.integral_of_le (by norm_num : (1:ℝ) ≤ 5)]
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (1:ℝ) ≤ 2), ← integral_Icc_eq_integral_Ioc]
  exact bounded_rectangle_swap fourthKernel_measurable 1 5 1 2 48
    (fun _ hy _ hx => fourthKernel_bound hy hx)

/-- The odd gate at `(2y+2-x, x)` as an integral over `[1,x]` with a threshold in `y`. -/
theorem odd_gate_threshold (H : Profile) (y : ℝ) {x : ℝ} (hx : x ∈ Icc (1:ℝ) 2) :
    gate H .odd (2*y+2-x) x =
      ∫ u : ℝ in (1:ℝ)..x, if x+2*u ≤ 2*y then H .even (2*y+2-x-u) u/(max 1 u) else 0 := by
  classical
  have heq : Ioc (1:ℝ) (upperCutoff .odd (2*y+2-x) x) = Ioc (1:ℝ) x ∩ {u : ℝ | x+2*u ≤ 2*y} := by
    ext u
    have hc := mem_upperCutoff .odd (2*y+2-x) x u
    constructor
    · intro hu
      obtain ⟨hu1,hu2,hux,ha⟩ := hc.mp hu
      rw [strong_gate_below_two hu2] at ha
      refine ⟨⟨hu1,hux⟩,?_⟩
      change x+2*u ≤ 2*y
      linarith
    · rintro ⟨⟨hu1,hux⟩,huy⟩
      apply hc.mpr
      refine ⟨hu1,hux.trans hx.2,hux,?_⟩
      rw [strong_gate_below_two (hux.trans hx.2)]
      change x+2*u ≤ 2*y at huy
      linarith
  rw [gate,intervalIntegral.integral_of_le (upperCutoff_bounds .odd (2*y+2-x) x).1,
    intervalIntegral.integral_of_le hx.1]
  change (∫ u in Ioc (1:ℝ) (upperCutoff .odd (2*y+2-x) x),H .even (2*y+2-x-u) u/(max 1 u))=
    ∫ u in Ioc (1:ℝ) x,({u : ℝ | x+2*u ≤ 2*y}).indicator (fun u => H .even (2*y+2-x-u) u/(max 1 u)) u
  have hm : MeasurableSet {u : ℝ | x+2*u ≤ 2*y} := measurableSet_le (by fun_prop) measurable_const
  rw [setIntegral_indicator hm,heq]

/-- Kernel in `(y, u)` for fixed `x`, with the threshold `x+2u ≤ 2y` from the odd gate. -/
noncomputable def fourthInner (x : ℝ) (p : ℝ×ℝ) : ℝ :=
  if x+2*p.2 ≤ 2*p.1 then
    (2*(p.1^2-1)/(max 1 p.2))*gateIterate 1 omissionForce .even (2*p.1+2-x-p.2) p.2 else 0

/-- Same kernel without the threshold, as a function of `y` for fixed `x, u`. -/
noncomputable def fourthTail (x u y : ℝ) : ℝ :=
  (2*(y^2-1)/(max 1 u))*gateIterate 1 omissionForce .even (2*y+2-x-u) u

theorem fourthInner_measurable (x : ℝ) : Measurable (fourthInner x) := by
  have hc : Continuous (fun p : ℝ×ℝ => gateIterate 1 omissionForce .even (2*p.1+2-x-p.2) p.2) :=
    profile_comp_continuous (gateIterate_continuous omissionForce_continuous 1) .even
      (by fun_prop) continuous_snd
  have hp : Measurable (fun p : ℝ×ℝ => 2*(p.1^2-1)/(max 1 p.2)) := by fun_prop
  exact Measurable.ite (measurableSet_le (measurable_const.add (measurable_const.mul measurable_snd))
    (measurable_const.mul measurable_fst)) (hp.mul hc.measurable) measurable_const

theorem fourthInner_bound {x y u : ℝ} (hy : y ∈ Icc (1:ℝ) 5) (hu : u ∈ Icc (1:ℝ) 2) :
    |fourthInner x (y,u)| ≤ 48 := by
  have hu0 : 0 < u := by linarith [hu.1]
  unfold fourthInner
  dsimp only
  split_ifs
  · rw [max_eq_right hu.1]
    have hp0 : 0 ≤ 2*(y^2-1)/u := by
      apply div_nonneg _ hu0.le
      nlinarith [hy.1]
    have hp48 : 2*(y^2-1)/u ≤ 48 := by
      apply (div_le_iff₀ hu0).mpr
      nlinarith [hy.1,hy.2,hu.1]
    have hg0 := gateIterate_nonnegative omissionForce_nonnegative 1 .even (2*y+2-x-u) u
    have hg1 := gateIterate_force_le_one 1 .even (2*y+2-x-u) u
    rw [abs_of_nonneg (mul_nonneg hp0 hg0)]
    exact (mul_le_mul_of_nonneg_left hg1 hp0).trans (by simpa only [mul_one] using hp48)
  · norm_num

theorem fourthKernel_inner (y : ℝ) {x : ℝ} (hx : x ∈ Icc (1:ℝ) 2) :
    fourthKernel (y,x) = (1/x) * ∫ u : ℝ in (1:ℝ)..x, fourthInner x (y,u) := by
  change (2*(y^2-1)/(max 1 x))*gate (gateIterate 1 omissionForce) .odd (2*y+2-x) x = _
  rw [odd_gate_threshold _ y hx, max_eq_right hx.1, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _hu
  dsimp only [fourthInner]
  split_ifs
  · ring
  · simp

noncomputable def levelU (x u : ℝ) : ℝ := ∫ y in Icc ((x+2*u)/2) 5, fourthTail x u y

theorem fourth_level_x {x : ℝ} (hx : x ∈ Icc (1:ℝ) 2) :
    (∫ y in Icc (1:ℝ) 5, fourthKernel (y,x)) = (1/x) * ∫ u in Icc (1:ℝ) x, levelU x u := by
  simp_rw [fourthKernel_inner _ hx]
  rw [integral_const_mul]
  congr 1
  simp_rw [intervalIntegral.integral_of_le hx.1, ← integral_Icc_eq_integral_Ioc]
  rw [bounded_rectangle_swap (fourthInner_measurable x) 1 5 1 x 48
    (fun _ hy _ hu => fourthInner_bound hy ⟨hu.1, hu.2.trans hx.2⟩)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  dsimp only
  have he : (fun y : ℝ => fourthInner x (y,u)) = (Ici ((x+2*u)/2)).indicator (fourthTail x u) := by
    funext y
    dsimp only [fourthInner, fourthTail]
    by_cases hh : x+2*u ≤ 2*y
    · rw [ite_eq_left hh, indicator_of_mem (show y ∈ Ici ((x+2*u)/2) by
        change (x+2*u)/2 ≤ y; linarith)]
      rfl
    · rw [ite_eq_right hh, indicator_of_notMem (show y ∉ Ici ((x+2*u)/2) by
        intro h; change (x+2*u)/2 ≤ y at h; apply hh; linarith)]
  have hset : Icc (1:ℝ) 5 ∩ Ici ((x+2*u)/2) = Icc ((x+2*u)/2) 5 := by
    ext y
    constructor
    · rintro ⟨hy,hxy⟩; exact ⟨hxy,hy.2⟩
    · intro hy; exact ⟨⟨by linarith [hx.1,hu.1,hy.1],hy.2⟩,hy.1⟩
  rw [he, setIntegral_indicator measurableSet_Ici, hset]
  rfl

/-- Kernel in `(y, t)` for fixed `x, u`, after unfolding the inner even gate. -/
noncomputable def fourthForce (x u : ℝ) (p : ℝ×ℝ) : ℝ :=
  ((p.1^2-1)/(max 1 p.2))*omissionForce .odd (2*p.1+2-(x+u+p.2)) p.2

theorem fourthForce_measurable (x u : ℝ) : Measurable (fourthForce x u) := by
  have hf : Continuous (fun p : ℝ×ℝ => omissionForce .odd (2*p.1+2-(x+u+p.2)) p.2) :=
    profile_comp_continuous omissionForce_continuous .odd (by fun_prop) continuous_snd
  have hp : Measurable (fun p : ℝ×ℝ => (p.1^2-1)/(max 1 p.2)) := by fun_prop
  exact hp.mul hf.measurable

theorem fourthForce_bound {x u y t : ℝ} (hy : y ∈ Icc (1:ℝ) 5) (ht : t ∈ Icc (1:ℝ) 2) :
    |fourthForce x u (y,t)| ≤ 24 := by
  have ht0 : 0 < t := by linarith [ht.1]
  unfold fourthForce
  dsimp only
  rw [max_eq_right ht.1]
  have hp0 : 0 ≤ (y^2-1)/t := by
    apply div_nonneg _ ht0.le
    nlinarith [hy.1]
  have hp24 : (y^2-1)/t ≤ 24 := by
    apply (div_le_iff₀ ht0).mpr
    nlinarith [hy.1,hy.2,ht.1]
  rw [abs_of_nonneg (mul_nonneg hp0 (omissionForce_nonnegative _ _ _))]
  exact (mul_le_mul_of_nonneg_left (OAI.Erdos970.ErdosOmissionTail.omissionForce_le_one _ _ _) hp0).trans
    (by simpa only [mul_one] using hp24)

theorem fourthTail_gate (y : ℝ) {x u : ℝ} (hu : u ∈ Icc (1:ℝ) 2) :
    fourthTail x u y = (2/u) * ∫ t : ℝ in (1:ℝ)..u, fourthForce x u (y,t) := by
  have hc : upperCutoff .even (2*y+2-x-u) u = u := baseCutoff_on hu.1 hu.2
  change (2*(y^2-1)/(max 1 u))*gate omissionForce .even (2*y+2-x-u) u = _
  rw [gate, hc, max_eq_right hu.1, ← intervalIntegral.integral_const_mul (2/u),
    ← intervalIntegral.integral_const_mul (2*(y^2-1)/u)]
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only [fourthForce, Side.flip]
  rw [show 2*y+2-x-u-t = 2*y+2-(x+u+t) by ring]
  ring

noncomputable def levelT (x u t : ℝ) : ℝ := ∫ y in Icc ((x+2*u)/2) 5, fourthForce x u (y,t)

theorem fourth_level_u {x u : ℝ} (hx : x ∈ Icc (1:ℝ) 2) (hu : u ∈ Icc (1:ℝ) x) :
    levelU x u = (2/u) * ∫ t in Icc (1:ℝ) u, levelT x u t := by
  have hu2 : u ∈ Icc (1:ℝ) 2 := ⟨hu.1, hu.2.trans hx.2⟩
  unfold levelU
  simp_rw [fourthTail_gate _ hu2]
  rw [integral_const_mul]
  congr 1
  simp_rw [intervalIntegral.integral_of_le hu.1, ← integral_Icc_eq_integral_Ioc]
  rw [bounded_rectangle_swap (fourthForce_measurable x u) ((x+2*u)/2) 5 1 u 24
    (fun _ hy _ ht => fourthForce_bound ⟨by linarith [hx.1,hu.1,hy.1], hy.2⟩ ⟨ht.1, ht.2.trans hu2.2⟩)]
  rfl

theorem fourth_level_t {x u t : ℝ} (hx : x ∈ Icc (1:ℝ) 2) (hu : u ∈ Icc (1:ℝ) x)
    (ht : t ∈ Icc (1:ℝ) u) :
    levelT x u t = (1/t) * ∫ s : ℝ in (1:ℝ)..t,
      ((((x+u+t)/2+s)^3-((x+2*u)/2)^3)/3-1*((x+u+t)/2+s-(x+2*u)/2))/(s^2) := by
  have hu2 : u ≤ 2 := hu.2.trans hx.2
  have ht2 : t ≤ 2 := ht.2.trans hu2
  have hl : (x+2*u)/2 ≤ 5 := by linarith [hx.2]
  unfold levelT
  have he : (fun y : ℝ => fourthForce x u (y,t)) =
      fun y => (1/t) * ((y^2-1)*omissionForce .odd (2*y+2-(x+u+t)) t) := by
    funext y
    dsimp only [fourthForce]
    rw [max_eq_right ht.1]
    ring
  rw [he, integral_const_mul]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hl]
  exact integrated_force_window (x+u+t) ((x+2*u)/2) 5 t 1 (by linarith [hx.1,hu.1]) ht.1 ht2
    (by linarith [hu2,ht.1]) (by linarith [hx.2,hu2,ht2])

theorem fourth_loss_iterated :
    omissionLossTerm 3 = ∫ x : ℝ in (1:ℝ)..2, ∫ u : ℝ in (1:ℝ)..x, ∫ t : ℝ in (1:ℝ)..u,
      ∫ s : ℝ in (1:ℝ)..t, loss4Kernel s t u x := by
  rw [fourth_loss_rectangle, intervalIntegral.integral_of_le (by norm_num : (1:ℝ) ≤ 2),
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  dsimp only
  rw [fourth_level_x hx, ← integral_const_mul, intervalIntegral.integral_of_le hx.1,
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  dsimp only
  rw [fourth_level_u hx hu, ← mul_assoc, ← integral_const_mul, intervalIntegral.integral_of_le hu.1,
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [fourth_level_t hx hu ht, ← mul_assoc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  dsimp only
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have hu0 : u ≠ 0 := by linarith [hu.1]
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hs0 : s ≠ 0 := by linarith [hs.1]
  unfold loss4Kernel
  field_simp

theorem fourth_loss_value : omissionLossTerm 3 = L4value :=
  fourth_loss_iterated.trans loss4_iterated_eq

end JacobsthalLogSaving.Numerics
