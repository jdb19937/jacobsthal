import JacobsthalLogSaving.Conclusions.JacobsthalDeletionBudget
import JacobsthalLogSaving.Conclusions.JacobsthalProgressionLength
import JacobsthalLogSaving.Estimates.CorrectionFloorRemainder

namespace JacobsthalLogSaving
open OAI

namespace Erdos970
open OAI.Erdos970
open scoped _root_.Erdos970

namespace NumberTheoryLean.JacobsthalTerminalScales
open OAI.Erdos970.NumberTheoryLean
open _root_.Filter Asymptotics JacobsthalSourceScale JacobsthalSourceRounding ProgressionSieve
open JacobsthalLogSaving.Erdos970.NumberTheoryLean.JacobsthalProgressionLength
open ErdosInverseBoxHeight (cutoffExponent cutoffShift one_le_cutoffExponent cutoffExponent_le
  cutoffShift_nonneg cutoffShift_le_one two_mul_cutoffExponent_eq)
open scoped Topology

noncomputable def terminalTop (x : ℝ) : ℝ := x*Real.log x
noncomputable def terminalY (x : ℝ) : ℕ := ErdosInverseBoxHeight.sourceY (terminalTop x)
noncomputable def terminalCutoff (x : ℝ) : ℕ := ⌊terminalTop x⌋₊

theorem eventual_terminal_logs : ∀ᶠ x : ℝ in atTop,
    4 ≤ x ∧ 2 ≤ Real.log x ∧ (Real.log x)^2 ≤ x ∧ 16*Real.log x ≤ Real.sqrt x ∧
      Real.log x ≤ Real.log (terminalTop x) ∧ Real.log (terminalTop x) ≤ 2*Real.log x := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (1:ℝ) (s:=1/2) (by norm_num)).bound (by norm_num : (0:ℝ)<1/16)
  filter_upwards [eventually_ge_atTop (4:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 2,
    log_square_le_sqrt_eventually,hsmall] with x hx hlog hs hsmall
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hr : Real.sqrt x ≤ x := by nlinarith [Real.sq_sqrt hx0.le,Real.sqrt_nonneg x]
  have h16 : Real.log x ≤ (1/16:ℝ)*Real.sqrt x := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg hl0.le,
      ← Real.sqrt_eq_rpow,abs_of_nonneg (Real.sqrt_nonneg x)] using hsmall
  have hll0 := Real.log_nonneg (by linarith : 1 ≤ Real.log x)
  have hllu := Real.log_le_sub_one_of_pos hl0
  have he : Real.log (terminalTop x)=Real.log x+Real.log (Real.log x) :=
    Real.log_mul hx0.ne' hl0.ne'
  refine ⟨hx,hlog,hs.trans hr,by linarith,?_,?_⟩ <;> rw [he] <;> linarith

theorem terminal_top_tendsto : Tendsto terminalTop atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [eventual_terminal_logs,eventually_ge_atTop R] with x hx hR
  unfold terminalTop
  nlinarith [hx.1,hx.2.1]

theorem terminal_w_tendsto :
    Tendsto (fun x : ℝ => ErdosInverseBoxHeight.sourceW (terminalTop x)) atTop atTop :=
  (JacobsthalSourceScale.sourceW_tendsto.comp Real.tendsto_log_atTop).comp terminal_top_tendsto

theorem terminal_w_le_top : ∀ᶠ x : ℝ in atTop,
    ErdosInverseBoxHeight.sourceW (terminalTop x) ≤ terminalTop x := by
  filter_upwards [(Real.tendsto_log_atTop.comp terminal_top_tendsto).eventually
    JacobsthalSourceScale.sourceW_bounds_eventually,terminal_top_tendsto.eventually_gt_atTop 1]
    with x hw ht
  have hW : ErdosInverseBoxHeight.sourceW (terminalTop x) ≤ Real.log (terminalTop x) := hw.2.2
  have hlog := Real.log_le_sub_one_of_pos (zero_lt_one.trans ht)
  linarith

/-- `t = l^θ` satisfies `1 ≤ t ≤ l` for `l ≥ 1`, since `0 ≤ θ ≤ 1`. -/
theorem cutoff_power_bounds {l : ℝ} (hl : 1 ≤ l) : 1 ≤ l^cutoffShift ∧ l^cutoffShift ≤ l := by
  refine ⟨Real.one_le_rpow hl cutoffShift_nonneg,?_⟩
  calc l^cutoffShift ≤ l^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hl cutoffShift_le_one
    _ = l := Real.rpow_one l

/-- `x²/(16 l^θ) ≤ ⌊(xl)²/L^(2A)⌋ ≤ x²/l^θ` for `l ≤ L ≤ 2l`. -/
theorem floor_length_bounds_cutoff {x l L : ℝ} (hx : 4 ≤ x) (hl : 1 ≤ l)
    (hlL : l ≤ L) (hLl : L ≤ 2*l) (hbig : 16*l ≤ x^2) :
    x^2/(16*l^cutoffShift) ≤ (⌊(x*l)^2/L^(2*cutoffExponent)⌋₊:ℝ) ∧
      (⌊(x*l)^2/L^(2*cutoffExponent)⌋₊:ℝ) ≤ x^2/l^cutoffShift := by
  have hl0 : 0 < l := by linarith
  have hL0 : 0 < L := by linarith
  have ht := cutoff_power_bounds hl
  have ht0 : 0 < l^cutoffShift := by linarith
  have h2A : 0 ≤ 2*cutoffExponent := by linarith [one_le_cutoffExponent]
  have hsplit : l^(2*cutoffExponent) = l^2*l^cutoffShift := by
    rw [two_mul_cutoffExponent_eq,Real.rpow_add hl0,Real.rpow_two]
  have hLlow : l^(2*cutoffExponent) ≤ L^(2*cutoffExponent) := Real.rpow_le_rpow hl0.le hlL h2A
  have hLup : L^(2*cutoffExponent) ≤ 8*l^(2*cutoffExponent) := by
    calc L^(2*cutoffExponent) ≤ (2*l)^(2*cutoffExponent) := Real.rpow_le_rpow hL0.le hLl h2A
      _ = 2^(2*cutoffExponent)*l^(2*cutoffExponent) := Real.mul_rpow (by norm_num) hl0.le
      _ ≤ 8*l^(2*cutoffExponent) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hl0.le _)
        calc (2:ℝ)^(2*cutoffExponent) ≤ 2^((3:ℕ):ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith [cutoffExponent_le])
          _ = 8 := by rw [Real.rpow_natCast]; norm_num
  have hP0 : 0 < L^(2*cutoffExponent) := Real.rpow_pos_of_pos hL0 _
  have hl2A : 0 < l^(2*cutoffExponent) := Real.rpow_pos_of_pos hl0 _
  have hup : (x*l)^2/L^(2*cutoffExponent) ≤ x^2/l^cutoffShift := by
    calc (x*l)^2/L^(2*cutoffExponent) ≤ (x*l)^2/l^(2*cutoffExponent) :=
          div_le_div_of_nonneg_left (sq_nonneg _) hl2A hLlow
      _ = x^2/l^cutoffShift := by rw [hsplit]; field_simp <;> ring
  have hlow : x^2/(8*l^cutoffShift) ≤ (x*l)^2/L^(2*cutoffExponent) := by
    calc x^2/(8*l^cutoffShift) = (x*l)^2/(8*l^(2*cutoffExponent)) := by rw [hsplit]; field_simp <;> ring
      _ ≤ (x*l)^2/L^(2*cutoffExponent) := div_le_div_of_nonneg_left (sq_nonneg _) hP0 hLup
  have hfloor := Nat.floor_le (div_nonneg (sq_nonneg (x*l)) hP0.le)
  have hround := Nat.lt_floor_add_one ((x*l)^2/L^(2*cutoffExponent))
  constructor
  · have h16 : 16*l^cutoffShift ≤ x^2 := by linarith [ht.2]
    have hstep : x^2/(16*l^cutoffShift)+1 ≤ x^2/(8*l^cutoffShift) := by
      rw [div_add_one (by positivity),div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h16 ht0.le]
    linarith
  · exact hfloor.trans hup

theorem eventual_terminal_numerics : ∀ᶠ x : ℝ in atTop,
    4 ≤ x ∧ 2 ≤ Real.log x ∧ (Real.log x)^2 ≤ x ∧ 1 < terminalTop x ∧
    x^2/(16*(Real.log x)^cutoffShift) ≤ (terminalY x:ℝ) ∧
    (terminalY x:ℝ) ≤ x^2/(Real.log x)^cutoffShift ∧
    progressionLength (terminalY x) (terminalCutoff x) ≤ terminalCutoff x ∧
    (progressionLength (terminalY x) (terminalCutoff x):ℝ) ≤ (terminalY x:ℝ)/(x*Real.log x)+1 ∧
    Real.log x/2 ≤ Real.log (progressionLength (terminalY x) (terminalCutoff x):ℝ) := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (s:=1/2) (by norm_num)).bound
    (by norm_num : (0:ℝ)<1/32)
  filter_upwards [eventual_terminal_logs,hsmall] with x hx hs32
  obtain ⟨hx,hlog,hs,h16,hlo,hhi⟩ := hx
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hl1 : 1 ≤ Real.log x := by linarith
  have htop : 2 ≤ terminalTop x := by unfold terminalTop; nlinarith
  have hsx : Real.sqrt x ≤ x := by nlinarith [Real.sq_sqrt hx0.le,Real.sqrt_nonneg x]
  have hbig : 16*Real.log x ≤ x^2 := by nlinarith
  have hY := floor_length_bounds_cutoff hx hl1 hlo hhi hbig
  have hY' : x^2/(16*(Real.log x)^cutoffShift) ≤ (terminalY x:ℝ) ∧
      (terminalY x:ℝ) ≤ x^2/(Real.log x)^cutoffShift := by
    simpa only [terminalY,ErdosInverseBoxHeight.sourceY,terminalTop] using hY
  have hZ := floor_cutoff_bounds htop
  have ht := cutoff_power_bounds hl1
  have hT := source_progression_bounds_cutoff hx hlog hs ht.1 ht.2 (terminalY x) (terminalCutoff x)
    hY'.1 hY'.2 hZ.1 (by simpa only [terminalCutoff,terminalTop,mul_assoc] using hZ.2.2.2) hZ.2.2.1
  have h32 : (Real.log x)^2 ≤ (1/32:ℝ)*Real.sqrt x := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log x)),
      ← Real.sqrt_eq_rpow,abs_of_nonneg (Real.sqrt_nonneg x)] using hs32
  exact ⟨hx,hlog,hs,by linarith,hY'.1,hY'.2,hT.2.2.2,hT.2.1,
    progression_log_lower_cutoff hx0 hl0 (by linarith) _ _ hT.1⟩

end NumberTheoryLean.JacobsthalTerminalScales

end Erdos970

end JacobsthalLogSaving
