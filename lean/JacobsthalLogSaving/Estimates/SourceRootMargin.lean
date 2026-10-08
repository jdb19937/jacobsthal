import JacobsthalLogSaving.Estimates.SourceRootReference
import JacobsthalLogSaving.Numerics.Margin


namespace JacobsthalLogSaving
open OAI


namespace Erdos970
open OAI.Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosPositiveReference
open ErdosOmissionBindings ErdosOmissionTail ErdosContinuousOmission
open ErdosBoundaryIntegral ErdosBoundaryLoss
open Erdos970Dependency.InvariantCostBound
open NumberTheoryLean.BuchstabBridge

theorem actual_I_gt_eleven_seventyfive : (11:ℝ)/75 < signedCoefficientI := by
  have hfirst := actual_first_three_partial_sum_lt
  have htail := actual_omission_tail_lt
  have hsplit := actual_loss_summable.sum_add_tsum_nat_add 3
  have htotal := actual_signed_loss_series
  linarith

theorem actual_I_gt_source_margin : (14:ℝ)/100 < signedCoefficientI := by
  linarith [actual_I_gt_eleven_seventyfive]

theorem exp_gamma_lt_two : Real.exp Real.eulerMascheroniConstant < 2 := by
  have hg : Real.eulerMascheroniConstant < Real.log 2 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds,log_two_bounds.1]
  have h := Real.exp_lt_exp.mpr hg
  simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using h

theorem costMass_lt_eight : costMass < 8 := by
  have h := costMass_le
  change costMass ≤ 2*(2*Real.exp Real.eulerMascheroniConstant) at h
  linarith [exp_gamma_lt_two]

/-- The positivity margin at the raised cutoff: `−(1/100 + 2A − 2) + 2I/M_g > 1/1000`, from the
certified constants `I > 0.3326` (`Numerics.signedCoefficientI_gt`) and `M_g < 7.1804`
(`Numerics.costMass_lt`): with `2A − 2 = 2/25` the left side exceeds `−0.09 + 0.0926`. -/
theorem source_reference_coefficient_margin :
    (1:ℝ)/1000 < -((1:ℝ)/100+ErdosInverseBoxHeight.cutoffShift)+2*signedCoefficientI/costMass := by
  have h : (91:ℝ)/1000 < 2*signedCoefficientI/costMass := by
    apply (lt_div_iff₀ costMass_pos).mpr
    nlinarith [JacobsthalLogSaving.Numerics.signedCoefficientI_gt,
      JacobsthalLogSaving.Numerics.costMass_lt,costMass_pos]
  rw [ErdosInverseBoxHeight.cutoffShift_eq]
  linarith

end ErdosPositiveReference

end

section

open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosSourceReferenceMargin
open ErdosCorrectionLimit ErdosBoundaryIntegral ErdosPositiveReference
open NumberTheoryLean.ReferenceSourceDecomposition
open Erdos970Dependency.InvariantCostBound

theorem actual_reference_limit_positive :
    Real.exp Real.eulerMascheroniConstant/1000 <
      Real.exp Real.eulerMascheroniConstant*
        (-((1:ℝ)/100+ErdosInverseBoxHeight.cutoffShift)+2*signedCoefficientI/costMass) := by
  have hh := mul_lt_mul_of_pos_left source_reference_coefficient_margin (Real.exp_pos Real.eulerMascheroniConstant)
  nlinarith [Real.exp_pos Real.eulerMascheroniConstant]

theorem actual_source_reference_lower_bound :
    ∃ c_L z₀ : ℝ,0 < c_L ∧ 1 < z₀ ∧ ∀ z : ℝ,z₀ ≤ z →
      c_L ≤ (ErdosInverseBoxHeight.sourceB z)^2*
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) ∧
      c_L/(ErdosInverseBoxHeight.sourceB z)^2 ≤
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) := by
  let c_L : ℝ := Real.exp Real.eulerMascheroniConstant/1000
  have hc : 0 < c_L := div_pos (Real.exp_pos _) (by norm_num)
  have hevent := actual_sourceReference_tendsto.eventually (Ioi_mem_nhds actual_reference_limit_positive)
  have he : ∀ᶠ z : ℝ in atTop,
      c_L ≤ (ErdosInverseBoxHeight.sourceB z)^2*
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) ∧
      c_L/(ErdosInverseBoxHeight.sourceB z)^2 ≤
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) := by
    filter_upwards [hevent,rootB_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with z hz hB
    have hz' : c_L < (ErdosInverseBoxHeight.sourceB z)^2*
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) := hz
    refine ⟨hz'.le,?_⟩
    apply (div_le_iff₀ (sq_pos_of_pos hB)).mpr
    simpa only [mul_comm] using hz'.le
  obtain ⟨z₁,hz₁⟩ := eventually_atTop.mp he
  refine ⟨c_L,max 2 z₁,hc,by have h := le_max_left (2:ℝ) z₁; linarith,?_⟩
  intro z hz
  exact hz₁ z ((le_max_right _ _).trans hz)

theorem actual_source_reference_eventually_positive :
    ∃ z₀ : ℝ,1 < z₀ ∧ ∀ z : ℝ,z₀ ≤ z →
      0 < sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) := by
  obtain ⟨c_L,z₁,hc,hz₁,h⟩ := actual_source_reference_lower_bound
  obtain ⟨z₂,hz₂⟩ := eventually_atTop.mp (rootB_tendsto.eventually (eventually_gt_atTop (0:ℝ)))
  refine ⟨max z₁ z₂,hz₁.trans_le (le_max_left _ _),?_⟩
  intro z hz
  have hB := hz₂ z ((le_max_right _ _).trans hz)
  exact (div_pos hc (sq_pos_of_pos hB)).trans_le (h z ((le_max_left _ _).trans hz)).2

end ErdosSourceReferenceMargin

end


namespace NumberTheoryLean.SourceRootReference
open OAI.Erdos970.NumberTheoryLean
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open ReferenceSourceDecomposition ReferenceSourcePrimeSets ReferenceProductsBasics ReferenceAdmission
open LogarithmicBinPartition SourceNodeCoordinates
open ErdosCorrectionLimit ErdosSourceReferenceMargin ErdosInverseBoxHeight
open scoped Topology


theorem source_primes_eq_root_set {top : ℝ} (htop : 1 < top) (hw : 1 < sourceW top) :
    sourcePrimes (sourceW top) (sourceB top) true=sourcePrimeSet (sourceW top) top := by
  have hp : (sourceW top)^(sourceB top)=top :=
    (JacobsthalSourceScale.sourceW_pow_sourceB hw).trans (Real.exp_log (zero_lt_one.trans htop))
  rw [sourcePrimes,hp,availablePrimes_closed,primesBetween_eq_sdiff (zero_lt_one.trans hw).le]
  rfl

theorem source_reference_root_polynomial (a top : ℝ) (htop : 1 < top) (hw : 1 < sourceW top) :
    sourceReference (sourceW top) (sourceRootNode a top)=
      referencePolynomial (sourceW top) (sourcePrimeSet (sourceW top) top)
        (sourceRootNode a top).side (sourceRootNode a top).gap := by
  unfold sourceReference
  change referencePolynomial _ (sourcePrimes (sourceW top) (sourceB top) true) _ _=_
  rw [source_primes_eq_root_set htop hw]

theorem source_root_polynomial_margin : ∃ c_L : ℝ,0 < c_L ∧ ∀ᶠ top : ℝ in atTop,
    c_L ≤ (sourceB top)^2*referencePolynomial (sourceW top) (sourcePrimeSet (sourceW top) top)
      (sourceRootNode (1/100) top).side (sourceRootNode (1/100) top).gap := by
  obtain ⟨c_L,T,hc,_hT,hMargin⟩ := actual_source_reference_lower_bound
  refine ⟨c_L,hc,?_⟩
  filter_upwards [eventually_ge_atTop T,actual_root_eventually (1/100),eventually_gt_atTop (1:ℝ)] with top htop hroot ht1
  have hh := (hMargin top htop).1
  rwa [source_reference_root_polynomial (1/100) top ht1 hroot.2.1] at hh

theorem source_root_eventually_data : ∀ᶠ top : ℝ in atTop,
    0 < sourceY top ∧ 3 ≤ sourceB top ∧ 1 < sourceW top ∧ sourceW top < top ∧
    Real.log (sourceB top) ≤ 2*Real.log (sourceW top) ∧
    199/100 ≤ (sourceRootNode (1/100) top).ratio ∧ (sourceRootNode (1/100) top).ratio ≤ 23/10 ∧
    Consistent (sourceRootNode (1/100) top) ∧ (sourceW top)^(sourceB top)=top := by
  filter_upwards [actual_root_eventually (1/100),rootB_tendsto.eventually_ge_atTop 3,
    Real.tendsto_log_atTop.eventually JacobsthalSourceScale.sourceW_bounds_eventually,eventually_gt_atTop (1:ℝ)]
    with top hroot hB hW ht1
  obtain ⟨_hBpos,hw,hcomp,h199,h23,_hgap,hcons⟩ := hroot
  have hwt : sourceW top < top := by
    have hsmall : sourceW top ≤ Real.log top := hW.2.2
    have hl := Real.log_le_sub_one_of_pos (zero_lt_one.trans ht1)
    linarith
  have hY : 0 < sourceY top := by
    by_contra! hn
    have hzero : sourceY top=0 := by omega
    have hg : (sourceRootNode (1/100) top).gap=199/100 := by
      change Real.log (sourceY top:ℝ)/Real.log (sourceW top)-(1:ℝ)/100+2=199/100
      rw [hzero]
      norm_num
    have hs : Valid (sourceRootNode (1/100) top).side (sourceRootNode (1/100) top).ratio := by
      change 198/100 ≤ (sourceRootNode (1/100) top).ratio
      linarith
    have he := node_gap_eq hs hcons (rfl : (sourceRootNode (1/100) top).cutoff=sourceB top)
    change (sourceRootNode (1/100) top).gap=sourceB top*(sourceRootNode (1/100) top).ratio at he
    have hprod := mul_le_mul h199 hB (by norm_num : (0:ℝ)≤3) (by linarith : 0 ≤ (sourceRootNode (1/100) top).ratio)
    nlinarith
  exact ⟨hY,hB,hw,hwt,hcomp,h199,h23,hcons,
    (JacobsthalSourceScale.sourceW_pow_sourceB hw).trans (Real.exp_log (zero_lt_one.trans ht1))⟩
end NumberTheoryLean.SourceRootReference


end Erdos970

end JacobsthalLogSaving
