/- Verification harness. Each `#guard_msgs` block fails elaboration unless `#print axioms`
reports exactly Lean's three standard axioms. -/
import JacobsthalLogSaving
import JacobsthalLogSaving.Numerics.Margin

/-- info: 'JacobsthalLogSaving.jacobsthal_log_saving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms JacobsthalLogSaving.jacobsthal_log_saving

/-- info: 'JacobsthalLogSaving.Erdos970.Erdos970Final.jacobsthal_log_saving_cutoffShift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms JacobsthalLogSaving.Erdos970.Erdos970Final.jacobsthal_log_saving_cutoffShift

/-- info: 'JacobsthalLogSaving.Erdos970.Erdos970Final.source_root_survivor_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms JacobsthalLogSaving.Erdos970.Erdos970Final.source_root_survivor_lower

/-- info: 'JacobsthalLogSaving.Erdos970.NumberTheoryLean.IteratedLogBound.of_source_root_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms JacobsthalLogSaving.Erdos970.NumberTheoryLean.IteratedLogBound.of_source_root_lower

/-- info: 'JacobsthalLogSaving.Erdos970.ErdosPositiveReference.source_reference_coefficient_margin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms JacobsthalLogSaving.Erdos970.ErdosPositiveReference.source_reference_coefficient_margin

/-- info: 'JacobsthalLogSaving.Numerics.signedCoefficientI_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms JacobsthalLogSaving.Numerics.signedCoefficientI_gt

/-- info: 'JacobsthalLogSaving.Numerics.costMass_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms JacobsthalLogSaving.Numerics.costMass_lt

/-- info: 'JacobsthalLogSaving.Numerics.eulerMascheroniConstant_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms JacobsthalLogSaving.Numerics.eulerMascheroniConstant_lt

/-- info: 'JacobsthalLogSaving.Numerics.fourth_loss_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms JacobsthalLogSaving.Numerics.fourth_loss_value

/-- info: 'JacobsthalLogSaving.Erdos970.ErdosCorrectionLimit.paperGap_floor_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms JacobsthalLogSaving.Erdos970.ErdosCorrectionLimit.paperGap_floor_eq

/-- info: 'JacobsthalLogSaving.Erdos970.ErdosCorrectionLimit.sourceRoot_eq_paper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms JacobsthalLogSaving.Erdos970.ErdosCorrectionLimit.sourceRoot_eq_paper

