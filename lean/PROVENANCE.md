# Provenance of `JacobsthalLogSaving/`

`OAI/NumberTheory/Jacobsthal/` is OpenAI's formalization of h(k) << k^2/(log log 3k)^2 (github.com/openai/math, preprint of September 25, 2026), vendored byte-identical. Our proof imports it unchanged for every module that does not mention the interval length `sourceY`.

The modules below are copies of the vendored modules of the same path (the import closure of the definition of `sourceY`), with three mechanical changes in every file: imports of copied modules point at `JacobsthalLogSaving.*`, the root namespace `OAI` is renamed `JacobsthalLogSaving`, and `open OAI...` lines are inserted after namespace commands so that unchanged references to vendored declarations resolve. Files marked *modified* carry mathematical changes beyond that; the count is the number of added or changed non-mechanical lines. Compare any file against its vendored original with `diff`. `Estimates/SourceRootReference.lean` is the first part of the vendored file of that name and `Estimates/SourceRootMargin.lean` the second, split so that the certified constants can be inserted between them.

New modules (not copies): `Conclusions/LogSavingModel.lean`, `Estimates/SourceRootMargin.lean`, `Numerics/FourthLoss.lean`, `Numerics/Gamma.lean`, `Numerics/LossFour.lean`, `Numerics/Margin.lean`, and the root module `JacobsthalLogSaving.lean`. The `Numerics/` modules certify `I > 0.3326` (exact fourth loss term, nine-digit `log 2`, the vendored tail majorant shifted by one index) and `M_g < 7.1804` (`γ < 0.58501` from Mathlib bracketing at `n = 64`).

Vendored modules in the closure that were not copied because the rewritten terminal chain replaces them: `Conclusions/JacobsthalBudgetSeparation.lean`, `Conclusions/JacobsthalFromRootLower.lean`.

| module | status |
|---|---|
| `Analysis/CompactSmallCountErrors.lean` | mechanical only |
| `Analysis/JointModelDensity.lean` | mechanical only |
| `Analysis/PaperContinuousCorrection.lean` | mechanical only |
| `Analysis/PatternErrorNormalization.lean` | mechanical only |
| `Analysis/SmallModelMeasure.lean` | mechanical only |
| `Analysis/SourceCompactErrorMass.lean` | modified (3 lines added or changed) |
| `Analysis/SourceCompactSingletons.lean` | mechanical only |
| `Analysis/SourceProductLimit.lean` | mechanical only |
| `Analysis/SourceReferenceLimit.lean` | modified (3 lines added or changed) |
| `Analysis/TripleWeightDensity.lean` | mechanical only |
| `Conclusions/IteratedLogBound.lean` | modified (45 lines added or changed) |
| `Conclusions/IteratedLogBudget.lean` | modified (88 lines added or changed) |
| `Conclusions/IteratedLogFinite.lean` | modified (27 lines added or changed) |
| `Conclusions/IteratedLogScales.lean` | mechanical only |
| `Conclusions/JacobsthalDeletionBudget.lean` | modified (22 lines added or changed) |
| `Conclusions/JacobsthalProgressionLength.lean` | modified (30 lines added or changed) |
| `Conclusions/JacobsthalSurvivorScale.lean` | modified (10 lines added or changed) |
| `Conclusions/JacobsthalTerminalScales.lean` | modified (80 lines added or changed) |
| `Conclusions/SourceRootCompletion.lean` | mechanical only |
| `Estimates/ActualModelTargets.lean` | mechanical only |
| `Estimates/ActualPatternClass.lean` | mechanical only |
| `Estimates/ActualPointSlopes.lean` | mechanical only |
| `Estimates/ActualRegularAdmission.lean` | mechanical only |
| `Estimates/ActualSourceInverse.lean` | mechanical only |
| `Estimates/CandidateExceptionMass.lean` | mechanical only |
| `Estimates/CandidateLengthBand.lean` | mechanical only |
| `Estimates/CanonicalCorrectionSum.lean` | mechanical only |
| `Estimates/CanonicalCrossingTail.lean` | mechanical only |
| `Estimates/CanonicalKeyReference.lean` | mechanical only |
| `Estimates/ConditionalPatternCounts.lean` | mechanical only |
| `Estimates/CorrectionFloorRemainder.lean` | modified (80 lines added or changed) |
| `Estimates/CountErrorRemainder.lean` | mechanical only |
| `Estimates/EffectiveAvoidance.lean` | mechanical only |
| `Estimates/EffectiveNumerator.lean` | mechanical only |
| `Estimates/EffectiveProgression.lean` | mechanical only |
| `Estimates/EffectiveSurvivors.lean` | mechanical only |
| `Estimates/EndpointSoftConclusion.lean` | mechanical only |
| `Estimates/FirstIsolatedPosition.lean` | mechanical only |
| `Estimates/FrozenSuffixData.lean` | mechanical only |
| `Estimates/FullEndpointData.lean` | mechanical only |
| `Estimates/FullPatternSurvivors.lean` | mechanical only |
| `Estimates/HarmonicConditioning.lean` | mechanical only |
| `Estimates/IsolatedPowerOrdering.lean` | mechanical only |
| `Estimates/IsolatedSourceScales.lean` | mechanical only |
| `Estimates/JointModelCount.lean` | mechanical only |
| `Estimates/LargeGapCountErrors.lean` | mechanical only |
| `Estimates/LiteralSourceList.lean` | mechanical only |
| `Estimates/NonisolatedSelectedOccurrence.lean` | mechanical only |
| `Estimates/NonstructuredCounts.lean` | mechanical only |
| `Estimates/OriginalPairMembership.lean` | mechanical only |
| `Estimates/ParentProductReadout.lean` | mechanical only |
| `Estimates/PatternCardGrowth.lean` | mechanical only |
| `Estimates/ReferenceIsolatedExclusion.lean` | mechanical only |
| `Estimates/RefinedDiscardBound.lean` | mechanical only |
| `Estimates/RefinementRewardMargin.lean` | mechanical only |
| `Estimates/RepeatedPairRow.lean` | mechanical only |
| `Estimates/RepeatedPositionNeighbors.lean` | mechanical only |
| `Estimates/RepeatedSelectedOccurrence.lean` | mechanical only |
| `Estimates/RepeatedStepRowBound.lean` | mechanical only |
| `Estimates/SmallModelSourceScales.lean` | mechanical only |
| `Estimates/SourceCenteredGap.lean` | modified (9 lines added or changed) |
| `Estimates/SourceExtensionScale.lean` | mechanical only |
| `Estimates/SourceFirstCrossing.lean` | mechanical only |
| `Estimates/SourceFullPatternDomination.lean` | mechanical only |
| `Estimates/SourceGuardedHardCount.lean` | mechanical only |
| `Estimates/SourceInitialDiscard.lean` | mechanical only |
| `Estimates/SourceLargePairBound.lean` | mechanical only |
| `Estimates/SourceParentBenchmark.lean` | modified (4 lines added or changed) |
| `Estimates/SourceReferenceRemainders.lean` | mechanical only |
| `Estimates/SourceRepeatedRates.lean` | mechanical only |
| `Estimates/SourceRichPoints.lean` | mechanical only |
| `Estimates/SourceRichSetContradiction.lean` | mechanical only |
| `Estimates/SourceRootErrorLower.lean` | mechanical only |
| `Estimates/SourceRootReference.lean` | modified (0 lines added or changed) |
| `Estimates/SourceSamplePopulation.lean` | mechanical only |
| `Estimates/SourceSquareScale.lean` | mechanical only |
| `Estimates/UniformJointModel.lean` | mechanical only |
| `Estimates/UnlistedLocalMass.lean` | mechanical only |
| `Harmonic/OriginalSourcePolynomial.lean` | mechanical only |
| `Partitions/ActualBoxFourSum.lean` | mechanical only |
| `Partitions/ActualBoxHarmonicInverse.lean` | mechanical only |
| `Partitions/ActualBoxList.lean` | mechanical only |
| `Partitions/ActualRepeatedBinStep.lean` | mechanical only |
| `Partitions/ActualSafeBoxMass.lean` | mechanical only |
| `Partitions/BinCutGapMovement.lean` | mechanical only |
| `Partitions/BoundedEdgeBins.lean` | mechanical only |
| `Partitions/BoxHeightBudget.lean` | mechanical only |
| `Partitions/EffectiveCommonInterval.lean` | mechanical only |
| `Partitions/EffectiveCoordinateUnits.lean` | mechanical only |
| `Partitions/EffectiveCoordinates.lean` | mechanical only |
| `Partitions/EligibleBoxLists.lean` | mechanical only |
| `Partitions/FullBoxTotalLength.lean` | mechanical only |
| `Partitions/FullHypotheticalBinLower.lean` | mechanical only |
| `Partitions/FullPatternCoordinates.lean` | mechanical only |
| `Partitions/GeometricInverseGeometry.lean` | mechanical only |
| `Partitions/GeometricRangeInverse.lean` | mechanical only |
| `Partitions/GeometricSelectionHardMass.lean` | mechanical only |
| `Partitions/GeometricTotalBoxMass.lean` | mechanical only |
| `Partitions/GoodSampleSelection.lean` | mechanical only |
| `Partitions/PaperGeometricRegularity.lean` | mechanical only |
| `Partitions/RegularityDefectPartition.lean` | mechanical only |
| `Partitions/SortedLabelRepetition.lean` | mechanical only |
| `Partitions/SourceBlockFibreBound.lean` | mechanical only |
| `Partitions/SourceCanonicalKeyGeometry.lean` | mechanical only |
| `Partitions/SourceDenseCellContradiction.lean` | mechanical only |
| `Partitions/SourceIntervalReplacement.lean` | mechanical only |
| `Partitions/SourceLabelCount.lean` | mechanical only |
| `Partitions/SourceRawBoxFactory.lean` | mechanical only |
| `Partitions/SourceRefinedCell.lean` | mechanical only |
| `Partitions/TwoSingletonBins.lean` | mechanical only |
| `Paths/ActualEffectiveWitness.lean` | mechanical only |
| `Paths/ActualNearFullStopGroup.lean` | mechanical only |
| `Paths/ActualOwnerLocalComparison.lean` | mechanical only |
| `Paths/ActualPrefixClearance.lean` | mechanical only |
| `Paths/ActualSampleWitness.lean` | mechanical only |
| `Paths/ActualWordSelection.lean` | mechanical only |
| `Paths/CanonicalKeyWitness.lean` | mechanical only |
| `Paths/ExpandedHardCapture.lean` | mechanical only |
| `Paths/FiniteBoxWordMass.lean` | mechanical only |
| `Paths/FullBoxPrefixLower.lean` | mechanical only |
| `Paths/FullWordHighAlignment.lean` | mechanical only |
| `Paths/GeometricEdgeWitness.lean` | mechanical only |
| `Paths/GeometricRegularWords.lean` | mechanical only |
| `Paths/GeometricWords.lean` | mechanical only |
| `Paths/MovingStopBandParameters.lean` | mechanical only |
| `Paths/MovingStopMargins.lean` | mechanical only |
| `Paths/OutsideExceptionsWitness.lean` | mechanical only |
| `Paths/RawBoxRationalWitness.lean` | mechanical only |
| `Paths/RepeatedWordData.lean` | mechanical only |
| `Paths/SampleWitnessAverage.lean` | mechanical only |
| `Paths/SourceStopWindow.lean` | mechanical only |
| `Paths/SourceStoppedCorrection.lean` | mechanical only |
| `Paths/StoppedErrorReduction.lean` | mechanical only |
| `Paths/StoppedReferenceFinite.lean` | mechanical only |
| `Paths/WeightedIsolatedWords.lean` | mechanical only |
| `Paths/WeightedRepeatedWords.lean` | mechanical only |
| `Paths/WordIntervalGeometry.lean` | mechanical only |
| `Primes/ActualPrimeSelectors.lean` | mechanical only |
| `Primes/BoundedEdgeHighPrimes.lean` | mechanical only |
| `Primes/CrossingPrimeBin.lean` | mechanical only |
| `Primes/FrozenPrimeGroup.lean` | mechanical only |
| `Primes/FullPrimeEventFibres.lean` | mechanical only |
| `Primes/GuardedHardPrimeSets.lean` | mechanical only |
| `Primes/LatePrimeRatio.lean` | mechanical only |
| `Primes/PrimeEventCounting.lean` | mechanical only |
| `Primes/PrimePartitionCounts.lean` | mechanical only |
| `Primes/PrimeWordArithmetic.lean` | mechanical only |
| `Primes/SmallEffectivePrimeSplit.lean` | mechanical only |
| `Primes/SourcePrimeProductData.lean` | mechanical only |
| `Primes/SourceRawPrimeMass.lean` | mechanical only |
| `Primes/StoppedReferencePrimes.lean` | mechanical only |
| `Primes/TwoPrimeObservableSum.lean` | mechanical only |
| `Probability/ActualUnlistedEvent.lean` | mechanical only |
| `Probability/FullBoxVarianceGeometry.lean` | mechanical only |
| `Probability/FullPatternVariance.lean` | mechanical only |
| `Probability/MomentIndicators.lean` | mechanical only |
| `Probability/PaperSubsetTagEvent.lean` | mechanical only |
| `Probability/RegularStoppedEvent.lean` | mechanical only |
| `Probability/RepeatedPairEvents.lean` | mechanical only |
| `Probability/RepeatedPairProbability.lean` | mechanical only |
| `Probability/RepeatedWordEvents.lean` | mechanical only |
| `Probability/SingletonEventMass.lean` | mechanical only |
| `Probability/SourceFullEventCount.lean` | mechanical only |
| `Probability/SourceIsolatedProbability.lean` | mechanical only |
| `Probability/SourceMarkedStopping.lean` | mechanical only |
| `Probability/StableModelMoments.lean` | mechanical only |
| `Sieve/ActualCofactorArithmetic.lean` | mechanical only |
| `Sieve/ActualCofactorCellData.lean` | mechanical only |
| `Sieve/AlignedCofactorSplit.lean` | mechanical only |
| `Sieve/BoxWitnessFactorization.lean` | mechanical only |
| `Sieve/CRTPrimeCost.lean` | mechanical only |
| `Sieve/CofactorAllChoiceBounds.lean` | mechanical only |
| `Sieve/CoprimePositionSieve.lean` | mechanical only |
| `Sieve/EndpointCofactorSplit.lean` | mechanical only |
| `Sieve/ErasedCofactorGeometry.lean` | mechanical only |
| `Sieve/FrozenSieveMean.lean` | mechanical only |
| `Sieve/FullPatternCongruences.lean` | mechanical only |
| `Sieve/HypotheticalCofactorHit.lean` | mechanical only |
| `Sieve/LastPrimeModulusCount.lean` | mechanical only |
| `Sieve/OriginalCofactorPoints.lean` | mechanical only |
| `Sieve/OriginalCofactorSums.lean` | mechanical only |
| `Sieve/OriginalPairSieve.lean` | mechanical only |
| `Sieve/RefinementPrimeCongruences.lean` | mechanical only |
| `Sieve/ResidueProjection.lean` | mechanical only |
