import ResearchSupport.GRHSource.Lib.CM.Sigma.PadicSeriesDefs
import ResearchSupport.GRHSource.Lib.DiscreteSeries.CuspKernel.BesselSchurBound
import ResearchSupport.GRHSource.Lib.Weil.Periods.DegreeOfT

/-! General lemmas of group theory (textbook or folklore).

This file: Index of a finite product of subgroups is the product of indices. -/

lemma index_pi_univ {I G} [Fintype I] [∀ i, Group (G i)] H :
    (@Subgroup.pi I G _ .univ H).index = ∏ i, (H i).index :=
  (Nat.card_congr (QuotientGroup.leftRel_pi H ▸ Setoid.piQuotientEquiv _) ▸ Nat.card_pi :)
