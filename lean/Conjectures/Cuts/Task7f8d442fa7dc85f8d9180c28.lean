import Mathlib

open scoped Classical

namespace Conjectures.Cuts.Task7f8d442fa7dc85f8d9180c28

lemma finite_gap_bound (B : Set ℕ) (N K : ℕ) (hK : 0 < K) :
    ((Finset.Icc 1 N).filter (fun n => n ∈ B)).card ≤
      N / K + 1 + ∑ h ∈ Finset.Icc 1 K,
        ((Finset.Icc 1 N).filter (fun n => n ∈ B ∧ n + h ∈ B)).card := by
  classical
  let S := (Finset.Icc 1 N).filter (fun n => n ∈ B)
  let F := S.filter (fun n => ∀ h ∈ Finset.Icc 1 K, n + h ∉ B)
  let D := fun h : ℕ => (Finset.Icc 1 N).filter (fun n => n ∈ B ∧ n + h ∈ B)
  have inject : Set.InjOn (fun n : ℕ => n / K) (↑F : Set ℕ) := by
    intro a ha b hb hab
    have sep : ∀ {a b}, a ∈ F → b ∈ F → a < b → a / K ≠ b / K := by
      intro a b ha hb hab heq
      have hA := (Finset.mem_filter.mp ha).2
      have hB := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
      have hdiff : b - a ≤ K := by
        have ha0 := Nat.div_mul_le_self a K
        have hb0 := Nat.mod_add_div b K
        have hb1 := Nat.mod_lt b hK
        rw [Nat.mul_comm K (b / K), ← heq] at hb0
        omega
      have hp := hA (b-a) (Finset.mem_Icc.mpr ⟨by omega,hdiff⟩)
      exact hp (by simpa [Nat.add_sub_of_le hab.le] using hB)
    rcases lt_trichotomy a b with h | h | h
    · exact (sep ha hb h hab).elim
    · exact h
    · exact (sep hb ha h hab.symm).elim
  have hf : F.card ≤ N / K + 1 := by
    have h := Finset.card_le_card_of_injOn (s := F) (t := Finset.range (N / K + 1))
      (fun n => n / K) (by
        intro n hn
        have hN := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).2
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hN))) inject
    simpa using h
  have cover : S ⊆ F ∪ (Finset.Icc 1 K).biUnion D := by
    intro n hn
    by_cases hnF : n ∈ F
    · exact Finset.mem_union_left _ hnF
    · have ht : ¬ ∀ h ∈ Finset.Icc 1 K, n + h ∉ B := by
        intro h
        exact hnF (Finset.mem_filter.mpr ⟨hn,h⟩)
      push Not at ht
      obtain ⟨h, hh, hsum⟩ := ht
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨h,hh,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1,(Finset.mem_filter.mp hn).2,hsum⟩⟩)
  calc S.card ≤ (F ∪ (Finset.Icc 1 K).biUnion D).card := Finset.card_le_card cover
    _ ≤ F.card + ((Finset.Icc 1 K).biUnion D).card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add hf (Finset.card_biUnion_le)

theorem differenceCriterion :
    ∀ B : Set ℕ,
      (∀ h : ℕ, 0 < h → ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N ≥ T,
        (((Finset.Icc 1 N).filter (fun n => n ∈ B ∧ n + h ∈ B)).card : ℝ) ≤ ε * (N : ℝ)) →
      ∀ η : ℝ, 0 < η → ∃ T : ℕ, ∀ N ≥ T,
        (((Finset.Icc 1 N).filter (fun n => n ∈ B)).card : ℝ) ≤ η * (N : ℝ) := by
  classical
  intro B hB η hη
  obtain ⟨K,hKη⟩ := exists_nat_gt (4 / η)
  have hK : (0 : ℝ) < K := lt_trans (by positivity : 0 < 4 / η) hKη
  have hKnat : 0 < K := by exact_mod_cast hK
  have hKprod := (div_lt_iff₀ hη).mp hKη
  let δ := η / (2 * (K : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hex (h : ℕ) : ∃ T : ℕ, ∀ N ≥ T, 0 < h →
      (((Finset.Icc 1 N).filter (fun n => n ∈ B ∧ n + h ∈ B)).card : ℝ) ≤ δ * (N : ℝ) := by
    by_cases hh : 0 < h
    · obtain ⟨T,hT⟩ := hB h hh δ hδ
      exact ⟨T,fun N hN _ => hT N hN⟩
    · exact ⟨0,fun _ _ hn => (hh hn).elim⟩
  choose T hT using hex
  refine ⟨max K ((Finset.Icc 1 K).sup T), ?_⟩
  intro N hN
  have hKN : (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_trans (le_max_left _ _) hN)
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have small : (↑(N / K) : ℝ) + 1 ≤ η / 2 * N := by
    have hA : (N : ℝ) / K ≤ (η / 4) * N := by
      apply (div_le_iff₀ hK).mpr
      nlinarith [mul_nonneg hN0 (le_of_lt (sub_pos.mpr hKprod))]
    have hB : (1 : ℝ) ≤ (N : ℝ) / K := (le_div_iff₀ hK).mpr (by simpa using hKN)
    linarith [Nat.cast_div_le (m := N) (n := K) (α := ℝ)]
  let D := fun h : ℕ => (Finset.Icc 1 N).filter (fun n => n ∈ B ∧ n + h ∈ B)
  have hsum : (∑ h ∈ Finset.Icc 1 K, ((D h).card : ℝ)) ≤ η / 2 * N := by
    calc
      _ ≤ ∑ _h ∈ Finset.Icc 1 K, δ * (N : ℝ) := by
        apply Finset.sum_le_sum
        intro h hh
        exact hT h N ((Finset.le_sup hh).trans ((le_max_right _ _).trans hN)) (Finset.mem_Icc.mp hh).1
      _ = η / 2 * N := by
        simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
        dsimp [δ]
        field_simp
  have hcomb := finite_gap_bound B N K hKnat
  have hcast : (((Finset.Icc 1 N).filter (fun n => n ∈ B)).card : ℝ) ≤
      (↑(N / K) : ℝ) + 1 + ∑ h ∈ Finset.Icc 1 K, ((D h).card : ℝ) := by
    exact_mod_cast hcomb
  linarith

end Conjectures.Cuts.Task7f8d442fa7dc85f8d9180c28

theorem Conjectures.Cuts.Task7f8d442fa7dc85f8d9180c28 : (∀ (x1 : Set ℕ), (∀ (x2 : ℕ), (0 : ℕ) < x2 → ∀ (x4 : ℝ), (0 : ℝ) < x4 → ∃ (x6 : ℕ), ∀ x7 ≥ x6, ↑(Set.Icc (1 : ℕ) x7 ∩ {x9 : ℕ | x9 ∈ x1 ∧ x9 + x2 ∈ x1}).ncard ≤ x4 * ↑x7) → ∀ (x3 : ℝ), (0 : ℝ) < x3 → ∃ (x5 : ℕ), ∀ x6 ≥ x5, ↑(Set.Icc (1 : ℕ) x6 ∩ x1).ncard ≤ x3 * ↑x6) := by
  classical
  have count (N : ℕ) (U : Set ℕ) :
      (Set.Icc 1 N ∩ U).ncard = ((Finset.Icc 1 N).filter (fun n => n ∈ U)).card := by
    rw [show Set.Icc 1 N ∩ U = (↑((Finset.Icc 1 N).filter (fun n => n ∈ U)) : Set ℕ) by
      ext n
      simp]
    exact Set.ncard_coe_finset _
  intro B hB η hη
  obtain ⟨T, hT⟩ := Conjectures.Cuts.Task7f8d442fa7dc85f8d9180c28.differenceCriterion B (by
    intro h hh ε hε
    obtain ⟨T, hT⟩ := hB h hh ε hε
    refine ⟨T, fun N hN => ?_⟩
    simpa only [count, Set.mem_ofPred_eq] using hT N hN) η hη
  exact ⟨T, fun N hN => by simpa only [count] using hT N hN⟩

