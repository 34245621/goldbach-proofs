import Mathlib

-- child 1 zh: 在无界素数边长的四条平移抛物线上，每列选两点并给全部候选点排定次序。除去少于半个边长且留有固定比例余量的例外点，每个候选点在每条经过它的非竖直直线上至多有一个后继。
-- child 1 en: Choose two points per column on four translated parabolas at unbounded primes and rank them. Except for at most a fixed fraction below half the side length, each point has at most one later candidate on each nonvertical line through it.
-- child 2 zh: 有限标号点集的秩互异。若每一点在集合中至多有一个秩比它大的点，则集合至多有两个点。
-- child 2 en: A finite set of distinctly ranked labels has size at most two if each member has at most one higher-ranked member in the set.
theorem Conjectures.Cuts.Cut913e43a24b311252cc4b89ad
    (profiles : ∃ d : ℝ, 0 < d ∧ ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧
      ∃ A b : ZMod p, A ≠ 0 ∧ ∃ L : Fin 4 → ZMod p, Function.Injective L ∧
      let x := fun (u : Fin p × Fin 4) => (u.1.val : ℤ)
      let y := fun (u : Fin p × Fin 4) =>
        ((A * (u.1.val : ZMod p)^2 + b * u.1.val + L u.2).val : ℤ)
      ∃ T E : Finset (Fin p × Fin 4), ∃ r : Fin p × Fin 4 → ℕ,
        Function.Injective r ∧ T.card = 2*p ∧
        (∀ c, {u ∈ T | u.1 = c}.card ≤ 2) ∧
        (E.card : ℝ) ≤ (1/2-d)*(p : ℝ) ∧
        ∀ u ∈ T \ E, ∀ a b : ℤ, a ≠ 0 →
          {v ∈ T | r u < r v ∧ a*(y v - y u) = b*(x v - x u)}.card ≤ 1)
    (rankBound : ∀ (p : ℕ) (S : Finset (Fin p × Fin 4)) (r : Fin p × Fin 4 → ℕ),
      Function.Injective r → (∀ u ∈ S, {v ∈ S | r u < r v}.card ≤ 1) → S.card ≤ 2) : (∃ (x1 : ℝ),   (0 : ℝ) < x1 ∧     ∀ (x2 : ℕ),       ∃ (x3 : ℕ),         x2 < x3 ∧           Nat.Prime x3 ∧             ∃ (x4 : ZMod x3) (x5 : ZMod x3),               x4 ≠ (0 : ZMod x3) ∧                 ∃ (x6 : Fin (4 : ℕ) → ZMod x3),                   Function.Injective x6 ∧                     ∃ (x7 : Finset (Fin x3 × Fin (4 : ℕ))),                       (↑x7.card : ℝ) ≤ ((5 / 2 : ℝ) - x1) * (↑x3 : ℝ) ∧                         have x8 : Fin x3 × Fin (4 : ℕ) → ZMod x3 := fun (x8 : Fin x3 × Fin (4 : ℕ)) => (↑(↑x8.1 : ℕ) : ZMod x3);                         have x9 : Fin x3 × Fin (4 : ℕ) → ZMod x3 := fun (x9 : Fin x3 × Fin (4 : ℕ)) => x4 * x8 x9 ^ (2 : ℕ) + x5 * x8 x9 + x6 x9.2;                         have x10 : Fin x3 × Fin (4 : ℕ) → ℕ × ℕ := fun (x10 : Fin x3 × Fin (4 : ℕ)) => ((↑x10.1 : ℕ), (x9 x10).val);                         have x11 : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ → Prop := fun (x11 x12 x13 : ℕ × ℕ) => ((↑x12.1 : ℤ) - (↑x11.1 : ℤ)) * ((↑x13.2 : ℤ) - (↑x11.2 : ℤ)) = ((↑x12.2 : ℤ) - (↑x11.2 : ℤ)) * ((↑x13.1 : ℤ) - (↑x11.1 : ℤ));                         have x12 : Fin x3 × Fin (4 : ℕ) → Fin x3 × Fin (4 : ℕ) → Fin x3 × Fin (4 : ℕ) → Prop := fun (x12 x13 x14 : Fin x3 × Fin (4 : ℕ)) =>                           if x12.1 = x13.1 then x14.1 = x12.1                           else                             have x15 : ZMod x3 := (x9 x13 - x9 x12) * (x8 x13 - x8 x12)⁻¹;                             have x16 : ZMod x3 := x9 x12 - x15 * x8 x12;                             ((2 : ZMod x3) * x4 * x8 x14 + x5 - x15) ^ (2 : ℕ) = (x5 - x15) ^ (2 : ℕ) - (4 : ZMod x3) * x4 * (x6 x14.2 - x16);                         ∀ (x13 x14 x15 : Fin x3 × Fin (4 : ℕ)), x13 ≠ x14 → x13 ≠ x15 → x14 ≠ x15 → x12 x13 x14 x15 → x11 (x10 x13) (x10 x14) (x10 x15) → x13 ∈ x7 ∨ x14 ∈ x7 ∨ x15 ∈ x7) := by
  classical
  obtain ⟨d, hd, build⟩ := profiles
  refine ⟨d, hd, ?_⟩
  intro B
  obtain ⟨p, hpB, hp, A, b, hA, L, hL, T, E, r, hr, hT, hColumn, hE, hLater⟩ := build B
  let x := fun (u : Fin p × Fin 4) => (u.1.val : ℤ)
  let y := fun (u : Fin p × Fin 4) =>
    ((A * (u.1.val : ZMod p)^2 + b * u.1.val + L u.2).val : ℤ)
  let D := Tᶜ ∪ E
  refine ⟨p, hpB, hp, A, b, hA, L, hL, D, ?_, ?_⟩
  · have hcomp := T.card_compl_add_card
    simp only [Fintype.card_prod, Fintype.card_fin] at hcomp
    have hsize : Tᶜ.card = 2*p := by omega
    have hUnion := Finset.card_union_le Tᶜ E
    rw [hsize] at hUnion
    have hcast : (D.card : ℝ) ≤ 2*(p : ℝ) + E.card := by exact_mod_cast hUnion
    nlinarith only [hcast, hE]
  · intro X Y pt aligned candidate i j k hij hik hjk shadow col
    by_contra! hmiss
    have retained (v : Fin p × Fin 4) (hv : v ∉ D) : v ∈ T \ E := by
      simpa [D] using hv
    obtain ⟨hi, hj, hk⟩ := hmiss
    have hiR := retained i hi
    have hjR := retained j hj
    have hkR := retained k hk
    have three (S : Finset (Fin p × Fin 4)) (hiS : i ∈ S) (hjS : j ∈ S) (hkS : k ∈ S) :
        2 < S.card := by
      have hsub : {i,j,k} ⊆ S := by
        exact Finset.insert_subset hiS (Finset.insert_subset hjS (Finset.singleton_subset_iff.mpr hkS))
      have hcard := Finset.card_le_card hsub
      have hc : 3 ≤ S.card := by simpa [hij, hik, hjk] using hcard
      omega
    by_cases heq : i.1 = j.1
    · have hki : k.1 = i.1 := by simpa only [candidate, ite_eq_left heq] using shadow
      apply (hColumn i.1).not_gt
      exact three _ (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hiR).1, rfl⟩)
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hjR).1, heq.symm⟩)
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hkR).1, hki⟩)
    · let a := x j - x i
      let t := y j - y i
      have ha : a ≠ 0 := by
        intro hz
        apply heq
        apply Fin.ext
        dsimp [a, x] at hz
        omega
      let line := (T \ E).filter fun v => a*(y v - y i) = t*(x v - x i)
      have load : line.card ≤ 2 := by
        apply rankBound p line r hr
        intro u hu
        obtain ⟨huR, huLine⟩ := Finset.mem_filter.mp hu
        apply le_trans (Finset.card_le_card ?_) (hLater u huR a t ha)
        intro v hv
        obtain ⟨hvLine, hRank⟩ := Finset.mem_filter.mp hv
        obtain ⟨hvR, hvEq⟩ := Finset.mem_filter.mp hvLine
        refine Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hvR).1, hRank, ?_⟩
        change a*(y v - y u) = t*(x v - x u)
        change a*(y v - y i) = t*(x v - x i) at hvEq
        change a*(y u - y i) = t*(x u - x i) at huLine
        linear_combination hvEq - huLine
      apply load.not_gt
      exact three line (Finset.mem_filter.mpr ⟨hiR, by simp⟩)
        (Finset.mem_filter.mpr ⟨hjR, by dsimp [a, t]; ring⟩)
        (Finset.mem_filter.mpr ⟨hkR, col⟩)
