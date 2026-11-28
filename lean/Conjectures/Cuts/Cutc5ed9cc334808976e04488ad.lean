import Mathlib
import Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b
import Conjectures.Cuts.Taskc1374e5a144c390fd55782fc

open Finset Filter Polynomial

-- child 1 en: Bound residual collisions of cubic polynomial quadruple sums with no equal proper subsums of the same length on opposite sides, by C M^ε |A|⁵.
-- child 1 zh: 对三次整系数多项式，控制剩余四元组碰撞中左右无等长真子和相等的部分，上界为 C M^ε |A|⁵。
-- child 2 en: Bound residual collisions of polynomial quadruple sums of degree at least four with no equal proper subsums of the same length on opposite sides, by C M^ε |A|⁴.
-- child 2 zh: 对次数至少为四的整系数多项式，控制剩余四元组碰撞中左右无等长真子和相等的部分，上界为 C M^ε |A|⁴。

theorem Conjectures.Cuts.Cutc5ed9cc334808976e04488ad
  (h₁ : ∀ P : Polynomial ℤ, P.natDegree = 3 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Finset.Icc 1 M,
    let v (a : ℕ) : ℤ := P.eval (a : ℤ)
    let T := Fintype.piFinset (fun _ : Fin 4 => A)
    let w (x : Fin 4 → ℕ) := ∑ i, v (x i)
    let S := (T.product T).filter (fun z => w z.1 = w z.2 ∧
      ∀ ij : Fin 4 × Fin 4, z.1 ij.1 ≠ z.2 ij.2)
    let R := S.filter (fun z => ∀ ij kl : Fin 4 × Fin 4, ij.1 ≠ ij.2 → kl.1 ≠ kl.2 →
      z.1 ij.1 + z.1 ij.2 ≠ z.2 kl.1 + z.2 kl.2 ∧
      z.1 ij.1 ^ 2 + z.1 ij.2 ^ 2 ≠ z.2 kl.1 ^ 2 + z.2 kl.2 ^ 2)
    let One (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) := ∃ ij : Fin 4 × Fin 4,
      v (z.1 ij.1) = v (z.2 ij.2)
    let Two (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) := ∃ ij kl : Fin 4 × Fin 4,
      ij.1 ≠ ij.2 ∧ kl.1 ≠ kl.2 ∧
      v (z.1 ij.1) + v (z.1 ij.2) = v (z.2 kl.1) + v (z.2 kl.2)
    ((R.filter (fun z => ¬ One z ∧ ¬ Two z)).card : ℝ) ≤
      C * (M : ℝ)^ε * (A.card : ℝ)^5)
  (h₂ : ∀ P : Polynomial ℤ, 4 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Finset.Icc 1 M,
    let v (a : ℕ) : ℤ := P.eval (a : ℤ)
    let T := Fintype.piFinset (fun _ : Fin 4 => A)
    let w (x : Fin 4 → ℕ) := ∑ i, v (x i)
    let S := (T.product T).filter (fun z => w z.1 = w z.2 ∧
      ∀ ij : Fin 4 × Fin 4, z.1 ij.1 ≠ z.2 ij.2)
    let R := S.filter (fun z => ∀ ij kl : Fin 4 × Fin 4, ij.1 ≠ ij.2 → kl.1 ≠ kl.2 →
      z.1 ij.1 + z.1 ij.2 ≠ z.2 kl.1 + z.2 kl.2 ∧
      z.1 ij.1 ^ 2 + z.1 ij.2 ^ 2 ≠ z.2 kl.1 ^ 2 + z.2 kl.2 ^ 2)
    let One (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) := ∃ ij : Fin 4 × Fin 4,
      v (z.1 ij.1) = v (z.2 ij.2)
    let Two (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) := ∃ ij kl : Fin 4 × Fin 4,
      ij.1 ≠ ij.2 ∧ kl.1 ≠ kl.2 ∧
      v (z.1 ij.1) + v (z.1 ij.2) = v (z.2 kl.1) + v (z.2 kl.2)
    ((R.filter (fun z => ¬ One z ∧ ¬ Two z)).card : ℝ) ≤
      C * (M : ℝ)^ε * (A.card : ℝ)^4) : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (4 : ℕ)) => x8;                   let x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12) : ℤ) x1;                   have x12 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Fin (4 : ℕ) × Fin (4 : ℕ)), x12.1 x13.1 ≠ x12.2 x13.2};                   (↑{x13 ∈ x12 | ∀ (x14 x15 : Fin (4 : ℕ) × Fin (4 : ℕ)), x14.1 ≠ x14.2 → x15.1 ≠ x15.2 → x13.1 x14.1 + x13.1 x14.2 ≠ x13.2 x15.1 + x13.2 x15.2 ∧ x13.1 x14.1 ^ (2 : ℕ) + x13.1 x14.2 ^ (2 : ℕ) ≠ x13.2 x15.1 ^ (2 : ℕ) + x13.2 x15.2 ^ (2 : ℕ)}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ)) := by
  classical
  have selfEventuallyInjective (Q : Polynomial ℝ) (hQ : 2 ≤ Q.natDegree) :
      ∃ t : ℝ, Set.InjOn Q.eval (Set.Ici t) := by
    have hd : 0 < Q.derivative.degree := natDegree_pos_iff_degree_pos.mp (by rw [natDegree_derivative]; omega)
    rcases le_total 0 Q.derivative.leadingCoeff with hc | hc
    · have h := (Q.derivative.tendsto_atTop_of_leadingCoeff_nonneg hd hc).eventually_gt_atTop 0
      obtain ⟨t, ht⟩ := eventually_atTop.mp h
      refine ⟨t, (strictMonoOn_of_deriv_pos (convex_Ici t) Q.continuous.continuousOn ?_).injOn⟩
      intro x hx
      rw [Q.deriv]
      exact ht x (interior_subset hx)
    · have h := (Q.derivative.tendsto_atBot_of_leadingCoeff_nonpos hd hc).eventually_lt_atBot 0
      obtain ⟨t, ht⟩ := eventually_atTop.mp h
      refine ⟨t, (strictAntiOn_of_deriv_neg (convex_Ici t) Q.continuous.continuousOn ?_).injOn⟩
      intro x hx
      rw [Q.deriv]
      exact ht x (interior_subset hx)

  have selfBound (P : Polynomial ℤ) (hP : 3 ≤ P.natDegree) :
      ∃ K : ℕ, ∀ A : Finset ℕ,
        ((A.product A).filter fun z => z.1 ≠ z.2 ∧ P.eval (z.1 : ℤ) = P.eval (z.2 : ℤ)).card ≤ K := by
    let Q := P.map (Int.castRingHom ℝ)
    have hdeg : Q.natDegree = P.natDegree := natDegree_map_eq_of_injective Int.cast_injective P
    have hd : 2 ≤ Q.natDegree := by omega
    obtain ⟨t, ht⟩ := selfEventuallyInjective Q hd
    obtain ⟨T, hT⟩ := exists_nat_ge t
    have hQ (a : ℕ) : Q.eval (a : ℝ) = ((P.eval (a : ℤ) : ℤ) : ℝ) := by
      simpa only [Int.cast_natCast, Int.coe_castRingHom] using P.eval_map_apply (Int.castRingHom ℝ) (a : ℤ)
    have hi {a b : ℕ} (ha : T ≤ a) (hb : T ≤ b) (h : Q.eval (a : ℝ) = Q.eval (b : ℝ)) : a = b := by
      exact_mod_cast (ht (hT.trans (Nat.cast_le.mpr ha)) (hT.trans (Nat.cast_le.mpr hb)) h)
    have hdegpos : 0 < Q.degree := natDegree_pos_iff_degree_pos.mp (by omega)
    have hlim : Tendsto (fun n : ℕ => |Q.eval (n : ℝ)|) atTop atTop :=
      (Q.abs_tendsto_atTop hdegpos).comp tendsto_natCast_atTop_atTop
    have hsep : ∀ᶠ n : ℕ in atTop, ∀ a ∈ range T, |Q.eval (a : ℝ)| < |Q.eval (n : ℝ)| :=
      (eventually_all_finset _).mpr fun a _ => hlim.eventually_gt_atTop _
    obtain ⟨S, hS⟩ := eventually_atTop.mp hsep
    let B := max T S
    have hbound {a b : ℕ} (hab : a ≠ b) (he : Q.eval (a : ℝ) = Q.eval (b : ℝ)) : a < B := by
      by_contra! h
      have haT : T ≤ a := (le_max_left _ _).trans h
      by_cases hbT : T ≤ b
      · exact hab (hi haT hbT he)
      · have hlt := hS a ((le_max_right _ _).trans h) b (mem_range.mpr (lt_of_not_ge hbT))
        rw [he] at hlt
        exact (lt_irrefl _ hlt)
    refine ⟨((range B).product (range B)).card, fun A => card_le_card ?_⟩
    rintro ⟨a,b⟩ h
    obtain ⟨_, hab, he⟩ := mem_filter.mp h
    have he' : Q.eval (a : ℝ) = Q.eval (b : ℝ) := by rw [hQ, hQ, he]
    exact mem_product.mpr ⟨mem_range.mpr (hbound hab he'), mem_range.mpr (hbound hab.symm he'.symm)⟩
  have singleBound (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
      (ε : ℝ) (hε : 0 < ε) (K : ℕ)
      (hK : ∀ A : Finset ℕ, ((A.product A).filter (fun t =>
        t.1 ≠ t.2 ∧ P.eval (t.1 : ℤ) = P.eval (t.2 : ℤ))).card ≤ K) :
      ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Finset.Icc 1 M,
        let v (a : ℕ) := P.eval (a : ℤ)
        let T := Fintype.piFinset fun _ : Fin 4 => A
        let w (x : Fin 4 → ℕ) := ∑ i, v (x i)
        (((T.product T).filter (fun z => w z.1 = w z.2 ∧
          (∀ ij : Fin 4 × Fin 4, z.1 ij.1 ≠ z.2 ij.2) ∧
          ∃ ij : Fin 4 × Fin 4, v (z.1 ij.1) = v (z.2 ij.2))).card : ℝ) ≤
          C * (M : ℝ)^ε * (A.card : ℝ)^4 := by
    have countSingle (A : Finset ℕ) (v : ℕ → ℤ) :
        let T := Fintype.piFinset fun _ : Fin 4 => A
        let w (x : Fin 4 → ℕ) := ∑ i, v (x i)
        let U := Fintype.piFinset fun _ : Fin 3 => A
        let u (x : Fin 3 → ℕ) := ∑ i, v (x i)
        ((T.product T).filter (fun z => w z.1 = w z.2 ∧
          (∀ ij : Fin 4 × Fin 4, z.1 ij.1 ≠ z.2 ij.2) ∧
          ∃ ij : Fin 4 × Fin 4, v (z.1 ij.1) = v (z.2 ij.2))).card ≤
          16 * (((A.product A).filter (fun t => t.1 ≠ t.2 ∧ v t.1 = v t.2)).card *
            ((U.product U).filter (fun z => u z.1 = u z.2)).card) := by
      intro T w U u
      let B := (A.product A).filter (fun t => t.1 ≠ t.2 ∧ v t.1 = v t.2)
      let H := (U.product U).filter (fun z => u z.1 = u z.2)
      let J := (Finset.univ : Finset (Fin 4 × Fin 4))
      let D (j : Fin 4 × Fin 4) := (B.product H).image (fun p =>
        (j.1.insertNth (α := fun _ => ℕ) p.1.1 p.2.1, j.2.insertNth (α := fun _ => ℕ) p.1.2 p.2.2))
      apply le_trans (b := (J.biUnion D).card)
      · apply Finset.card_le_card
        intro z hz
        obtain ⟨hzT, hw, hn, j, hmatch⟩ := Finset.mem_filter.mp hz
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp hzT
        have hx' := Fintype.mem_piFinset.mp hx
        have hy' := Fintype.mem_piFinset.mp hy
        refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, Finset.mem_image.mpr
          ⟨((z.1 j.1, z.2 j.2), (j.1.removeNth z.1, j.2.removeNth z.2)), ?_, ?_⟩⟩
        · apply Finset.mem_product.mpr
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx' _, hy' _⟩, hn j, hmatch⟩, ?_⟩
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr (fun i => hx' (j.1.succAbove i)),
            Fintype.mem_piFinset.mpr (fun i => hy' (j.2.succAbove i))⟩, ?_⟩
          have h₁ := Fin.add_sum_removeNth j.1 (fun i => v (z.1 i))
          have h₂ := Fin.add_sum_removeNth j.2 (fun i => v (z.2 i))
          change v (z.1 j.1) + u (j.1.removeNth z.1) = w z.1 at h₁
          change v (z.2 j.2) + u (j.2.removeNth z.2) = w z.2 at h₂
          change u (j.1.removeNth z.1) = u (j.2.removeNth z.2)
          omega
        · simp only [Fin.insertNth_self_removeNth, Prod.mk.eta]
      · have h := Finset.card_biUnion_le_card_mul J D (B.product H).card (fun _ _ => Finset.card_image_le)
        simpa [J, B, H, Finset.card_product] using h
    obtain ⟨c, hc, hpair⟩ := Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b P hP ε hε
    refine ⟨16 * ((K : ℝ) + 1) * c, by positivity, ?_⟩
    intro M hM A hA v T w
    let U := Fintype.piFinset fun _ : Fin 3 => A
    let u (x : Fin 3 → ℕ) := ∑ i, v (x i)
    let H := (U.product U).filter (fun z => u z.1 = u z.2)
    let B := (A.product A).filter (fun t => t.1 ≠ t.2 ∧ v t.1 = v t.2)
    let G := (Finset.univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
      (fun z => (∑ i, v (z.1 i)) = ∑ i, v (z.2 i))
    have h := countSingle A v
    have htrip : H.card ≤ A.card ^ 2 * G.card := CubicTripleCount.triple_le A v
    have hB : B.card ≤ K + 1 := (hK A).trans (Nat.le_succ K)
    have hcount := h.trans (Nat.mul_le_mul_left 16 (Nat.mul_le_mul hB htrip))
    have hG : (G.card : ℝ) ≤ c * (M : ℝ)^ε * (A.card : ℝ)^2 := hpair M hM A hA
    calc
      _ ≤ 16 * (((K : ℝ) + 1) * ((A.card : ℝ)^2 * G.card)) := by exact_mod_cast hcount
      _ ≤ 16 * (((K : ℝ) + 1) * ((A.card : ℝ)^2 * (c * (M : ℝ)^ε * (A.card : ℝ)^2))) := by
        gcongr
      _ = _ := by ring
  have pairBound (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (ε : ℝ) (hε : 0 < ε) :
      ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Finset.Icc 1 M,
        let v := fun a : ℕ => P.eval (a : ℤ)
        let T := Fintype.piFinset fun _ : Fin 4 => A
        let w := fun x : Fin 4 → ℕ => ∑ i, v (x i)
        (((T.product T).filter (fun z => w z.1 = w z.2 ∧
          ∃ ij kl : Fin 4 × Fin 4, ij.1 ≠ ij.2 ∧ kl.1 ≠ kl.2 ∧
            v (z.1 ij.1) + v (z.1 ij.2) = v (z.2 kl.1) + v (z.2 kl.2))).card : ℝ) ≤
          C * (M : ℝ)^ε * (A.card : ℝ)^4 := by
    let energy (A : Finset ℕ) (v : ℕ → ℤ) : ℕ :=
      ((Finset.univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
        (fun z => (∑ i, v (z.1 i)) = ∑ i, v (z.2 i))).card

    have fixed_le (A : Finset ℕ) (v : ℕ → ℤ) :
        let T := Fintype.piFinset fun _ : Fin 4 => A
        let w := fun x : Fin 4 → ℕ => ∑ i, v (x i)
        ((T.product T).filter (fun z => w z.1 = w z.2 ∧
          v (z.1 0) + v (z.1 1) = v (z.2 0) + v (z.2 1))).card ≤
          energy A v * energy A v := by
      classical
      intro T w
      let S := (T.product T).filter (fun z => w z.1 = w z.2 ∧
        v (z.1 0) + v (z.1 1) = v (z.2 0) + v (z.2 1))
      let B := (Fin 2 → ↥A) × (Fin 2 → ↥A)
      have mems (z : ↥S) : (∀ i, z.val.1 i ∈ A) ∧ (∀ i, z.val.2 i ∈ A) := by
        obtain ⟨hl, hr⟩ := Finset.mem_product.mp (Finset.mem_filter.mp z.prop).1
        exact ⟨Fintype.mem_piFinset.mp hl, Fintype.mem_piFinset.mp hr⟩
      let head (z : ↥S) : B :=
        (fun i => ⟨z.val.1 i.castSucc.castSucc, (mems z).1 _⟩,
         fun i => ⟨z.val.2 i.castSucc.castSucc, (mems z).2 _⟩)
      let tail (z : ↥S) : B :=
        (fun i => ⟨z.val.1 i.succ.succ, (mems z).1 _⟩,
         fun i => ⟨z.val.2 i.succ.succ, (mems z).2 _⟩)
      let G := (Finset.univ : Finset B).filter
        (fun z => (∑ i, v (z.1 i)) = ∑ i, v (z.2 i))
      let split (z : ↥S) := (head z, tail z)
      have into (z : ↥S) (_ : z ∈ Finset.univ) : split z ∈ G.product G := by
        obtain ⟨hs,hh⟩ := (Finset.mem_filter.mp z.prop).2
        apply Finset.mem_product.mpr
        constructor
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          simp only [Fin.sum_univ_two]
          change v (z.val.1 0) + v (z.val.1 1) = v (z.val.2 0) + v (z.val.2 1)
          exact hh
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          simp only [w, Fin.sum_univ_four] at hs
          simp only [Fin.sum_univ_two]
          change v (z.val.1 2) + v (z.val.1 3) = v (z.val.2 2) + v (z.val.2 3)
          omega
      have inj : Set.InjOn split (↑(Finset.univ : Finset ↥S) : Set ↥S) := by
        intro x hx y hy he
        have h : head x = head y := congrArg Prod.fst he
        have t : tail x = tail y := congrArg Prod.snd he
        have hL (i : Fin 2) := congrArg (fun q : B => (q.1 i : ℕ)) h
        have hR (i : Fin 2) := congrArg (fun q : B => (q.2 i : ℕ)) h
        have tL (i : Fin 2) := congrArg (fun q : B => (q.1 i : ℕ)) t
        have tR (i : Fin 2) := congrArg (fun q : B => (q.2 i : ℕ)) t
        apply Subtype.ext
        apply Prod.ext
        · funext i
          fin_cases i
          · exact hL 0
          · exact hL 1
          · exact tL 0
          · exact tL 1
        · funext i
          fin_cases i
          · exact hR 0
          · exact hR 1
          · exact tR 0
          · exact tR 1
      have hn := Finset.card_le_card_of_injOn split into inj
      have hc : (G.product G).card = G.card * G.card := Finset.card_product G G
      rw [hc, Finset.card_univ, Fintype.card_coe] at hn
      exact hn

    have move_pair (i j : Fin 4) (h : i ≠ j) :
        ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := by
      let τ := Equiv.swap 0 i
      have hτ : τ 0 = i := Equiv.swap_apply_left _ _
      have h0 : (0 : Fin 4) ≠ τ.symm j := by
        intro he
        exact h (hτ.symm.trans ((congrArg τ he).trans (τ.apply_symm_apply j)))
      refine ⟨(Equiv.swap 1 (τ.symm j)).trans τ, ?_, ?_⟩
      · change τ (Equiv.swap 1 (τ.symm j) 0) = i
        rw [Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 4) ≠ 1) h0, hτ]
      · change τ (Equiv.swap 1 (τ.symm j) 1) = j
        rw [Equiv.swap_apply_left, τ.apply_symm_apply]

    have any_le (A : Finset ℕ) (v : ℕ → ℤ) :
        let T := Fintype.piFinset fun _ : Fin 4 => A
        let w := fun x : Fin 4 → ℕ => ∑ i, v (x i)
        ((T.product T).filter (fun z => w z.1 = w z.2 ∧
          ∃ ij kl : Fin 4 × Fin 4, ij.1 ≠ ij.2 ∧ kl.1 ≠ kl.2 ∧
          v (z.1 ij.1) + v (z.1 ij.2) = v (z.2 kl.1) + v (z.2 kl.2))).card ≤
          576 * (energy A v * energy A v) := by
      classical
      intro T w
      let D := (T.product T).filter (fun z => w z.1 = w z.2 ∧
        v (z.1 0) + v (z.1 1) = v (z.2 0) + v (z.2 1))
      let perms := (Finset.univ : Finset (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)))
      let blocks (p : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)) :=
        D.image (fun z => (z.1 ∘ p.1.symm, z.2 ∘ p.2.symm))
      apply le_trans (b := (perms.biUnion blocks).card)
      · apply Finset.card_le_card
        intro z hz
        obtain ⟨hzT, hw, ij, kl, hi, hk, hmatch⟩ := Finset.mem_filter.mp hz
        obtain ⟨hxT, hyT⟩ := Finset.mem_product.mp hzT
        obtain ⟨σ,hσ₀,hσ₁⟩ := move_pair _ _ hi
        obtain ⟨τ,hτ₀,hτ₁⟩ := move_pair _ _ hk
        apply Finset.mem_biUnion.mpr
        refine ⟨(σ,τ), Finset.mem_univ _, Finset.mem_image.mpr ⟨(z.1 ∘ σ, z.2 ∘ τ), ?_, ?_⟩⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_, ?_⟩
          · exact Fintype.mem_piFinset.mpr fun i => Fintype.mem_piFinset.mp hxT (σ i)
          · exact Fintype.mem_piFinset.mpr fun i => Fintype.mem_piFinset.mp hyT (τ i)
          · exact (Equiv.sum_comp σ (fun i => v (z.1 i))).trans (hw.trans (Equiv.sum_comp τ (fun i => v (z.2 i))).symm)
          · simpa only [Function.comp_apply, hσ₀, hσ₁, hτ₀, hτ₁] using hmatch
        · apply Prod.ext <;> funext i <;> simp
      · have h := Finset.card_biUnion_le_card_mul perms blocks D.card (fun _ _ => Finset.card_image_le)
        have hcard : perms.card = 576 := by
          norm_num [perms, Fintype.card_prod, Fintype.card_perm, Nat.factorial]
        rw [hcard] at h
        exact h.trans (Nat.mul_le_mul_left _ (fixed_le A v))
    obtain ⟨D, hD, hpairs⟩ := Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b
      P hP (ε / 2) (by positivity)
    refine ⟨576 * (D * D), by positivity, ?_⟩
    intro M hM A hA v T w
    have hp : (energy A v : ℝ) ≤ D * (M : ℝ)^(ε/2) * (A.card : ℝ)^2 := hpairs M hM A hA
    have product := mul_le_mul hp hp (Nat.cast_nonneg _) (by positivity)
    have hrpow : (M : ℝ) ^ (ε / 2) * (M : ℝ) ^ (ε / 2) = (M : ℝ) ^ ε := by
      rw [← Real.rpow_add (by exact_mod_cast (show 0 < M by omega))]
      congr 1
      ring
    calc
      _ ≤ 576 * ((energy A v : ℝ) * (energy A v : ℝ)) := by exact_mod_cast any_le A v
      _ ≤ 576 * ((D * (M : ℝ)^(ε/2) * (A.card : ℝ)^2) *
          (D * (M : ℝ)^(ε/2) * (A.card : ℝ)^2)) :=
        mul_le_mul_of_nonneg_left product (by norm_num)
      _ = (576 * (D * D)) * ((M : ℝ)^(ε/2) * (M : ℝ)^(ε/2)) * (A.card : ℝ)^4 := by ring
      _ = _ := by rw [hrpow]
  let residualBound (P : Polynomial ℤ) (ε : ℝ) (k : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Finset.Icc 1 M,
      let v (a : ℕ) : ℤ := P.eval (a : ℤ)
      let T := Fintype.piFinset (fun _ : Fin 4 => A)
      let w (x : Fin 4 → ℕ) := ∑ i, v (x i)
      let S := (T.product T).filter (fun z => w z.1 = w z.2 ∧
        ∀ ij : Fin 4 × Fin 4, z.1 ij.1 ≠ z.2 ij.2)
      let R := S.filter (fun z => ∀ ij kl : Fin 4 × Fin 4, ij.1 ≠ ij.2 → kl.1 ≠ kl.2 →
        z.1 ij.1 + z.1 ij.2 ≠ z.2 kl.1 + z.2 kl.2 ∧
        z.1 ij.1 ^ 2 + z.1 ij.2 ^ 2 ≠ z.2 kl.1 ^ 2 + z.2 kl.2 ^ 2)
      let One (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) := ∃ ij : Fin 4 × Fin 4,
        v (z.1 ij.1) = v (z.2 ij.2)
      let Two (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) := ∃ ij kl : Fin 4 × Fin 4,
        ij.1 ≠ ij.2 ∧ kl.1 ≠ kl.2 ∧
        v (z.1 ij.1) + v (z.1 ij.2) = v (z.2 kl.1) + v (z.2 kl.2)
      ((R.filter (fun z => ¬ One z ∧ ¬ Two z)).card : ℝ) ≤
        C * (M : ℝ)^ε * (A.card : ℝ)^k
  intro P hP ε hε
  obtain ⟨K,hK⟩ := selfBound P hP
  obtain ⟨C₁,hC₁,hOne⟩ := singleBound P (by omega) ε hε K hK
  obtain ⟨C₂,hC₂,hTwo⟩ := pairBound P (by omega) ε hε
  have hrest : residualBound P ε (if P.natDegree = 3 then 5 else 4) := by
    by_cases h : P.natDegree = 3
    · rw [ite_eq_left h]
      exact h₁ P h ε hε
    · rw [ite_eq_right h]
      exact h₂ P (by omega) ε hε
  obtain ⟨C₃,hC₃,hThree⟩ := hrest
  refine ⟨C₁ + C₂ + C₃, by positivity, ?_⟩
  intro M hM A hA T w S
  let v (a : ℕ) : ℤ := P.eval (a : ℤ)
  let R := S.filter (fun z => ∀ ij kl : Fin 4 × Fin 4, ij.1 ≠ ij.2 → kl.1 ≠ kl.2 →
    z.1 ij.1 + z.1 ij.2 ≠ z.2 kl.1 + z.2 kl.2 ∧
    z.1 ij.1 ^ 2 + z.1 ij.2 ^ 2 ≠ z.2 kl.1 ^ 2 + z.2 kl.2 ^ 2)
  let One (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) := ∃ ij : Fin 4 × Fin 4,
    v (z.1 ij.1) = v (z.2 ij.2)
  let Two (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) := ∃ ij kl : Fin 4 × Fin 4,
    ij.1 ≠ ij.2 ∧ kl.1 ≠ kl.2 ∧
    v (z.1 ij.1) + v (z.1 ij.2) = v (z.2 kl.1) + v (z.2 kl.2)
  let U := (T.product T).filter (fun z => w z.1 = w z.2 ∧
    (∀ ij : Fin 4 × Fin 4, z.1 ij.1 ≠ z.2 ij.2) ∧ One z)
  let V := (T.product T).filter (fun z => w z.1 = w z.2 ∧ Two z)
  let H := R.filter (fun z => ¬ One z ∧ ¬ Two z)
  have hc : R.card ≤ U.card + V.card + H.card := by
    have hin : R ⊆ (U ∪ V) ∪ H := by
      intro z hz
      have hs := (Finset.mem_filter.mp hz).1
      obtain ⟨ht,hw,hdis⟩ := Finset.mem_filter.mp hs
      by_cases ho : One z
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht,hw,hdis,ho⟩))
      by_cases ht' : Two z
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht,hw,ht'⟩))
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,ho,ht'⟩)
    calc
      _ ≤ ((U ∪ V) ∪ H).card := Finset.card_le_card hin
      _ ≤ (U ∪ V).card + H.card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
  let k := if P.natDegree = 3 then 5 else 4
  have hk : (A.card : ℝ)^4 ≤ (A.card : ℝ)^k := by
    dsimp [k]
    split
    · by_cases h : A.card = 0
      · simp [h]
      · exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ A.card by omega)) (by decide)
    · rfl
  have hu : (U.card : ℝ) ≤ C₁ * (M : ℝ)^ε * (A.card : ℝ)^4 := hOne M hM A hA
  have hv : (V.card : ℝ) ≤ C₂ * (M : ℝ)^ε * (A.card : ℝ)^4 := hTwo M hM A hA
  have hh : (H.card : ℝ) ≤ C₃ * (M : ℝ)^ε * (A.card : ℝ)^k := hThree M hM A hA
  change (R.card : ℝ) ≤ (C₁ + C₂ + C₃) * (M : ℝ)^ε * (A.card : ℝ)^k
  calc
    _ ≤ (U.card : ℝ) + (V.card : ℝ) + (H.card : ℝ) := by exact_mod_cast hc
    _ ≤ (C₁ * (M : ℝ)^ε * (A.card : ℝ)^k + C₂ * (M : ℝ)^ε * (A.card : ℝ)^k) +
          C₃ * (M : ℝ)^ε * (A.card : ℝ)^k := by
      exact add_le_add (add_le_add
        (hu.trans (mul_le_mul_of_nonneg_left hk (by positivity)))
        (hv.trans (mul_le_mul_of_nonneg_left hk (by positivity)))) hh
    _ = _ := by ring
