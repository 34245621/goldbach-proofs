import Mathlib
import Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b

namespace RepeatedTripleCollision
noncomputable section
open Finset

private def equalPairs {α : Type*} [Fintype α] (f g : α → ℤ) : Finset (α × α) :=
  univ.filter fun z => f z.1 = g z.2

private lemma count_equalPairs {α : Type*} [Fintype α] (f g : α → ℤ) (T : Finset ℤ)
    (hf : ∀ a, f a ∈ T) :
    (equalPairs f g).card = ∑ k ∈ T, (univ.filter fun a => f a = k).card *
      (univ.filter fun b => g b = k).card := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun z : α × α => f z.1)
    (t := T) (s := equalPairs f g) (fun a _ => hf a.1)]
  refine sum_congr rfl (fun k _ => ?_)
  rw [← card_product]
  congr 1
  ext z
  simp [equalPairs]
  omega

private lemma mixed_bound {α : Type*} [Fintype α] (f g : α → ℤ)
    (h : (equalPairs g g).card ≤ (equalPairs f f).card) :
    (equalPairs f g).card ≤ (equalPairs f f).card := by
  classical
  let T := univ.image f ∪ univ.image g
  have hf (a : α) : f a ∈ T := mem_union_left _ (mem_image_of_mem _ (mem_univ a))
  have hg (a : α) : g a ∈ T := mem_union_right _ (mem_image_of_mem _ (mem_univ a))
  have hsum : 2 * (equalPairs f g).card ≤ (equalPairs f f).card + (equalPairs g g).card := by
    rw [count_equalPairs f g T hf, count_equalPairs f f T hf, count_equalPairs g g T hg,
      mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro k _
    generalize (univ.filter fun a => f a = k).card = a
    generalize (univ.filter fun a => g a = k).card = b
    zify
    nlinarith [sq_nonneg ((a : ℤ) - (b : ℤ))]
  omega

/-- Uniformly count two pairs of polynomial values at an arbitrary displacement
determined by k other indices.  The displacement need not be injective. -/
theorem pair_sums_with_anchors (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Icc 1 M, ∀ k : ℕ,
    ∀ shift : (Fin k → ↥A) → ℤ,
      (∑ t : Fin k → ↥A, (((univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
        fun z => (∑ i, P.eval ((z.1 i : ℕ) : ℤ)) =
          (∑ i, P.eval ((z.2 i : ℕ) : ℤ)) + shift t).card : ℝ)) ≤
        C * (M : ℝ)^ε * (A.card : ℝ)^(k+2) := by
  classical
  obtain ⟨C,hC,h⟩ := Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b P hd ε hε
  refine ⟨C,hC,?_⟩
  intro M hM A hA k shift
  let f (a : Fin 2 → ↥A) := ∑ i, P.eval ((a i : ℕ) : ℤ)
  have hs (t : Fin k → ↥A) : (equalPairs f (fun a => f a + shift t)).card ≤
      (equalPairs f f).card := by
    apply mixed_bound
    have he : equalPairs (fun a => f a + shift t) (fun a => f a + shift t) = equalPairs f f := by
      ext z
      simp [equalPairs]
    rw [he]
  have he : ((equalPairs f f).card : ℝ) ≤ C * (M : ℝ)^ε * (A.card : ℝ)^2 := h M hM A hA
  calc
    _ ≤ ∑ _t : Fin k → ↥A, C * (M : ℝ)^ε * (A.card : ℝ)^2 :=
      sum_le_sum fun t _ => (Nat.cast_le.mpr (hs t)).trans he
    _ = _ := by simp [nsmul_eq_mul, pow_add]; ring

/-- Ordered four-term collisions with the repeated positions put first.
The first count represents (x,x,a,b) versus (y,y,c,d).
The second represents (x,x,a,b) versus (y,z,c,d). -/
theorem repeated_quartet_counts (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Icc 1 M,
      let w (a : ↥A) := P.eval ((a : ℕ) : ℤ)
      let g (a : Fin 2 → ↥A) := ∑ i, w (a i)
      (∑ t : Fin 2 → ↥A, (((univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
        fun p => 2*w (t 0) + g p.1 = 2*w (t 1) + g p.2).card : ℝ)) ≤
          C * (M : ℝ)^ε * (A.card : ℝ)^4 ∧
      (∑ t : Fin 3 → ↥A, (((univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
        fun p => 2*w (t 0) + g p.1 = w (t 1) + w (t 2) + g p.2).card : ℝ)) ≤
          C * (M : ℝ)^ε * (A.card : ℝ)^5 := by
  classical
  obtain ⟨C,hC,h⟩ := pair_sums_with_anchors P hd ε hε
  refine ⟨C,hC,?_⟩
  intro M hM A hA
  let w (a : ↥A) := P.eval ((a : ℕ) : ℤ)
  let g (a : Fin 2 → ↥A) := ∑ i, w (a i)
  constructor
  · apply le_trans _ (h M hM A hA 2 (fun t => 2*w (t 1) - 2*w (t 0)))
    refine sum_le_sum (fun t _ => Nat.cast_le.mpr (card_le_card (fun p hp => ?_)))
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    have he : 2*w (t 0) + g p.1 = 2*w (t 1) + g p.2 := (mem_filter.mp hp).2
    change g p.1 = g p.2 + (2*w (t 1) - 2*w (t 0))
    linarith
  · apply le_trans _ (h M hM A hA 3 (fun t => w (t 1) + w (t 2) - 2*w (t 0)))
    refine sum_le_sum (fun t _ => Nat.cast_le.mpr (card_le_card (fun p hp => ?_)))
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    have he : 2*w (t 0) + g p.1 = w (t 1) + w (t 2) + g p.2 := (mem_filter.mp hp).2
    change g p.1 = g p.2 + (w (t 1) + w (t 2) - 2*w (t 0))
    linarith

end
end RepeatedTripleCollision



namespace QuartetRepeats
open Finset
noncomputable section

private abbrev Perm := Equiv.Perm (Fin 4)
private abbrev Slots := Perm × Perm
private abbrev Four (α : Type) := (Fin 4 → α) × (Fin 4 → α)
private abbrev Two (α : Type) := (Fin 2 → α) × (Fin 2 → α)

private lemma place {α : Type} (u : Fin 4 → α) (h : ¬ Function.Injective u) :
    ∃ e : Perm, u (e 0) = u (e 1) := by
  classical
  simp only [Function.Injective, not_forall] at h
  obtain ⟨i,j,he, hn⟩ := h
  let t : Perm := Equiv.swap 0 i
  have ht : t 0 = i := Equiv.swap_apply_left _ _
  have hk : t.symm j ≠ 0 := by
    intro hk
    exact hn ((ht.symm.trans (congrArg t hk).symm).trans (t.apply_symm_apply j))
  let e := (Equiv.swap 1 (t.symm j)).trans t
  have he0 : e 0 = i := by
    change t (Equiv.swap 1 (t.symm j) 0) = i
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hk), ht]
  have he1 : e 1 = j := by simp [e]
  exact ⟨e, by rwa [he0, he1]⟩

private lemma encode_bound {α β : Type} [Fintype α] [Fintype β] (f : α → ℤ)
    (a b c : β → α) (G : Finset (Four α))
    (hs : ∀ z ∈ G, (∑ i, f (z.1 i)) = ∑ i, f (z.2 i))
    (hp : ∀ z ∈ G, ∃ s : Slots, ∃ t : β,
      z.1 (s.1 0) = a t ∧ z.1 (s.1 1) = a t ∧ z.2 (s.2 0) = b t ∧ z.2 (s.2 1) = c t) :
    (G.card : ℝ) ≤ (Fintype.card Slots : ℝ) * ∑ t : β,
      (((univ : Finset (Two α)).filter fun z =>
        2*f (a t) + (∑ i, f (z.1 i)) = f (b t) + f (c t) + ∑ i, f (z.2 i)).card : ℝ) := by
  classical
  let pair (t : β) := (univ : Finset (Two α)).filter fun z =>
    2*f (a t) + (∑ i, f (z.1 i)) = f (b t) + f (c t) + ∑ i, f (z.2 i)
  let s (z : ↥G) := (hp z.val z.property).choose
  let t (z : ↥G) := (hp z.val z.property).choose_spec.choose
  have hst (z : ↥G) := (hp z.val z.property).choose_spec.choose_spec
  let F (z : ↥G) : Slots × (Σ _ : β, Two α) :=
    (s z, ⟨t z, (![z.val.1 ((s z).1 2),z.val.1 ((s z).1 3)],
                  ![z.val.2 ((s z).2 2),z.val.2 ((s z).2 3)])⟩)
  have hm (z : ↥G) : F z ∈ (univ : Finset Slots) ×ˢ univ.sigma pair := by
    refine mem_product.mpr ⟨mem_univ _, mem_sigma.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_univ _,?_⟩⟩⟩
    have h₁ := Equiv.sum_comp (s z).1 (fun i => f (z.val.1 i))
    have h₂ := Equiv.sum_comp (s z).2 (fun i => f (z.val.2 i))
    have h := h₁.trans ((hs z.val z.property).trans h₂.symm)
    rcases hst z with ⟨ha,ha',hb,hc⟩
    change z.val.1 ((s z).1 0) = a (t z) at ha
    change z.val.1 ((s z).1 1) = a (t z) at ha'
    change z.val.2 ((s z).2 0) = b (t z) at hb
    change z.val.2 ((s z).2 1) = c (t z) at hc
    simp only [Fin.sum_univ_four,ha,ha',hb,hc] at h
    simp only [F,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
    linarith
  have hi : Function.Injective F := by
    intro x y he
    have hslot : s x = s y := congrArg Prod.fst he
    have hparam : t x = t y := congrArg (fun z => z.2.1) he
    obtain ⟨hx0,hx1,hx2,hx3⟩ := hst x
    obtain ⟨hy0,hy1,hy2,hy3⟩ := hst y
    apply Subtype.ext
    apply Prod.ext
    · funext i
      obtain ⟨k,rfl⟩ := (s x).1.surjective i
      have hk : x.val.1 ((s x).1 k) = y.val.1 ((s y).1 k) := by
        fin_cases k
        · exact hx0.trans ((congrArg a hparam).trans hy0.symm)
        · exact hx1.trans ((congrArg a hparam).trans hy1.symm)
        · exact congrArg (fun z => z.2.2.1 0) he
        · exact congrArg (fun z => z.2.2.1 1) he
      simpa only [hslot] using hk
    · funext i
      obtain ⟨k,rfl⟩ := (s x).2.surjective i
      have hk : x.val.2 ((s x).2 k) = y.val.2 ((s y).2 k) := by
        fin_cases k
        · exact hx2.trans ((congrArg b hparam).trans hy2.symm)
        · exact hx3.trans ((congrArg c hparam).trans hy3.symm)
        · exact congrArg (fun z => z.2.2.2 0) he
        · exact congrArg (fun z => z.2.2.2 1) he
      simpa only [hslot] using hk
  have hnat := card_le_card_of_injOn (s := (univ : Finset ↥G)) F (fun z _ => hm z) hi.injOn
  simp only [card_univ, Fintype.card_coe, card_product, card_sigma] at hnat
  exact_mod_cast hnat

/-- Both tuples have a repeated index: fourth power of the support size.
Either tuple has a repeated index: fifth power of the support size. -/
theorem quartet_bounds (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Icc 1 M,
      ∀ G : Finset ((Fin 4 → ↥A) × (Fin 4 → ↥A)),
      (∀ z ∈ G, (∑ i, P.eval ((z.1 i : ℕ) : ℤ)) = ∑ i, P.eval ((z.2 i : ℕ) : ℤ)) →
      ((∀ z ∈ G, ¬ Function.Injective z.1 ∧ ¬ Function.Injective z.2) →
        (G.card : ℝ) ≤ C * (M : ℝ)^ε * (A.card : ℝ)^4) ∧
      ((∀ z ∈ G, ¬ Function.Injective z.1 ∨ ¬ Function.Injective z.2) →
        (G.card : ℝ) ≤ C * (M : ℝ)^ε * (A.card : ℝ)^5) := by
  classical
  obtain ⟨C,hC,h⟩ := RepeatedTripleCollision.repeated_quartet_counts P hd ε hε
  let B : ℝ := Fintype.card Slots
  have hB : 0 < B := by dsimp [B]; exact_mod_cast Fintype.card_pos
  refine ⟨2*B*C,by positivity,?_⟩
  intro M hM A hA G hs
  let w (a : ↥A) := P.eval ((a : ℕ) : ℤ)
  obtain ⟨h4,h5⟩ := h M hM A hA
  constructor
  · intro hdbl
    have henc := encode_bound w (fun t : Fin 2 → ↥A => t 0) (fun t => t 1) (fun t => t 1) G hs (by
      intro z hz
      obtain ⟨e,he⟩ := place z.1 (hdbl z hz).1
      obtain ⟨v,hv⟩ := place z.2 (hdbl z hz).2
      exact ⟨(e,v),![z.1 (e 0),z.2 (v 0)],rfl,he.symm,rfl,hv.symm⟩)
    simp only [← two_mul] at henc
    have hh := henc.trans (mul_le_mul_of_nonneg_left h4 hB.le)
    calc
      _ ≤ B * (C * (M : ℝ)^ε * (A.card : ℝ)^4) := hh
      _ ≤ 2*(B * (C * (M : ℝ)^ε * (A.card : ℝ)^4)) := by linarith [show 0 ≤ B * (C * (M : ℝ)^ε * (A.card : ℝ)^4) by positivity]
      _ = _ := by ring
  · intro heither
    have leftBound (S : Finset (Four ↥A))
        (heq : ∀ z ∈ S, (∑ i, w (z.1 i)) = ∑ i, w (z.2 i))
        (hl : ∀ z ∈ S, ¬ Function.Injective z.1) :
        (S.card : ℝ) ≤ B * (C * (M : ℝ)^ε * (A.card : ℝ)^5) := by
      have henc := encode_bound w (fun t : Fin 3 → ↥A => t 0) (fun t => t 1) (fun t => t 2) S heq (by
        intro z hz
        obtain ⟨e,he⟩ := place z.1 (hl z hz)
        exact ⟨(e,Equiv.refl _),![z.1 (e 0),z.2 0,z.2 1],rfl,he.symm,rfl,rfl⟩)
      exact henc.trans (mul_le_mul_of_nonneg_left h5 hB.le)
    let L := G.filter (fun z => ¬ Function.Injective z.1)
    let R := G.filter (fun z => Function.Injective z.1)
    have hbL := leftBound L (fun z hz => hs z (mem_filter.mp hz).1)
      (fun _ hz => (mem_filter.mp hz).2)
    have hbR := leftBound (R.image Prod.swap) (by
      intro z hz
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
      exact (hs y (mem_filter.mp hy).1).symm) (by
      intro z hz
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
      obtain ⟨hyG,hinj⟩ := mem_filter.mp hy
      exact (heither y hyG).resolve_left (not_not.mpr hinj))
    rw [card_image_of_injective _ Prod.swap_injective] at hbR
    have hcard : R.card + L.card = G.card :=
      card_filter_add_card_filter_not (s := G) (fun z => Function.Injective z.1)
    rw [← hcard,Nat.cast_add]
    calc
      _ ≤ B*(C*(M:ℝ)^ε*(A.card:ℝ)^5) + B*(C*(M:ℝ)^ε*(A.card:ℝ)^5) := add_le_add hbR hbL
      _ = _ := by ring

/-- The support-restricted version takes the natural-valued tuples used by
L-goldbach-cut-1e05ee16f5cfdc2abf090622. Additional filters on G are allowed. -/
theorem repeat_branch (P : Polynomial ℤ) (hd : 3 ≤ P.natDegree) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Icc 1 M,
      ∀ G : Finset ((Fin 4 → ℕ) × (Fin 4 → ℕ)),
      (∀ z ∈ G, (∀ i, z.1 i ∈ A) ∧ (∀ i, z.2 i ∈ A) ∧
        (∑ i, P.eval (z.1 i : ℤ)) = (∑ i, P.eval (z.2 i : ℤ)) ∧
        (if P.natDegree = 3 then ¬ Function.Injective z.1 ∨ ¬ Function.Injective z.2
         else ¬ Function.Injective z.1 ∧ ¬ Function.Injective z.2)) →
      (G.card : ℝ) ≤ C * (M : ℝ)^ε * (A.card : ℝ)^(if P.natDegree = 3 then 5 else 4) := by
  classical
  obtain ⟨C,hC,h⟩ := quartet_bounds P (by omega) ε hε
  refine ⟨C,hC,?_⟩
  intro M hM A hA G hg
  let F (z : ↥G) : Four ↥A :=
    (fun i => ⟨z.val.1 i,(hg z.val z.property).1 i⟩,
     fun i => ⟨z.val.2 i,(hg z.val z.property).2.1 i⟩)
  have hi : Function.Injective F := by
    intro a b hab
    exact Subtype.ext (Prod.ext
      (funext fun i => congrArg (fun z : Four ↥A => (z.1 i : ℕ)) hab)
      (funext fun i => congrArg (fun z : Four ↥A => (z.2 i : ℕ)) hab))
  let S := (univ : Finset ↥G).image F
  have hcard : S.card = G.card := by simp [S,card_image_of_injective _ hi]
  have match_inj (z : ↥G) : (Function.Injective (F z).1 ↔ Function.Injective z.val.1) ∧
      (Function.Injective (F z).2 ↔ Function.Injective z.val.2) := by
    constructor <;> constructor
    · intro hz i j he
      exact hz (Subtype.ext he)
    · intro hz i j he
      exact hz (congrArg Subtype.val he)
    · intro hz i j he
      exact hz (Subtype.ext he)
    · intro hz i j he
      exact hz (congrArg Subtype.val he)
  have hb := h M hM A hA S (by
    intro z hz
    obtain ⟨y,_,rfl⟩ := mem_image.mp hz
    exact (hg y.val y.property).2.2.1)
  rw [← hcard]
  by_cases hdeg : P.natDegree = 3
  · rw [ite_eq_left hdeg]
    apply hb.2
    intro z hz
    obtain ⟨y,_,rfl⟩ := mem_image.mp hz
    rw [(match_inj y).1,(match_inj y).2]
    simpa only [ite_eq_left hdeg] using (hg y.val y.property).2.2.2
  · rw [ite_eq_right hdeg]
    apply hb.1
    intro z hz
    obtain ⟨y,_,rfl⟩ := mem_image.mp hz
    rw [(match_inj y).1,(match_inj y).2]
    simpa only [ite_eq_right hdeg] using (hg y.val y.property).2.2.2

end
end QuartetRepeats

open Finset in
theorem Conjectures.Cuts.Taskde749f1787d3544386eed2a9 : (∀ (P : Polynomial ℤ), 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Icc 1 M,
      let T := Fintype.piFinset fun _ : Fin 4 => A
      let weight (a : Fin 4 → ℕ) := ∑ i, P.eval (a i : ℤ)
      let D := (T.product T).filter fun z => weight z.1 = weight z.2 ∧
        ∀ i : Fin 4 × Fin 4, z.1 i.1 ≠ z.2 i.2
      let G := D.filter fun z => ∀ (i j : Fin 4 × Fin 4), i.1 ≠ i.2 → j.1 ≠ j.2 →
        z.1 i.1 + z.1 i.2 ≠ z.2 j.1 + z.2 j.2 ∧
        z.1 i.1 ^ 2 + z.1 i.2 ^ 2 ≠ z.2 j.1 ^ 2 + z.2 j.2 ^ 2
      let repeated (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) :=
        if P.natDegree = 3 then ¬ Function.Injective z.1 ∨ ¬ Function.Injective z.2
        else ¬ Function.Injective z.1 ∧ ¬ Function.Injective z.2
      ((G.filter repeated).card : ℝ) ≤ C * (M : ℝ)^ε * (A.card : ℝ)^(if P.natDegree = 3 then 5 else 4)) := by
  classical
  intro P hd ε hε
  obtain ⟨C,hC,h⟩ := QuartetRepeats.repeat_branch P hd ε hε
  refine ⟨C,hC,?_⟩
  intro M hM A hA
  apply h M hM A hA
  intro z hz
  obtain ⟨hg,hr⟩ := mem_filter.mp hz
  obtain ⟨hb,_⟩ := mem_filter.mp hg
  obtain ⟨hT,hw,_⟩ := mem_filter.mp hb
  obtain ⟨hl,hh⟩ := mem_product.mp hT
  exact ⟨Fintype.mem_piFinset.mp hl,Fintype.mem_piFinset.mp hh,hw,hr⟩
