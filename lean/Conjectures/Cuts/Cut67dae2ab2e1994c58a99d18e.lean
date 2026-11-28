import Mathlib

/-- Reduce uniform prescribed classes to a single aggregate estimate for every choice of reduced pairs. -/
-- child 1 zh: 由目标同余和已知素数类推出反射素数的剩余类，化双素数表示为一变量筛。
-- child 1 en: Recover the reflected prime's prescribed residue from the admissible target class.
-- child 2 zh: 对每个模数同时选出一对既约剩余类，使该模数的损失达到最大值。
-- child 2 en: Select worst reduced pairs simultaneously across all moduli.
-- child 3 zh: 从带对数权的一阶矩提取一个可同时控制所有剩余类的例外模数集。
-- child 3 en: Extract a single exceptional-modulus set from the weighted first moment.
-- child 4 zh: 在平方根尺度，对任意逐模指定的既约类对证明反射素数筛缺失数的对数节省矩估计。
-- child 4 en: Prove logarithmic first-moment savings for reflected prime misses uniformly over all residue selectors.

theorem Conjectures.Cuts.Cut67dae2ab2e1994c58a99d18e
    (h₁ : ∀ q a b n : ℕ, a < q → b < q → n % q = (a+b) % q →
    ((∃ p r : ℕ, Nat.Prime p ∧ Nat.Prime r ∧ p+r=n ∧ p % q=a ∧ r % q=b) ↔
     ∃ p ∈ Finset.Icc 2 n, Nat.Prime p ∧ p % q=a ∧ Nat.Prime (n-p)))
    (h₂ : ∀ (S : Finset ℕ) (F : ℕ → ℕ → ℕ → ℝ), (∀ q ∈ S, 2 ≤ q) →
    ∃ a b : ℕ → ℕ, ∀ q ∈ S,
      a q < q ∧ b q < q ∧ Nat.Coprime (a q) q ∧ Nat.Coprime (b q) q ∧
      ∀ u v : ℕ, u < q → v < q → Nat.Coprime u q → Nat.Coprime v q →
        F q u v ≤ F q (a q) (b q))
    (h₃ : ∀ (S : Finset ℕ) (f : ℕ → ℝ) (u L R : ℝ), 0 < u → 0 ≤ L →
    (∀ q ∈ S, 0 ≤ f q) → (∑ q ∈ S, f q)*L ≤ u*R →
    ∃ T : Finset ℕ, T ⊆ S ∧ (T.card : ℝ)*L ≤ R ∧ ∀ q ∈ S, q ∉ T → f q ≤ u)
    (h₄ : by
  classical
  exact let bad := fun q a b n : ℕ => Even n ∧ n % q = (a+b) % q ∧
      ¬ ∃ p ∈ Finset.Icc 2 n, Nat.Prime p ∧ p % q=a ∧ Nat.Prime (n-p)
    ∀ B : ℕ, ∃ A : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 2 ≤ N₀ ∧
    ∀ N R : ℕ, N₀ ≤ N → 3 ≤ R → (R : ℝ)*(Real.log (N : ℝ))^A ≤ Real.sqrt (N : ℝ) →
    ∀ a b : ℕ → ℕ, (∀ q ∈ Finset.Icc 3 R, a q < q ∧ b q < q ∧
        Nat.Coprime (a q) q ∧ Nat.Coprime (b q) q) →
    (∑ q ∈ Finset.Icc 3 R,
      (((Finset.Icc 2 N).filter (bad q (a q) (b q))).card : ℝ)*(q : ℝ))*
       (Real.log (N : ℝ))^B ≤ (ε*(N : ℝ))*(R : ℝ))
    : (let missed := fun q a b n : ℕ => Even n ∧ n % q = (a+b) % q ∧ ¬ ∃ p r : ℕ, Nat.Prime p ∧ Nat.Prime r ∧ p+r=n ∧ p % q=a ∧ r % q=b; ∀ B : ℕ, ∃ A : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N R : ℕ, N₀ ≤ N → 3 ≤ R → (R : ℝ)*(Real.log (N : ℝ))^A ≤ Real.sqrt (N : ℝ) → ∃ T : Finset ℕ, T ⊆ Finset.Icc 3 R ∧ (T.card : ℝ)*(Real.log (N : ℝ))^B ≤ (R : ℝ) ∧ ∀ q ∈ Finset.Icc 3 R, q ∉ T → ∀ a b : ℕ, a < q → b < q → Nat.Coprime a q → Nat.Coprime b q → (((@Finset.filter ℕ (missed q a b) (Classical.decPred (missed q a b)) (Finset.Icc 2 N)).card : ℝ)*(q : ℝ)) ≤ ε*(N : ℝ)) := by
  classical
  intro missed B
  obtain ⟨A,hA⟩ := h₄ B
  refine ⟨A,?_⟩
  intro ε hε
  obtain ⟨N₀,h₂N,H⟩ := hA ε hε
  refine ⟨N₀,?_⟩
  intro N R hN hR hscale
  let bad := fun q a b n : ℕ => Even n ∧ n % q = (a+b) % q ∧
    ¬ ∃ p ∈ Finset.Icc 2 n, Nat.Prime p ∧ p % q=a ∧ Nat.Prime (n-p)
  let S := Finset.Icc 3 R
  let F := fun q a b : ℕ =>
    (((Finset.Icc 2 N).filter (bad q a b)).card : ℝ)*(q:ℝ)
  have hS (q : ℕ) (hq : q ∈ S) : 2 ≤ q := by
    have := (Finset.mem_Icc.mp hq).1
    omega
  obtain ⟨a,b,hm⟩ := h₂ S F hS
  have total := H N R hN hR hscale a b (fun q hq =>
    ⟨(hm q hq).1,(hm q hq).2.1,(hm q hq).2.2.1,(hm q hq).2.2.2.1⟩)
  have hposN : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hpos (q : ℕ) (_hq : q ∈ S) : 0 ≤ F q (a q) (b q) := by dsimp [F]; positivity
  obtain ⟨T,hTS,hcard,hgood⟩ := h₃ S (fun q => F q (a q) (b q)) (ε*(N:ℝ))
      ((Real.log (N:ℝ))^B) R (mul_pos hε hposN) (pow_nonneg hlog B) hpos total
  refine ⟨T,hTS,hcard,?_⟩
  intro q hq hnot u v hu hv huc hvc
  have eqsets : (@Finset.filter ℕ (missed q u v) (Classical.decPred (missed q u v)) (Finset.Icc 2 N)) =
      (Finset.Icc 2 N).filter (bad q u v) := by
    ext n
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro _
    change (Even n ∧ n % q = (u+v) % q ∧ _) ↔ (Even n ∧ n % q = (u+v) % q ∧ _)
    constructor
    · rintro ⟨he,hs,hn⟩
      exact ⟨he,hs,fun h => hn ((h₁ q u v n hu hv hs).mpr h)⟩
    · rintro ⟨he,hs,hn⟩
      exact ⟨he,hs,fun h => hn ((h₁ q u v n hu hv hs).mp h)⟩
  rw [eqsets]
  exact ((hm q hq).2.2.2.2 u v hu hv huc hvc).trans (hgood q hq hnot)
